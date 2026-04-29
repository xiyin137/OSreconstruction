/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalContinuousEOW
import OSReconstruction.SCV.DistributionalEOWSupport

/-!
# Linear Part of the Local EOW Chart

The local EOW chart is affine on the real edge:
`u ↦ x0 + ∑ j, u j • ys j`.  Product-kernel recovery is translation-covariant
in the real coordinate used by its smoothing kernels, so the linear part of
this affine chart must be kept explicit when moving between local chart
coordinates and the original real edge.
-/

noncomputable section

open Complex

namespace SCV

variable {m : ℕ}

/-- The real-linear part of the affine real chart
`localEOWRealChart x0 ys`. -/
def localEOWRealLinearPart
    (ys : Fin m → Fin m → ℝ) :
    (Fin m → ℝ) → Fin m → ℝ :=
  fun u a => ∑ j, u j * ys j a

@[simp]
theorem localEOWRealLinearPart_zero
    (ys : Fin m → Fin m → ℝ) :
    localEOWRealLinearPart ys 0 = 0 := by
  ext a
  simp [localEOWRealLinearPart]

theorem localEOWRealLinearPart_add
    (ys : Fin m → Fin m → ℝ) (u v : Fin m → ℝ) :
    localEOWRealLinearPart ys (u + v) =
      localEOWRealLinearPart ys u + localEOWRealLinearPart ys v := by
  ext a
  simp [localEOWRealLinearPart, add_mul, Finset.sum_add_distrib]

theorem localEOWRealLinearPart_neg
    (ys : Fin m → Fin m → ℝ) (u : Fin m → ℝ) :
    localEOWRealLinearPart ys (-u) =
      -localEOWRealLinearPart ys u := by
  ext a
  simp [localEOWRealLinearPart, Finset.sum_neg_distrib]

theorem localEOWRealLinearPart_sub
    (ys : Fin m → Fin m → ℝ) (u v : Fin m → ℝ) :
    localEOWRealLinearPart ys (u - v) =
      localEOWRealLinearPart ys u - localEOWRealLinearPart ys v := by
  ext a
  simp [sub_eq_add_neg, localEOWRealLinearPart_add,
    localEOWRealLinearPart_neg]

theorem localEOWRealLinearPart_smul
    (ys : Fin m → Fin m → ℝ) (c : ℝ) (u : Fin m → ℝ) :
    localEOWRealLinearPart ys (c • u) =
      c • localEOWRealLinearPart ys u := by
  ext a
  simp [localEOWRealLinearPart, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The real-linear chart displacement is the weighted sum of the chosen chart
basis vectors. -/
theorem localEOWRealLinearPart_eq_sum_smul
    (ys : Fin m → Fin m → ℝ) (v : Fin m → ℝ) :
    localEOWRealLinearPart ys v = ∑ j, v j • ys j := by
  ext a
  simp [localEOWRealLinearPart]

/-- Matrix of the real-linear part of the local EOW chart.  Its columns are
the chart basis vectors `ys j`. -/
def localEOWRealLinearMatrix
    (ys : Fin m → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (Matrix.of ys).transpose

theorem localEOWRealLinearMatrix_mulVec
    (ys : Fin m → Fin m → ℝ) (u : Fin m → ℝ) :
    (localEOWRealLinearMatrix ys).mulVec u =
      localEOWRealLinearPart ys u := by
  ext a
  simp [localEOWRealLinearMatrix, localEOWRealLinearPart, Matrix.mulVec,
    dotProduct, mul_comm]

/-- The real-linear chart part as a continuous linear equivalence, when the
chosen cone directions are a real basis. -/
noncomputable def localEOWRealLinearCLE
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys) :
    (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) := by
  let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of ys
  let M : Matrix (Fin m) (Fin m) ℝ := A.transpose
  have hA_unit : IsUnit A := by
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    show LinearIndependent ℝ A.row
    simpa [A] using hli
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA_unit
  have hdetM : IsUnit M.det := by
    simpa [M, Matrix.det_transpose] using hdetA
  exact
    { toLinearEquiv :=
        { toLinearMap := Matrix.toLin' M
          invFun := Matrix.toLin' M⁻¹
          left_inv := fun v => by
            show (Matrix.toLin' M⁻¹) ((Matrix.toLin' M) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul,
              Matrix.nonsing_inv_mul _ hdetM, Matrix.toLin'_one]
            simp
          right_inv := fun v => by
            show (Matrix.toLin' M) ((Matrix.toLin' M⁻¹) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul,
              Matrix.mul_nonsing_inv _ hdetM, Matrix.toLin'_one]
            simp }
      continuous_toFun := LinearMap.continuous_of_finiteDimensional _
      continuous_invFun := LinearMap.continuous_of_finiteDimensional _ }

@[simp]
theorem localEOWRealLinearCLE_apply
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (u : Fin m → ℝ) :
    localEOWRealLinearCLE ys hli u =
      localEOWRealLinearPart ys u := by
  change (Matrix.toLin' (localEOWRealLinearMatrix ys)) u =
    localEOWRealLinearPart ys u
  ext a
  simpa [Matrix.toLin'_apply] using
    congrFun (localEOWRealLinearMatrix_mulVec ys u) a

/-- Pull original real-edge Schwartz tests back to the local chart coordinates
through the real-linear part of the EOW chart.  The distributional pullback
will also need the corresponding Jacobian factor; this map is the test-function
composition part. -/
noncomputable def localEOWRealLinearPullbackCLM
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (localEOWRealLinearCLE ys hli)

@[simp]
theorem localEOWRealLinearPullbackCLM_apply
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) (u : Fin m → ℝ) :
    localEOWRealLinearPullbackCLM ys hli ψ u =
      ψ (localEOWRealLinearPart ys u) := by
  simp [localEOWRealLinearPullbackCLM,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Support transport for the chart pullback.  Pulling a kernel back by the
local real chart's linear part changes the support radius by at most the
operator norm of the inverse chart. -/
theorem KernelSupportWithin.localEOWRealLinearPullbackCLM
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    KernelSupportWithin (localEOWRealLinearPullbackCLM ys hli ψ)
      (‖(localEOWRealLinearCLE ys hli).symm.toContinuousLinearMap‖ * r) := by
  intro u hu
  let e := localEOWRealLinearCLE ys hli
  have hsub :
      tsupport ((ψ : (Fin m → ℝ) → ℂ) ∘ (e : (Fin m → ℝ) → Fin m → ℝ)) ⊆
        e ⁻¹' tsupport (ψ : (Fin m → ℝ) → ℂ) := by
    exact tsupport_comp_subset_preimage (ψ : (Fin m → ℝ) → ℂ) e.continuous
  have hu' : u ∈
      tsupport ((ψ : (Fin m → ℝ) → ℂ) ∘
        (e : (Fin m → ℝ) → Fin m → ℝ)) := by
    simpa [e, localEOWRealLinearPullbackCLM,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hu
  have he_supp : e u ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) := hsub hu'
  have he_ball := hψ he_supp
  rw [Metric.mem_closedBall, dist_zero_right] at he_ball ⊢
  have hinv_bound : ‖u‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e u‖ := by
    calc
      ‖u‖ = ‖e.symm (e u)‖ := by
        rw [ContinuousLinearEquiv.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e u‖ := by
        exact ContinuousLinearMap.le_opNorm e.symm.toContinuousLinearMap (e u)
  exact le_trans hinv_bound
    (mul_le_mul_of_nonneg_left he_ball (norm_nonneg _))

/-- Push a chart-coordinate Schwartz kernel forward to original real-edge
linear coordinates, without the Jacobian normalization. -/
noncomputable def localEOWRealLinearPushforwardCLM
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (localEOWRealLinearCLE ys hli).symm

@[simp]
theorem localEOWRealLinearPushforwardCLM_apply
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) (y : Fin m → ℝ) :
    localEOWRealLinearPushforwardCLM ys hli φ y =
      φ ((localEOWRealLinearCLE ys hli).symm y) := by
  simp [localEOWRealLinearPushforwardCLM,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Support transport for the chart-to-original linear pushforward. -/
theorem KernelSupportWithin.localEOWRealLinearPushforwardCLM
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    {φ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hφ : KernelSupportWithin φ r) :
    KernelSupportWithin (localEOWRealLinearPushforwardCLM ys hli φ)
      (‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * r) := by
  intro y hy
  let e := localEOWRealLinearCLE ys hli
  have hsub :
      tsupport ((φ : (Fin m → ℝ) → ℂ) ∘
          (e.symm : (Fin m → ℝ) → Fin m → ℝ)) ⊆
        e.symm ⁻¹' tsupport (φ : (Fin m → ℝ) → ℂ) := by
    exact tsupport_comp_subset_preimage (φ : (Fin m → ℝ) → ℂ) e.symm.continuous
  have hy' : y ∈
      tsupport ((φ : (Fin m → ℝ) → ℂ) ∘
        (e.symm : (Fin m → ℝ) → Fin m → ℝ)) := by
    simpa [e, localEOWRealLinearPushforwardCLM,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hy
  have hpre_supp : e.symm y ∈ tsupport (φ : (Fin m → ℝ) → ℂ) := hsub hy'
  have hpre_ball := hφ hpre_supp
  rw [Metric.mem_closedBall, dist_zero_right] at hpre_ball ⊢
  have hbound : ‖y‖ ≤ ‖e.toContinuousLinearMap‖ * ‖e.symm y‖ := by
    calc
      ‖y‖ = ‖e (e.symm y)‖ := by
        rw [ContinuousLinearEquiv.apply_symm_apply]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖e.symm y‖ := by
        exact ContinuousLinearMap.le_opNorm e.toContinuousLinearMap (e.symm y)
  exact le_trans hbound
    (mul_le_mul_of_nonneg_left hpre_ball (norm_nonneg _))

/-- Push a chart-coordinate Schwartz test to the original real-edge
coordinates by the affine chart `u ↦ x0 + localEOWRealLinearPart ys u`.

The value at the original real-edge point `y` is
`φ ((localEOWRealLinearCLE ys hli).symm (y - x0))`. -/
noncomputable def localEOWAffineTestPushforwardCLM
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
  (translateSchwartzCLM (-x0)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (localEOWRealLinearCLE ys hli).symm)

@[simp]
theorem localEOWAffineTestPushforwardCLM_apply
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) (y : Fin m → ℝ) :
    localEOWAffineTestPushforwardCLM x0 ys hli φ y =
      φ ((localEOWRealLinearCLE ys hli).symm (y - x0)) := by
  simp [localEOWAffineTestPushforwardCLM,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, sub_eq_add_neg]

/-- The affine test pushforward has support contained in the affine image of the
original chart-coordinate support. -/
theorem tsupport_localEOWAffineTestPushforwardCLM_subset
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    tsupport
        (localEOWAffineTestPushforwardCLM x0 ys hli φ :
          (Fin m → ℝ) → ℂ) ⊆
      (localEOWRealChart x0 ys) ''
        tsupport (φ : (Fin m → ℝ) → ℂ) := by
  let e := localEOWRealLinearCLE ys hli
  have hsub :
      tsupport ((φ : (Fin m → ℝ) → ℂ) ∘
          fun y : Fin m → ℝ => e.symm y - e.symm x0) ⊆
        (fun y : Fin m → ℝ => e.symm y - e.symm x0) ⁻¹'
          tsupport (φ : (Fin m → ℝ) → ℂ) := by
    exact tsupport_comp_subset_preimage (φ : (Fin m → ℝ) → ℂ)
      ((e.symm.continuous.comp continuous_id).sub continuous_const)
  intro y hy
  have hfun :
      (localEOWAffineTestPushforwardCLM x0 ys hli φ : (Fin m → ℝ) → ℂ) =
        (φ : (Fin m → ℝ) → ℂ) ∘
          fun y : Fin m → ℝ => e.symm y - e.symm x0 := by
    funext y
    simp [e, localEOWAffineTestPushforwardCLM_apply]
  have hy' :
      y ∈ tsupport ((φ : (Fin m → ℝ) → ℂ) ∘
          fun y : Fin m → ℝ => e.symm y - e.symm x0) := by
    simpa [hfun] using hy
  refine ⟨e.symm y - e.symm x0, hsub hy', ?_⟩
  have hlin :
      localEOWRealLinearPart ys (e.symm y - e.symm x0) = y - x0 := by
    calc
      localEOWRealLinearPart ys (e.symm y - e.symm x0) =
          e (e.symm y - e.symm x0) := by
        simp [e]
      _ = e (e.symm y) - e (e.symm x0) := by
        simp
      _ = y - x0 := by
        simp
  calc
    localEOWRealChart x0 ys (e.symm y - e.symm x0) =
        x0 + localEOWRealLinearPart ys (e.symm y - e.symm x0) := by
      ext a
      simp [localEOWRealChart, localEOWRealLinearPart]
    _ = x0 + (y - x0) := by
      rw [hlin]
    _ = y := by
      ext a
      simp

/-- Compact support is preserved by affine test pushforward. -/
theorem HasCompactSupport.localEOWAffineTestPushforwardCLM
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    {φ : SchwartzMap (Fin m → ℝ) ℂ}
    (hφ : HasCompactSupport (φ : (Fin m → ℝ) → ℂ)) :
    HasCompactSupport
      (localEOWAffineTestPushforwardCLM x0 ys hli φ :
        (Fin m → ℝ) → ℂ) := by
  exact IsCompact.of_isClosed_subset
    (hφ.image (continuous_localEOWRealChart x0 ys))
    (isClosed_tsupport _)
    (tsupport_localEOWAffineTestPushforwardCLM_subset x0 ys hli φ)

/-- Absolute Jacobian of the local EOW real-linear chart. -/
noncomputable def localEOWRealJacobianAbs
    (ys : Fin m → Fin m → ℝ) : ℝ :=
  |(localEOWRealLinearMatrix ys).det|

/-- Push a chart-coordinate smoothing kernel forward to the original real edge
with the inverse absolute determinant factor required by the change of
variables `y = A u`. -/
noncomputable def localEOWRealLinearKernelPushforwardCLM
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
  ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) •
    localEOWRealLinearPushforwardCLM ys hli

@[simp]
theorem localEOWRealLinearKernelPushforwardCLM_apply
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) (y : Fin m → ℝ) :
    localEOWRealLinearKernelPushforwardCLM ys hli φ y =
      ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
        φ ((localEOWRealLinearCLE ys hli).symm y) := by
  rfl

/-- Support transport for the Jacobian-normalized chart-to-original kernel
pushforward.  The scalar Jacobian factor does not enlarge support. -/
theorem KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    {φ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hφ : KernelSupportWithin φ r) :
    KernelSupportWithin (localEOWRealLinearKernelPushforwardCLM ys hli φ)
      (‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * r) := by
  simpa [localEOWRealLinearKernelPushforwardCLM] using
    KernelSupportWithin.smul ((localEOWRealJacobianAbs ys)⁻¹ : ℂ)
      (KernelSupportWithin.localEOWRealLinearPushforwardCLM ys hli hφ)

/-- Support transport for a translated chart-coordinate kernel after
Jacobian-normalized pushforward.  The translation first enlarges the chart
support radius by `‖a‖`, then the linear pushforward enlarges by the chart
operator norm. -/
theorem KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_translateSchwartz
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (a : Fin m → ℝ) {φ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hφ : KernelSupportWithin φ r) :
    KernelSupportWithin
      (SCV.localEOWRealLinearKernelPushforwardCLM ys hli (SCV.translateSchwartz a φ))
      (‖(SCV.localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * (r + ‖a‖)) := by
  exact KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM ys hli
    (KernelSupportWithin.translateSchwartz a hφ)

/-- Transport a compact-window value-CLM package from original real-edge
kernels to local chart-coordinate kernels.  The proof performs both cutoff
removals and transports the finite Schwartz-seminorm bound through the
chart-kernel pushforward. -/
theorem regularizedLocalEOW_chartKernelFamily_valueCLM
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    {Rcut r rcut rψ : ℝ}
    (χr χψ : SchwartzMap (Fin m → ℝ) ℂ)
    (Gorig : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (Lorig : ComplexChartSpace m →
      SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hχr_one :
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) r, χr t = 1)
    (hχr_support :
      tsupport (χr : (Fin m → ℝ) → ℂ) ⊆
        Metric.closedBall 0 rcut)
    (hAcut_le :
      ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          rcut ≤ rψ)
    (hχψ_one :
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rψ, χψ t = 1)
    (hLorig_value :
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
      ∀ η : SchwartzMap (Fin m → ℝ) ℂ,
        Lorig z η =
          Gorig
            (SchwartzMap.smulLeftCLM ℂ
              (χψ : (Fin m → ℝ) → ℂ) η) z)
    (hLorig_bound :
      ∃ s0 : Finset (ℕ × ℕ), ∃ C0 : ℝ, 0 ≤ C0 ∧
        ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
        ∀ η : SchwartzMap (Fin m → ℝ) ℂ,
          ‖Lorig z η‖ ≤
            C0 * s0.sup
              (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) η) :
    let P := localEOWRealLinearKernelPushforwardCLM ys hli
    let Gchart : SchwartzMap (Fin m → ℝ) ℂ →
        ComplexChartSpace m → ℂ :=
      fun ψ z => Gorig (P ψ) z
    ∃ Lchart : ComplexChartSpace m →
        SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ,
      (∀ z ψ,
        Lchart z ψ =
          Lorig z
            (P (SchwartzMap.smulLeftCLM ℂ
              (χr : (Fin m → ℝ) → ℂ) ψ))) ∧
      (∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          KernelSupportWithin ψ r →
            Lchart z ψ = Gchart ψ z) ∧
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          ‖Lchart z ψ‖ ≤
            C * s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ := by
  let P := localEOWRealLinearKernelPushforwardCLM ys hli
  let B : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
    P.comp (SchwartzMap.smulLeftCLM ℂ (χr : (Fin m → ℝ) → ℂ))
  let Lchart : ComplexChartSpace m →
      SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    fun z => (Lorig z).comp B
  refine ⟨Lchart, ?_, ?_, ?_⟩
  · intro z ψ
    simp [Lchart, B, P]
  · intro z hz ψ hψ
    have hχr_id :
        SchwartzMap.smulLeftCLM ℂ (χr : (Fin m → ℝ) → ℂ) ψ = ψ :=
      KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall
        χr hχr_one hψ
    have hcut_support :
        KernelSupportWithin
          (SchwartzMap.smulLeftCLM ℂ (χr : (Fin m → ℝ) → ℂ) ψ) rcut :=
      KernelSupportWithin.smulLeftCLM_of_leftSupport hχr_support ψ
    have hpush0 :
        KernelSupportWithin
          (P (SchwartzMap.smulLeftCLM ℂ (χr : (Fin m → ℝ) → ℂ) ψ))
          (‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * rcut) := by
      simpa [P] using
        KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM
          ys hli hcut_support
    have hpush :
        KernelSupportWithin
          (P (SchwartzMap.smulLeftCLM ℂ (χr : (Fin m → ℝ) → ℂ) ψ))
          rψ :=
      hpush0.mono hAcut_le
    have hχψ_id :
        SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m → ℝ) → ℂ)
            (P (SchwartzMap.smulLeftCLM ℂ (χr : (Fin m → ℝ) → ℂ) ψ)) =
          P (SchwartzMap.smulLeftCLM ℂ (χr : (Fin m → ℝ) → ℂ) ψ) :=
      KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall
        χψ hχψ_one hpush
    calc
      Lchart z ψ =
          Lorig z (P (SchwartzMap.smulLeftCLM ℂ
            (χr : (Fin m → ℝ) → ℂ) ψ)) := by
          simp [Lchart, B, P]
      _ = Gorig
            (SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m → ℝ) → ℂ)
              (P (SchwartzMap.smulLeftCLM ℂ
                (χr : (Fin m → ℝ) → ℂ) ψ))) z := by
          exact hLorig_value z hz _
      _ = Gorig
            (P (SchwartzMap.smulLeftCLM ℂ
              (χr : (Fin m → ℝ) → ℂ) ψ)) z := by
          rw [hχψ_id]
      _ = Gorig (P ψ) z := by
          rw [hχr_id]
  · rcases hLorig_bound with ⟨s0, C0, hC0, hbound0⟩
    obtain ⟨s1, C1, hC1, hbound1⟩ :=
      SchwartzMap.exists_schwartzCLM_finsetSeminormBound B s0
    refine ⟨s1, C0 * C1, mul_nonneg hC0 hC1, ?_⟩
    intro z hz ψ
    calc
      ‖Lchart z ψ‖ = ‖Lorig z (B ψ)‖ := by
          simp [Lchart]
      _ ≤ C0 * s0.sup
            (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) (B ψ) :=
          hbound0 z hz (B ψ)
      _ ≤ C0 * (C1 * s1.sup
            (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ) := by
          exact mul_le_mul_of_nonneg_left (hbound1 ψ) hC0
      _ = (C0 * C1) *
            s1.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ := by
          ring

/-- Pull a distribution on the original real edge back to local chart
coordinates.  The inverse absolute determinant is the usual Jacobian factor for
the affine change of variables `y = x0 + A u`. -/
noncomputable def localEOWAffineDistributionPullbackCLM
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
  ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) •
    T.comp (localEOWAffineTestPushforwardCLM x0 ys hli)

@[simp]
theorem localEOWAffineDistributionPullbackCLM_apply
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    localEOWAffineDistributionPullbackCLM x0 ys hli T φ =
      ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
        T (localEOWAffineTestPushforwardCLM x0 ys hli φ) := by
  rfl

/-- The affine real chart is the base point plus its real-linear part. -/
theorem localEOWRealChart_eq_x0_add_linearPart
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) (u : Fin m → ℝ) :
    localEOWRealChart x0 ys u =
      x0 + localEOWRealLinearPart ys u := by
  ext a
  simp [localEOWRealChart, localEOWRealLinearPart]

/-- Evaluating the affine pushed test on the real chart recovers the original
chart-coordinate test. -/
@[simp]
theorem localEOWAffineTestPushforwardCLM_apply_realChart
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) (u : Fin m → ℝ) :
    localEOWAffineTestPushforwardCLM x0 ys hli φ
        (localEOWRealChart x0 ys u) =
      φ u := by
  let e := localEOWRealLinearCLE ys hli
  have he_symm : e.symm (localEOWRealLinearPart ys u) = u := by
    rw [← localEOWRealLinearCLE_apply ys hli u]
    exact e.symm_apply_apply u
  simp [e, localEOWRealChart_eq_x0_add_linearPart, he_symm]

/-- Affine real-chart change of variables for a pushed chart test.  The
Jacobian factor is the inverse absolute determinant in
`localEOWAffineDistributionPullbackCLM`. -/
theorem integral_localEOWAffineTestPushforwardCLM_changeOfVariables
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (g : (Fin m → ℝ) → ℂ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
      ∫ x : Fin m → ℝ,
        g x * localEOWAffineTestPushforwardCLM x0 ys hli φ x =
    ∫ u : Fin m → ℝ, g (localEOWRealChart x0 ys u) * φ u := by
  let e := localEOWRealLinearCLE ys hli
  let A : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := e.toContinuousLinearMap
  have hlin :
      (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) =
        Matrix.toLin' (localEOWRealLinearMatrix ys) := by
    apply LinearMap.ext
    intro u
    ext a
    change (localEOWRealLinearCLE ys hli u) a =
      (Matrix.toLin' (localEOWRealLinearMatrix ys) u) a
    rw [localEOWRealLinearCLE_apply]
    simpa [Matrix.toLin'_apply] using
      (congrFun (localEOWRealLinearMatrix_mulVec ys u).symm a)
  have hjac : localEOWRealJacobianAbs ys = |A.det| := by
    rw [localEOWRealJacobianAbs]
    change |(localEOWRealLinearMatrix ys).det| =
      |LinearMap.det (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))|
    rw [hlin, LinearMap.det_toLin']
  have hdet_ne : A.det ≠ 0 := by
    exact (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hdet_abs_ne : |A.det| ≠ 0 := abs_ne_zero.mpr hdet_ne
  let f : (Fin m → ℝ) → Fin m → ℝ := fun u => x0 + e u
  let G : (Fin m → ℝ) → ℂ := fun x =>
    ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
      (g x * localEOWAffineTestPushforwardCLM x0 ys hli φ x)
  have hfderiv :
      ∀ x ∈ (Set.univ : Set (Fin m → ℝ)),
        HasFDerivWithinAt f A Set.univ x := by
    intro x _hx
    change HasFDerivWithinAt (fun u : Fin m → ℝ => x0 + e u) A Set.univ x
    exact (e.hasFDerivAt.const_add x0).hasFDerivWithinAt
  have hinj : Set.InjOn f Set.univ := by
    intro x _hx y _hy hxy
    have hxy' : x0 + e x = x0 + e y := by
      simpa [f] using hxy
    apply e.injective
    calc
      e x = -x0 + (x0 + e x) := by simp
      _ = -x0 + (x0 + e y) := by rw [hxy']
      _ = e y := by simp
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.MeasureSpace.volume)
      (s := (Set.univ : Set (Fin m → ℝ)))
      (f := f) (f' := fun _ => A)
      MeasurableSet.univ hfderiv hinj G
  have himage : f '' Set.univ = Set.univ := by
    ext y
    constructor
    · intro _hy
      trivial
    · intro _hy
      refine ⟨e.symm (y - x0), trivial, ?_⟩
      dsimp [f]
      rw [ContinuousLinearEquiv.apply_symm_apply]
      ext a
      simp
  rw [himage] at hchange
  have hchart (u : Fin m → ℝ) :
      x0 + e u = localEOWRealChart x0 ys u := by
    rw [localEOWRealChart_eq_x0_add_linearPart]
    ext a
    simp [e, localEOWRealLinearCLE_apply]
  have hrhs :
      ∀ u : Fin m → ℝ,
        |A.det| • G (f u) =
          g (localEOWRealChart x0 ys u) * φ u := by
    intro u
    dsimp [G, f]
    rw [hchart u, localEOWAffineTestPushforwardCLM_apply_realChart, hjac]
    field_simp [hdet_abs_ne]
  calc
    ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
        ∫ x : Fin m → ℝ,
          g x * localEOWAffineTestPushforwardCLM x0 ys hli φ x =
        ∫ x : Fin m → ℝ, G x := by
          simpa [G] using
            (MeasureTheory.integral_const_mul
              ((localEOWRealJacobianAbs ys)⁻¹ : ℂ)
              (fun x : Fin m → ℝ =>
                g x * localEOWAffineTestPushforwardCLM x0 ys hli φ x)).symm
    _ = ∫ u : Fin m → ℝ, |A.det| • G (f u) := by
          simpa using hchange
    _ = ∫ u : Fin m → ℝ,
        g (localEOWRealChart x0 ys u) * φ u := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          exact hrhs u

/-- Compose a uniform-on-set limit to a constant with a parameter tending in
the index filter and a point that remains in the uniformity set. -/
theorem tendstoUniformlyOn_const_comp_of_tendsto_of_eventually_mem
    {ι α β γ : Type*} [PseudoMetricSpace β]
    {F : ι → α → β} {c : β}
    {l : Filter ι} {q : Filter γ} {s : Set α}
    {a : γ → ι} {b : γ → α}
    (hF : TendstoUniformlyOn F (fun _ : α => c) l s)
    (ha : Filter.Tendsto a q l)
    (hb : ∀ᶠ x in q, b x ∈ s) :
    Filter.Tendsto (fun x => F (a x) (b x)) q (nhds c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε_event :
      ∀ᶠ i in l, ∀ z ∈ s, dist ((fun _ : α => c) z) (F i z) < ε :=
    (Metric.tendstoUniformlyOn_iff.mp hF) ε hε
  have hε_event' :
      ∀ᶠ x in q, ∀ z ∈ s, dist c (F (a x) z) < ε :=
    ha.eventually hε_event
  filter_upwards [hε_event', hb] with x hx hbx
  simpa [dist_comm] using hx (b x) hbx

/-- The coordinate sum tends to zero through positive reals on the strict
positive orthant. -/
theorem coordSum_tendsto_positiveOrthant_nhdsWithin_Ioi
    {m : ℕ} (hm : 0 < m) :
    Filter.Tendsto
      (fun y : Fin m → ℝ => ∑ j, y j)
      (nhdsWithin 0 {y : Fin m → ℝ | ∀ j, 0 < y j})
      (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : Continuous (fun y : Fin m → ℝ => ∑ j, y j) := by
      fun_prop
    have h0 : (∑ j, (0 : Fin m → ℝ) j) = 0 := by simp
    simpa [h0] using
      (hcont.tendsto (0 : Fin m → ℝ)).mono_left inf_le_left
  · haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact Finset.sum_pos (fun j _hj => hy j) Finset.univ_nonempty

/-- The negated coordinate sum tends to zero through positive reals on the
strict negative orthant. -/
theorem coordNegSum_tendsto_negativeOrthant_nhdsWithin_Ioi
    {m : ℕ} (hm : 0 < m) :
    Filter.Tendsto
      (fun y : Fin m → ℝ => ∑ j, -y j)
      (nhdsWithin 0 {y : Fin m → ℝ | ∀ j, y j < 0})
      (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : Continuous (fun y : Fin m → ℝ => ∑ j, -y j) := by
      fun_prop
    have h0 : (∑ j, -(0 : Fin m → ℝ) j) = 0 := by simp
    simpa [h0] using
      (hcont.tendsto (0 : Fin m → ℝ)).mono_left inf_le_left
  · haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact Finset.sum_pos (fun j _hj => neg_pos.mpr (hy j))
      Finset.univ_nonempty

/-- Decompose a complex chart point with real part `u` and imaginary chart
coordinate `y` into the real chart plus the chart-linear imaginary part. -/
theorem localEOWChart_real_add_imag
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (u y : Fin m → ℝ) :
    localEOWChart x0 ys
        (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I) =
      fun a =>
        (localEOWRealChart x0 ys u a : ℂ) +
          (localEOWRealLinearPart ys y a : ℂ) * Complex.I := by
  ext a
  simp [localEOWChart, localEOWRealChart, localEOWRealLinearPart,
    add_mul, Finset.sum_add_distrib]
  have hI :
      (∑ x, (y x : ℂ) * I * (ys x a : ℂ)) =
        (∑ x, (y x : ℂ) * (ys x a : ℂ)) * I := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hI]
  ring

/-- Transport uniform cone slow-growth estimates to strict coordinate orthants
of a local EOW chart. -/
theorem chartSlowGrowth_from_uniformConeSlowGrowth
    (E C : Set (Fin m → ℝ))
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys_mem : ∀ j, ys j ∈ C)
    (x0 : Fin m → ℝ)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_Echart : ∀ u ∈ B, localEOWRealChart x0 ys u ∈ E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hslow_plus :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ (A : ℝ) (N : ℕ) (r : ℝ), 0 < A ∧ 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              ‖Fplus (fun a => (x a : ℂ) +
                (ε : ℂ) * (η a : ℂ) * Complex.I)‖ ≤
                A * (ε⁻¹) ^ N)
    (hslow_minus :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ (A : ℝ) (N : ℕ) (r : ℝ), 0 < A ∧ 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              ‖Fminus (fun a => (x a : ℂ) -
                (ε : ℂ) * (η a : ℂ) * Complex.I)‖ ≤
                A * (ε⁻¹) ^ N) :
    ∃ (Aplus Aminus : ℝ) (Nplus Nminus : ℕ) (rplus rminus : ℝ),
      0 < Aplus ∧ 0 < Aminus ∧ 0 < rplus ∧ 0 < rminus ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < rplus →
          ‖Fplus (localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I))‖ ≤
            Aplus * ((∑ j, v j)⁻¹) ^ Nplus) ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < rminus →
          ‖Fminus (localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I))‖ ≤
            Aminus * ((∑ j, -v j)⁻¹) ^ Nminus) := by
  let K : Set (Fin m → ℝ) := localEOWRealChart x0 ys '' B
  let Kη : Set (Fin m → ℝ) := localEOWSimplexDirections ys
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact hB_compact.image (continuous_localEOWRealChart x0 ys)
  have hK_E : K ⊆ E := by
    rintro x ⟨u, hu, rfl⟩
    exact hB_Echart u hu
  have hKη_compact : IsCompact Kη := by
    dsimp [Kη]
    exact isCompact_localEOWSimplexDirections ys
  have hKη_C : Kη ⊆ C := by
    dsimp [Kη]
    exact localEOWSimplexDirections_subset_cone C hC_conv ys hys_mem
  obtain ⟨Aplus, Nplus, rplus, hAplus, hrplus, hplus_bound⟩ :=
    hslow_plus K hK_compact hK_E Kη hKη_compact hKη_C
  obtain ⟨Aminus, Nminus, rminus, hAminus, hrminus, hminus_bound⟩ :=
    hslow_minus K hK_compact hK_E Kη hKη_compact hKη_C
  refine ⟨Aplus, Aminus, Nplus, Nminus, rplus, rminus,
    hAplus, hAminus, hrplus, hrminus, ?_, ?_⟩
  · intro u hu v hv_nonneg hs_pos hs_lt
    let s : ℝ := ∑ j, v j
    let η : Fin m → ℝ := s⁻¹ • localEOWRealLinearPart ys v
    have hη : η ∈ Kη := by
      dsimp [η, s, Kη]
      rw [localEOWRealLinearPart_eq_sum_smul]
      exact localEOW_positive_imag_normalized_mem_simplex
        (ys := ys) hv_nonneg hs_pos
    have hs_ne : s ≠ 0 := ne_of_gt (by simpa [s] using hs_pos)
    have hscale : ∀ a,
        (s : ℂ) * (η a : ℂ) =
          (localEOWRealLinearPart ys v a : ℂ) := by
      intro a
      have hreal : s * η a = localEOWRealLinearPart ys v a := by
        dsimp [η]
        change s * (s⁻¹ * localEOWRealLinearPart ys v a) =
          localEOWRealLinearPart ys v a
        field_simp [hs_ne]
      exact_mod_cast hreal
    have hpoint :
        Fplus (localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I)) =
          Fplus (fun a => (localEOWRealChart x0 ys u a : ℂ) +
            (s : ℂ) * (η a : ℂ) * Complex.I) := by
      congr 1
      rw [localEOWChart_real_add_imag]
      ext a
      rw [hscale a]
    rw [hpoint]
    exact hplus_bound (localEOWRealChart x0 ys u)
      ⟨u, hu, rfl⟩ η hη s (by simpa [s] using hs_pos)
      (by simpa [s] using hs_lt)
  · intro u hu v hv_nonpos hs_pos hs_lt
    let s : ℝ := ∑ j, -v j
    let η : Fin m → ℝ := s⁻¹ • localEOWRealLinearPart ys (-v)
    have hw_nonneg : ∀ j, 0 ≤ (-v) j := by
      intro j
      exact neg_nonneg.mpr (hv_nonpos j)
    have hη : η ∈ Kη := by
      dsimp [η, s, Kη]
      rw [localEOWRealLinearPart_eq_sum_smul]
      exact localEOW_positive_imag_normalized_mem_simplex
        (ys := ys) hw_nonneg hs_pos
    have hs_ne : s ≠ 0 := ne_of_gt (by simpa [s] using hs_pos)
    have hscale : ∀ a,
        (s : ℂ) * (η a : ℂ) =
          (localEOWRealLinearPart ys (-v) a : ℂ) := by
      intro a
      have hreal : s * η a = localEOWRealLinearPart ys (-v) a := by
        dsimp [η]
        change s * (s⁻¹ * localEOWRealLinearPart ys (-v) a) =
          localEOWRealLinearPart ys (-v) a
        field_simp [hs_ne]
      exact_mod_cast hreal
    have hpoint :
        Fminus (localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I)) =
          Fminus (fun a => (localEOWRealChart x0 ys u a : ℂ) -
            (s : ℂ) * (η a : ℂ) * Complex.I) := by
      congr 1
      rw [localEOWChart_real_add_imag]
      ext a
      have hneg : localEOWRealLinearPart ys (-v) a =
          -localEOWRealLinearPart ys v a := by
        rw [localEOWRealLinearPart_neg]
        rfl
      rw [hscale a, hneg]
      simp
    rw [hpoint]
    exact hminus_bound (localEOWRealChart x0 ys u)
      ⟨u, hu, rfl⟩ η hη s (by simpa [s] using hs_pos)
      (by simpa [s] using hs_lt)

/-- Transport a uniform original-coordinate cone boundary value to the strict
positive and negative coordinate orthants of a local EOW chart. -/
theorem chartOrthantBoundaryValue_from_uniformConeBoundaryValue
    {m : ℕ} (hm : 0 < m)
    (E C : Set (Fin m → ℝ))
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys_mem : ∀ j, ys j ∈ C)
    (hli : LinearIndependent ℝ ys)
    (x0 : Fin m → ℝ)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_bv :
      ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
        ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
          HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
          tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : Fin m → ℝ,
                Fplus (fun a => (x a : ℂ) +
                  (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : Fin m → ℝ => T φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη)
    (hminus_bv :
      ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
        ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
          HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
          tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : Fin m → ℝ,
                Fminus (fun a => (x a : ℂ) -
                  (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : Fin m → ℝ => T φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (hφ_compact : HasCompactSupport (φ : (Fin m → ℝ) → ℂ))
    (hφ_chart_support :
      ∀ u ∈ tsupport (φ : (Fin m → ℝ) → ℂ),
        localEOWRealChart x0 ys u ∈ E) :
    let FplusChart : ComplexChartSpace m → ℂ :=
      fun w => Fplus (localEOWChart x0 ys w)
    let FminusChart : ComplexChartSpace m → ℂ :=
      fun w => Fminus (localEOWChart x0 ys w)
    let Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
      localEOWAffineDistributionPullbackCLM x0 ys hli T
    (Filter.Tendsto
      (fun y : Fin m → ℝ =>
        ∫ u : Fin m → ℝ,
          FplusChart (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I) * φ u)
      (nhdsWithin 0 {y : Fin m → ℝ | ∀ j, 0 < y j})
      (nhds (Tchart φ))) ∧
    (Filter.Tendsto
      (fun y : Fin m → ℝ =>
        ∫ u : Fin m → ℝ,
          FminusChart (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I) * φ u)
      (nhdsWithin 0 {y : Fin m → ℝ | ∀ j, y j < 0})
      (nhds (Tchart φ))) := by
  dsimp
  let ψ : SchwartzMap (Fin m → ℝ) ℂ :=
    localEOWAffineTestPushforwardCLM x0 ys hli φ
  have hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ) := by
    dsimp [ψ]
    exact HasCompactSupport.localEOWAffineTestPushforwardCLM x0 ys hli
      hφ_compact
  have hψ_support : tsupport (ψ : (Fin m → ℝ) → ℂ) ⊆ E := by
    intro x hx
    have hx_img :=
      tsupport_localEOWAffineTestPushforwardCLM_subset x0 ys hli φ hx
    rcases hx_img with ⟨u, hu, rfl⟩
    exact hφ_chart_support u hu
  let Kη : Set (Fin m → ℝ) := localEOWSimplexDirections ys
  have hKη_compact : IsCompact Kη := by
    dsimp [Kη]
    exact isCompact_localEOWSimplexDirections ys
  have hKη_C : Kη ⊆ C := by
    dsimp [Kη]
    exact localEOWSimplexDirections_subset_cone C hC_conv ys hys_mem
  constructor
  · let lplus := nhdsWithin 0 {y : Fin m → ℝ | ∀ j, 0 < y j}
    let splus : (Fin m → ℝ) → ℝ := fun y => ∑ j, y j
    let etaplus : (Fin m → ℝ) → Fin m → ℝ :=
      fun y => (splus y)⁻¹ • localEOWRealLinearPart ys y
    have hη_event : ∀ᶠ y in lplus, etaplus y ∈ Kη := by
      haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy_nonneg : ∀ j, 0 ≤ y j := fun j => (hy j).le
      have hsum_pos : 0 < ∑ j, y j :=
        Finset.sum_pos (fun j _hj => hy j) Finset.univ_nonempty
      dsimp [etaplus, splus, Kη]
      rw [show localEOWRealLinearPart ys y = ∑ j, y j • ys j by
        ext a
        simp [localEOWRealLinearPart]]
      exact localEOW_positive_imag_normalized_mem_simplex
        (ys := ys) hy_nonneg hsum_pos
    have hplus_uniform :=
      hplus_bv Kη hKη_compact hKη_C ψ hψ_compact hψ_support
    have hplus_orig :
        Filter.Tendsto
          (fun y : Fin m → ℝ =>
            ∫ x : Fin m → ℝ,
              Fplus (fun a => (x a : ℂ) +
                (splus y : ℂ) * (etaplus y a : ℂ) * Complex.I) * ψ x)
          lplus (nhds (T ψ)) := by
      exact tendstoUniformlyOn_const_comp_of_tendsto_of_eventually_mem
        (F := fun (ε : ℝ) (η : Fin m → ℝ) =>
          ∫ x : Fin m → ℝ,
            Fplus (fun a => (x a : ℂ) +
              (ε : ℂ) * (η a : ℂ) * Complex.I) * ψ x)
        (c := T ψ) (a := splus) (b := etaplus)
        hplus_uniform
        (coordSum_tendsto_positiveOrthant_nhdsWithin_Ioi hm)
        hη_event
    have hplus_scaled :
        Filter.Tendsto
          (fun y : Fin m → ℝ =>
            ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
              ∫ x : Fin m → ℝ,
                Fplus (fun a => (x a : ℂ) +
                  (splus y : ℂ) * (etaplus y a : ℂ) * Complex.I) * ψ x)
          lplus
          (nhds (localEOWAffineDistributionPullbackCLM x0 ys hli T φ)) := by
      have h := hplus_orig.const_mul ((localEOWRealJacobianAbs ys)⁻¹ : ℂ)
      simpa [ψ, localEOWAffineDistributionPullbackCLM_apply] using h
    have hplus_eq :
        (fun y : Fin m → ℝ =>
            ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
              ∫ x : Fin m → ℝ,
                Fplus (fun a => (x a : ℂ) +
                  (splus y : ℂ) * (etaplus y a : ℂ) * Complex.I) * ψ x) =ᶠ[lplus]
          (fun y : Fin m → ℝ =>
            ∫ u : Fin m → ℝ,
              Fplus (localEOWChart x0 ys
                (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I)) * φ u) := by
      haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hsum_pos : 0 < splus y := by
        dsimp [splus]
        exact Finset.sum_pos (fun j _hj => hy j) Finset.univ_nonempty
      have hs_ne : splus y ≠ 0 := ne_of_gt hsum_pos
      have hscale : ∀ a,
          (splus y : ℂ) * (etaplus y a : ℂ) =
            (localEOWRealLinearPart ys y a : ℂ) := by
        intro a
        have hreal :
            splus y * etaplus y a = localEOWRealLinearPart ys y a := by
          dsimp [etaplus]
          change splus y *
              ((splus y)⁻¹ * localEOWRealLinearPart ys y a) =
            localEOWRealLinearPart ys y a
          field_simp [hs_ne]
        exact_mod_cast hreal
      have hpoint : ∀ u : Fin m → ℝ,
          Fplus (localEOWChart x0 ys
              (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I)) =
            Fplus (fun a => (localEOWRealChart x0 ys u a : ℂ) +
              (splus y : ℂ) * (etaplus y a : ℂ) * Complex.I) := by
        intro u
        congr 1
        rw [localEOWChart_real_add_imag]
        ext a
        rw [hscale a]
      let g : (Fin m → ℝ) → ℂ := fun x =>
        Fplus (fun a => (x a : ℂ) +
          (splus y : ℂ) * (etaplus y a : ℂ) * Complex.I)
      calc
        ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
            ∫ x : Fin m → ℝ,
              Fplus (fun a => (x a : ℂ) +
                (splus y : ℂ) * (etaplus y a : ℂ) * Complex.I) * ψ x =
          ∫ u : Fin m → ℝ, g (localEOWRealChart x0 ys u) * φ u := by
            dsimp [g, ψ]
            exact integral_localEOWAffineTestPushforwardCLM_changeOfVariables
              x0 ys hli (fun x => Fplus (fun a => (x a : ℂ) +
                (splus y : ℂ) * (etaplus y a : ℂ) * Complex.I)) φ
        _ = ∫ u : Fin m → ℝ,
              Fplus (localEOWChart x0 ys
                (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I)) * φ u := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with u
            dsimp [g]
            rw [hpoint u]
    exact hplus_scaled.congr' hplus_eq
  · let lminus := nhdsWithin 0 {y : Fin m → ℝ | ∀ j, y j < 0}
    let sminus : (Fin m → ℝ) → ℝ := fun y => ∑ j, -y j
    let etaminus : (Fin m → ℝ) → Fin m → ℝ :=
      fun y => (sminus y)⁻¹ • localEOWRealLinearPart ys (-y)
    have hη_event : ∀ᶠ y in lminus, etaminus y ∈ Kη := by
      haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy_nonneg : ∀ j, 0 ≤ -y j :=
        fun j => (neg_pos.mpr (hy j)).le
      have hsum_pos : 0 < ∑ j, -y j :=
        Finset.sum_pos (fun j _hj => neg_pos.mpr (hy j))
          Finset.univ_nonempty
      dsimp [etaminus, sminus, Kη]
      rw [show localEOWRealLinearPart ys (-y) = ∑ j, (-y j) • ys j by
        ext a
        simp [localEOWRealLinearPart]]
      exact localEOW_positive_imag_normalized_mem_simplex
        (ys := ys) hy_nonneg hsum_pos
    have hminus_uniform :=
      hminus_bv Kη hKη_compact hKη_C ψ hψ_compact hψ_support
    have hminus_orig :
        Filter.Tendsto
          (fun y : Fin m → ℝ =>
            ∫ x : Fin m → ℝ,
              Fminus (fun a => (x a : ℂ) -
                (sminus y : ℂ) * (etaminus y a : ℂ) * Complex.I) * ψ x)
          lminus (nhds (T ψ)) := by
      exact tendstoUniformlyOn_const_comp_of_tendsto_of_eventually_mem
        (F := fun (ε : ℝ) (η : Fin m → ℝ) =>
          ∫ x : Fin m → ℝ,
            Fminus (fun a => (x a : ℂ) -
              (ε : ℂ) * (η a : ℂ) * Complex.I) * ψ x)
        (c := T ψ) (a := sminus) (b := etaminus)
        hminus_uniform
        (coordNegSum_tendsto_negativeOrthant_nhdsWithin_Ioi hm)
        hη_event
    have hminus_scaled :
        Filter.Tendsto
          (fun y : Fin m → ℝ =>
            ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
              ∫ x : Fin m → ℝ,
                Fminus (fun a => (x a : ℂ) -
                  (sminus y : ℂ) * (etaminus y a : ℂ) * Complex.I) * ψ x)
          lminus
          (nhds (localEOWAffineDistributionPullbackCLM x0 ys hli T φ)) := by
      have h := hminus_orig.const_mul ((localEOWRealJacobianAbs ys)⁻¹ : ℂ)
      simpa [ψ, localEOWAffineDistributionPullbackCLM_apply] using h
    have hminus_eq :
        (fun y : Fin m → ℝ =>
            ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
              ∫ x : Fin m → ℝ,
                Fminus (fun a => (x a : ℂ) -
                  (sminus y : ℂ) * (etaminus y a : ℂ) * Complex.I) * ψ x) =ᶠ[lminus]
          (fun y : Fin m → ℝ =>
            ∫ u : Fin m → ℝ,
              Fminus (localEOWChart x0 ys
                (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I)) * φ u) := by
      haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hsum_pos : 0 < sminus y := by
        dsimp [sminus]
        exact Finset.sum_pos (fun j _hj => neg_pos.mpr (hy j))
          Finset.univ_nonempty
      have hs_ne : sminus y ≠ 0 := ne_of_gt hsum_pos
      have hscale : ∀ a,
          (sminus y : ℂ) * (etaminus y a : ℂ) =
            (localEOWRealLinearPart ys (-y) a : ℂ) := by
        intro a
        have hreal :
            sminus y * etaminus y a = localEOWRealLinearPart ys (-y) a := by
          dsimp [etaminus]
          change sminus y *
              ((sminus y)⁻¹ * localEOWRealLinearPart ys (-y) a) =
            localEOWRealLinearPart ys (-y) a
          field_simp [hs_ne]
        exact_mod_cast hreal
      have hpoint : ∀ u : Fin m → ℝ,
          Fminus (localEOWChart x0 ys
              (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I)) =
            Fminus (fun a => (localEOWRealChart x0 ys u a : ℂ) -
              (sminus y : ℂ) * (etaminus y a : ℂ) * Complex.I) := by
        intro u
        congr 1
        rw [localEOWChart_real_add_imag]
        ext a
        have hneg : localEOWRealLinearPart ys (-y) a =
            -localEOWRealLinearPart ys y a := by
          rw [localEOWRealLinearPart_neg]
          rfl
        rw [hscale a, hneg]
        simp
      let g : (Fin m → ℝ) → ℂ := fun x =>
        Fminus (fun a => (x a : ℂ) -
          (sminus y : ℂ) * (etaminus y a : ℂ) * Complex.I)
      calc
        ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
            ∫ x : Fin m → ℝ,
              Fminus (fun a => (x a : ℂ) -
                (sminus y : ℂ) * (etaminus y a : ℂ) * Complex.I) * ψ x =
          ∫ u : Fin m → ℝ, g (localEOWRealChart x0 ys u) * φ u := by
            dsimp [g, ψ]
            exact integral_localEOWAffineTestPushforwardCLM_changeOfVariables
              x0 ys hli (fun x => Fminus (fun a => (x a : ℂ) -
                (sminus y : ℂ) * (etaminus y a : ℂ) * Complex.I)) φ
        _ = ∫ u : Fin m → ℝ,
              Fminus (localEOWChart x0 ys
                (fun j => (u j : ℂ) + (y j : ℂ) * Complex.I)) * φ u := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with u
            dsimp [g]
            rw [hpoint u]
    exact hminus_scaled.congr' hminus_eq

/-- Pull holomorphy back through the affine local EOW chart on any coordinate
set whose image lies in the original domain. -/
theorem chartHolomorphy_from_originalHolomorphy
    (Ω : Set (ComplexChartSpace m))
    (x0 : Fin m → ℝ)
    (ys : Fin m → Fin m → ℝ)
    (F : ComplexChartSpace m → ℂ)
    (Ucoord : Set (ComplexChartSpace m))
    (hU_mem : ∀ w ∈ Ucoord, localEOWChart x0 ys w ∈ Ω)
    (hF : DifferentiableOn ℂ F Ω) :
    DifferentiableOn ℂ (fun w => F (localEOWChart x0 ys w)) Ucoord := by
  simpa [Function.comp_def] using
    hF.comp (differentiable_localEOWChart x0 ys).differentiableOn hU_mem

/-- Real-coordinate translation in the local chart corresponds to translation
by the chart's linear part on the original real edge. -/
theorem localEOWRealChart_sub
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (u v : Fin m → ℝ) :
    localEOWRealChart x0 ys (u - v) =
      localEOWRealChart x0 ys u - localEOWRealLinearPart ys v := by
  ext a
  simp [localEOWRealChart, localEOWRealLinearPart]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-- Additive form of the real-coordinate chart displacement identity. -/
theorem localEOWRealChart_add
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (u v : Fin m → ℝ) :
    localEOWRealChart x0 ys (u + v) =
      localEOWRealChart x0 ys u + localEOWRealLinearPart ys v := by
  ext a
  simp [localEOWRealChart, localEOWRealLinearPart, add_mul,
    Finset.sum_add_distrib]
  ring

/-- Complex-chart version of the displacement identity.  This is the coordinate
accounting needed before a product-kernel covariance theorem can be stated:
the original real-edge displacement is `localEOWRealLinearPart ys v`, not `v`
unless the chosen chart basis is the standard one. -/
theorem localEOWChart_sub_realEmbed
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (w : Fin m → ℂ) (v : Fin m → ℝ) :
    localEOWChart x0 ys (w - realEmbed v) =
      localEOWChart x0 ys w - realEmbed (localEOWRealLinearPart ys v) := by
  ext a
  simp [localEOWChart, realEmbed, localEOWRealLinearPart,
    sub_eq_add_neg, add_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  ring

/-- Additive complex-chart displacement identity. -/
theorem localEOWChart_add_realEmbed
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (w : Fin m → ℂ) (v : Fin m → ℝ) :
    localEOWChart x0 ys (w + realEmbed v) =
      localEOWChart x0 ys w + realEmbed (localEOWRealLinearPart ys v) := by
  ext a
  simp [localEOWChart, realEmbed, localEOWRealLinearPart, add_mul,
    Finset.sum_add_distrib]
  ring

end SCV
