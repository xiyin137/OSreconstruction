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
