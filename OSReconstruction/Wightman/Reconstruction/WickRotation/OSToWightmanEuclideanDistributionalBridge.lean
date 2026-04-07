/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanTubeIdentity

/-!
# Euclidean Distributional Bridge

Support module for the strict OS-II route from Euclidean Wick-section
distributional equalities to one-parameter Lorentz-generator invariance on the
forward tube.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW
namespace Task2Bridge

/-- Wick rotation matrix `W = diag(i, 1, ..., 1)`. -/
def wickW : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal (fun i => if i = (0 : Fin (d + 1)) then Complex.I else 1)

/-- Inverse Wick rotation matrix `W⁻¹ = diag(-i, 1, ..., 1)`. -/
def wickWinv : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal (fun i => if i = (0 : Fin (d + 1)) then -Complex.I else 1)

theorem wickW_mul_wickWinv :
    (wickW : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * wickWinv = 1 := by
  simp only [wickW, wickWinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  split_ifs <;> simp [Complex.I_mul_I]

theorem wickWinv_mul_wickW :
    (wickWinv : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * wickW = 1 := by
  simp only [wickW, wickWinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  split_ifs <;> simp [Complex.I_mul_I]

/-- `ofEuclidean(R).val = W * R_ℂ * W⁻¹`. -/
theorem ofEuclidean_val_eq_wick_conjugation
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.det = 1) (horth : R.transpose * R = 1) :
    (ComplexLorentzGroup.ofEuclidean R hR horth).val =
      wickW * R.map Complex.ofReal * wickWinv := by
  ext μ ν
  simp only [ComplexLorentzGroup.ofEuclidean, wickW, wickWinv,
    Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem wickW_mul_eta :
    (wickW : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *
      (ComplexLorentzGroup.ηℂ (d := d)) = wickWinv := by
  simp only [wickW, wickWinv, ComplexLorentzGroup.ηℂ, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp only [minkowskiSignature]
  split_ifs <;> push_cast <;> simp

private theorem eta_mul_wickW :
    (ComplexLorentzGroup.ηℂ (d := d)) *
      (wickW : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = wickWinv := by
  simp only [wickW, wickWinv, ComplexLorentzGroup.ηℂ, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp only [minkowskiSignature]
  split_ifs <;> push_cast <;> simp

private theorem wickW_transpose :
    (wickW : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose = wickW :=
  Matrix.diagonal_transpose _

private theorem wickWinv_transpose :
    (wickWinv : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose = wickWinv :=
  Matrix.diagonal_transpose _

/-- The Wick-rotated Euclidean generator lies in the complex Lorentz Lie algebra. -/
theorem wick_rotated_isInLieAlgebra
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : Y.transpose + Y = 0) :
    ComplexLorentzGroup.IsInLieAlgebra (wickW * Y.map Complex.ofReal * wickWinv) := by
  unfold ComplexLorentzGroup.IsInLieAlgebra
  set Yc := Y.map Complex.ofReal
  have hYc_skew : Yc.transpose = -Yc := by
    ext i j
    simp only [Yc, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply]
    have := congr_fun (congr_fun hY j) i
    simp [Matrix.add_apply, Matrix.transpose_apply] at this
    have h : Y j i = -Y i j := by linarith
    rw [h]
    push_cast
    ring
  have hZT : (wickW * Yc * wickWinv).transpose = wickWinv * (-Yc) * wickW := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, wickWinv_transpose, hYc_skew,
      wickW_transpose]
    simp [Matrix.mul_assoc]
  rw [hZT]
  change wickWinv * -Yc * wickW * ComplexLorentzGroup.ηℂ +
      ComplexLorentzGroup.ηℂ * (wickW * Yc * wickWinv) = 0
  rw [Matrix.mul_assoc (wickWinv * -Yc) wickW, wickW_mul_eta]
  conv_lhs =>
    rw [show ComplexLorentzGroup.ηℂ * (wickW * Yc * wickWinv) =
      (ComplexLorentzGroup.ηℂ * wickW) * Yc * wickWinv from by
        simp only [Matrix.mul_assoc]]
  rw [eta_mul_wickW, Matrix.mul_neg, Matrix.neg_mul, neg_add_cancel]

/-- `exp(s * W Y_ℂ W⁻¹) = W * exp(s * Y_ℂ) * W⁻¹`. -/
theorem exp_wick_conjugation
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (s : ℂ) :
    NormedSpace.exp (s • (wickW * Y.map Complex.ofReal * wickWinv)) =
      wickW * NormedSpace.exp (s • Y.map Complex.ofReal) * wickWinv := by
  have h_smul : s • (wickW * Y.map Complex.ofReal * wickWinv) =
      wickW * (s • Y.map Complex.ofReal) * wickWinv := by
    ext i j
    simp [wickW, wickWinv, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply,
      Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, smul_eq_mul]
    ring_nf
  rw [h_smul]
  let Wunit : (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)ˣ :=
    ⟨wickW, wickWinv, wickW_mul_wickWinv, wickWinv_mul_wickW⟩
  have := NormedSpace.exp_units_conj Wunit (s • Y.map Complex.ofReal)
  convert this using 2

private theorem exp_map_ofReal_bridge
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (s : ℝ) :
    (NormedSpace.exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal =
      NormedSpace.exp ((s : ℂ) • Y.map Complex.ofReal) := by
  have hcont : Continuous (Complex.ofRealHom.mapMatrix :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  have h1 : Complex.ofRealHom.mapMatrix (NormedSpace.exp (s • Y)) =
      NormedSpace.exp (Complex.ofRealHom.mapMatrix (s • Y)) :=
    map_exp (f := Complex.ofRealHom.mapMatrix) hcont (s • Y)
  have h2 : Complex.ofRealHom.mapMatrix (s • Y) = (s : ℂ) • Y.map Complex.ofReal := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
  change Complex.ofRealHom.mapMatrix (NormedSpace.exp (s • Y)) = _
  rw [h1, h2]

private theorem exp_real_orthogonal
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : Y.transpose + Y = 0) (s : ℝ) :
    (NormedSpace.exp (s • Y) : Matrix _ _ ℝ).transpose * NormedSpace.exp (s • Y) = 1 := by
  have hskew : (s • Y).transpose = -(s • Y) := by
    ext i j
    have hij := congr_fun (congr_fun hY i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at hij
    have hji : Y j i = -Y i j := by linarith
    simp [Matrix.transpose_apply, Matrix.smul_apply, hji]
  rw [← Matrix.exp_transpose, hskew, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp (s • Y)))

private theorem exp_real_det_one_skew
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : Y.transpose + Y = 0) (s : ℝ) :
    (NormedSpace.exp (s • Y) : Matrix _ _ ℝ).det = 1 := by
  have hYskew : SOComplex.IsSkewSymm (Y.map Complex.ofReal) := by
    unfold SOComplex.IsSkewSymm
    ext i j
    have hij := congr_fun (congr_fun hY i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at hij
    have hji : Y j i = -Y i j := by linarith
    simp [Matrix.transpose_apply, Matrix.map_apply, hji]
  have hdetC :
      (NormedSpace.exp ((s : ℂ) • Y.map Complex.ofReal) : Matrix _ _ ℂ).det = 1 :=
    SOComplex.exp_det_one_skew (SOComplex.isSkewSymm_smul (s : ℂ) hYskew)
  have hmapdet :
      (((NormedSpace.exp (s • Y) : Matrix _ _ ℝ).det : ℂ)) =
        (NormedSpace.exp ((s : ℂ) • Y.map Complex.ofReal) : Matrix _ _ ℂ).det := by
    calc
      (((NormedSpace.exp (s • Y) : Matrix _ _ ℝ).det : ℂ))
          = (((NormedSpace.exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal).det) := by
              simpa using
                (Complex.ofRealHom.map_det (NormedSpace.exp (s • Y) : Matrix _ _ ℝ))
      _ = (NormedSpace.exp ((s : ℂ) • Y.map Complex.ofReal) : Matrix _ _ ℂ).det := by
              exact congrArg Matrix.det (exp_map_ofReal_bridge Y s)
  exact Complex.ofReal_injective (hmapdet.trans hdetC)

theorem ofEuclidean_exp_eq_exp_wick
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (s : ℝ)
    (hdet : (NormedSpace.exp (s • Y) : Matrix _ _ ℝ).det = 1)
    (horth : (NormedSpace.exp (s • Y) : Matrix _ _ ℝ).transpose *
        NormedSpace.exp (s • Y) = 1) :
    (ComplexLorentzGroup.ofEuclidean (NormedSpace.exp (s • Y)) hdet horth).val =
      NormedSpace.exp ((s : ℂ) • (wickW * Y.map Complex.ofReal * wickWinv)) := by
  calc
    (ComplexLorentzGroup.ofEuclidean (NormedSpace.exp (s • Y)) hdet horth).val
      = wickW * (NormedSpace.exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal * wickWinv :=
          ofEuclidean_val_eq_wick_conjugation _ hdet horth
    _ = wickW * NormedSpace.exp ((s : ℂ) • Y.map Complex.ofReal) * wickWinv := by
          rw [exp_map_ofReal_bridge]
    _ = NormedSpace.exp ((s : ℂ) • (wickW * Y.map Complex.ofReal * wickWinv)) :=
          (exp_wick_conjugation Y (s : ℂ)).symm

private theorem exp_wick_action_eq_ofEuclidean_action
    {n : ℕ}
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : Y.transpose + Y = 0) (s : ℝ)
    (w : Fin n → Fin (d + 1) → ℂ) :
    (fun k μ =>
      ∑ ν, (NormedSpace.exp ((s : ℂ) • (wickW * Y.map Complex.ofReal * wickWinv)) :
        Matrix _ _ ℂ) μ ν * w k ν) =
      BHW.complexLorentzAction
        (ComplexLorentzGroup.ofEuclidean (NormedSpace.exp (s • Y))
          (exp_real_det_one_skew Y hY s) (exp_real_orthogonal Y hY s))
        w := by
  ext k μ
  apply Finset.sum_congr rfl
  intro ν _
  exact congrArg (fun a : ℂ => a * w k ν)
    ((congrFun
      (congrFun
        (ofEuclidean_exp_eq_exp_wick Y s
          (exp_real_det_one_skew Y hY s) (exp_real_orthogonal Y hY s)) μ) ν).symm)

/-- The one-parameter action `t ↦ exp(tX) · z` is differentiable in `t`. -/
private theorem differentiable_expAction_local
    {n : ℕ}
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (z : Fin n → Fin (d + 1) → ℂ) :
    Differentiable ℂ (fun t : ℂ =>
      (fun k (μ : Fin (d + 1)) => ∑ ν, (NormedSpace.exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν) :
      ℂ → Fin n → Fin (d + 1) → ℂ) := by
  have hexp : Differentiable ℂ (fun t : ℂ => (NormedSpace.exp (t • X) : Matrix _ _ ℂ)) :=
    fun t => (hasDerivAt_exp_smul_const X t).differentiableAt
  apply differentiable_pi.mpr
  intro k
  apply differentiable_pi.mpr
  intro μ
  apply Differentiable.fun_sum
  intro ν _
  exact ((differentiable_apply ν).comp ((differentiable_apply μ).comp hexp)).mul
    (differentiable_const _)

/-- Distributional Wick-section equality on the Euclidean rotation orbit gives
pointwise invariance under the corresponding Wick-rotated generator, locally in
the real parameter. This is the honest OS-II TASK 2 bridge. -/
theorem distributional_to_generator_zero (n : ℕ) [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_dist :
      ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (hR : R.det = 1) (horth : R.transpose * R = 1)
        (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n |
            (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
              BHW.complexLorentzAction
                (ComplexLorentzGroup.ofEuclidean R hR horth)
                (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            F (BHW.complexLorentzAction
              (ComplexLorentzGroup.ofEuclidean R hR horth)
              (fun k => wickRotatePoint (x k))) * φ x =
          ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) * φ x)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : Y.transpose + Y = 0)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∃ r : ℝ, 0 < r ∧
      ∀ s : ℝ, |s| < r →
        (fun k μ =>
          ∑ ν, (NormedSpace.exp ((s : ℂ) • (wickW * Y.map Complex.ofReal * wickWinv)) :
            Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n →
        F (fun k μ =>
          ∑ ν, (NormedSpace.exp ((s : ℂ) • (wickW * Y.map Complex.ofReal * wickWinv)) :
            Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  let Z := wickW * Y.map Complex.ofReal * wickWinv
  let x0 : NPointDomain d n :=
    fun k μ => if μ = 0 then (k : ℝ) + 1 else 0
  have hw0 : (fun k => wickRotatePoint (x0 k)) ∈ ForwardTube d n := by
    have hw0root : (fun k => wickRotatePoint (x0 k)) ∈ _root_.ForwardTube d n := by
      apply _root_.euclidean_ordered_in_forwardTube (d := d) (n := n) x0
      · intro i j hij
        simp [x0, hij]
      · intro i
        have : (0 : ℝ) < (i : ℝ) + 1 := by positivity
        simpa [x0] using this
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hw0root
  let action0 : ℝ → Fin n → Fin (d + 1) → ℂ :=
    fun s k μ => ∑ ν, (NormedSpace.exp ((s : ℂ) • Z) : Matrix _ _ ℂ) μ ν * wickRotatePoint (x0 k) ν
  have haction0_cont : Continuous action0 := by
    let action0c : ℂ → Fin n → Fin (d + 1) → ℂ :=
      fun t k μ => ∑ ν, (NormedSpace.exp (t • Z) : Matrix _ _ ℂ) μ ν * wickRotatePoint (x0 k) ν
    have hcont : Continuous action0c :=
      (differentiable_expAction_local Z (fun k => wickRotatePoint (x0 k))).continuous
    simpa [action0, action0c] using hcont.comp Complex.continuous_ofReal
  let U0 : Set ℝ := {s : ℝ | action0 s ∈ ForwardTube d n}
  have hU0_open : IsOpen U0 := by
    apply isOpen_forwardTube.preimage
    simpa [U0, action0] using haction0_cont
  have h0U0 : (0 : ℝ) ∈ U0 := by
    have hzero :
        action0 0 = fun k => wickRotatePoint (x0 k) := by
      ext k μ
      unfold action0
      rw [show (((0 : ℝ) : ℂ) • Z) = 0 by simp, NormedSpace.exp_zero]
      simp [Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ]
    change action0 0 ∈ ForwardTube d n
    rw [hzero]
    exact hw0
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU0_open 0 h0U0
  refine ⟨r, hr_pos, ?_⟩
  intro s hs_small hs_action_z
  let R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := NormedSpace.exp (s • Y)
  let Λ : ComplexLorentzGroup d :=
    ComplexLorentzGroup.ofEuclidean R
      (exp_real_det_one_skew Y hY s) (exp_real_orthogonal Y hY s)
  have hs_w0 :
      BHW.complexLorentzAction Λ (fun k => wickRotatePoint (x0 k)) ∈ ForwardTube d n := by
    have hsU0 : s ∈ U0 := by
      exact hr_sub (by rwa [Metric.mem_ball, dist_zero_right])
    have hs_action0 : action0 s ∈ ForwardTube d n := hsU0
    have hact0 :
        action0 s = BHW.complexLorentzAction Λ (fun k => wickRotatePoint (x0 k)) := by
      simpa [action0, Z, R, Λ] using
        exp_wick_action_eq_ofEuclidean_action (Y := Y) hY s (fun k => wickRotatePoint (x0 k))
    exact hact0 ▸ hs_action0
  have hzD :
      z ∈ {w | w ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ w ∈ ForwardTube d n} := by
    refine ⟨hz, ?_⟩
    have hactz :
        (fun k μ =>
          ∑ ν, (NormedSpace.exp ((s : ℂ) • (wickW * Y.map Complex.ofReal * wickWinv)) :
            Matrix _ _ ℂ) μ ν * z k ν) =
          BHW.complexLorentzAction Λ z := by
      simpa [Z, R, Λ] using exp_wick_action_eq_ofEuclidean_action (Y := Y) hY s z
    exact hactz ▸ hs_action_z
  have hFtrans :
      DifferentiableOn ℂ (fun w => F (BHW.complexLorentzAction Λ w))
        {w | w ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ w ∈ ForwardTube d n} := by
    intro w hw
    have hact_diff :
        DifferentiableWithinAt ℂ (BHW.complexLorentzAction Λ)
          {w | w ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ w ∈ ForwardTube d n} w := by
      have htmp : DifferentiableAt ℂ (BHW.complexLorentzAction Λ) w :=
        (BHW.differentiable_complexLorentzAction_snd (d := d) (n := n) Λ).differentiableAt
      exact htmp.differentiableWithinAt
    have hact_maps :
        Set.MapsTo (BHW.complexLorentzAction Λ)
          {w | w ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ w ∈ ForwardTube d n}
          (ForwardTube d n) := by
      intro w hw
      exact hw.2
    exact (hF_holo _ hw.2).comp w hact_diff hact_maps
  have hFD :
      DifferentiableOn ℂ F
        {w | w ∈ ForwardTube d n ∧ BHW.complexLorentzAction Λ w ∈ ForwardTube d n} := by
    exact hF_holo.mono (by intro w hw; exact hw.1)
  have hD_wick_nonempty_root :
      ∃ x : NPointDomain d n,
        (fun k => wickRotatePoint (x k)) ∈ _root_.ForwardTube d n ∧
          BHW.complexLorentzAction Λ (fun k => wickRotatePoint (x k)) ∈ _root_.ForwardTube d n := by
    refine ⟨x0, ?_, ?_⟩
    · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hw0
    · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hs_w0
  have hFtrans_root :
      DifferentiableOn ℂ (fun w => F (BHW.complexLorentzAction Λ w))
        {w | w ∈ _root_.ForwardTube d n ∧ BHW.complexLorentzAction Λ w ∈ _root_.ForwardTube d n} := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hFtrans
  have hFD_root :
      DifferentiableOn ℂ F
        {w | w ∈ _root_.ForwardTube d n ∧ BHW.complexLorentzAction Λ w ∈ _root_.ForwardTube d n} := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hFD
  have hzD_root :
      z ∈ {w | w ∈ _root_.ForwardTube d n ∧ BHW.complexLorentzAction Λ w ∈ _root_.ForwardTube d n} := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hzD
  have hEq :=
    eqOn_d_lambda_of_distributional_wickSection_eq (d := d) (n := n) Λ
      hD_wick_nonempty_root
      (fun w => F (BHW.complexLorentzAction Λ w)) F hFtrans_root hFD_root
      (fun φ hφ_compact hφ_tsupport => by
        have hφ_tsupport' :
            tsupport (φ : NPointDomain d n → ℂ) ⊆
              {x : NPointDomain d n |
                (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
                  BHW.complexLorentzAction
                    (ComplexLorentzGroup.ofEuclidean R
                      (exp_real_det_one_skew Y hY s) (exp_real_orthogonal Y hY s))
                    (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} := by
          simpa [BHW_forwardTube_eq (d := d) (n := n)] using hφ_tsupport
        exact hF_dist R (exp_real_det_one_skew Y hY s) (exp_real_orthogonal Y hY s)
          φ hφ_compact hφ_tsupport')
  have hEqz : F (BHW.complexLorentzAction Λ z) = F z := hEq hzD_root
  calc
    F (fun k μ =>
        ∑ ν, (NormedSpace.exp ((s : ℂ) • (wickW * Y.map Complex.ofReal * wickWinv)) :
          Matrix _ _ ℂ) μ ν * z k ν)
        = F (BHW.complexLorentzAction Λ z) := by
            rw [exp_wick_action_eq_ofEuclidean_action (Y := Y) hY s z]
    _ = F z := hEqz

/-- Near-zero holomorphic constancy along the Wick-rotated generator orbit,
derived from the distributional Euclidean hypothesis via the subdomain identity
theorem. -/
theorem single_generator_invariance_euclidean_distributional (n : ℕ) [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_dist :
      ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (hR : R.det = 1) (horth : R.transpose * R = 1)
        (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n |
            (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
              BHW.complexLorentzAction
                (ComplexLorentzGroup.ofEuclidean R hR horth)
                (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            F (BHW.complexLorentzAction
              (ComplexLorentzGroup.ofEuclidean R hR horth)
              (fun k => wickRotatePoint (x k))) * φ x =
          ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) * φ x)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : Y.transpose + Y = 0)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (NormedSpace.exp (t • (wickW * Y.map Complex.ofReal * wickWinv)) :
          Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n →
      F (fun k μ =>
        ∑ ν, (NormedSpace.exp (t • (wickW * Y.map Complex.ofReal * wickWinv)) :
          Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  set Z := wickW * Y.map Complex.ofReal * wickWinv
  set action : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t k μ => ∑ ν, (NormedSpace.exp (t • Z) : Matrix _ _ ℂ) μ ν * z k ν
  set U := {t : ℂ | action t ∈ ForwardTube d n}
  have hU_open : IsOpen U := by
    apply isOpen_forwardTube.preimage
    exact (differentiable_expAction_local Z z).continuous
  have h0U : (0 : ℂ) ∈ U := by
    simp only [U, Set.mem_setOf_eq, action]
    convert hz using 2
    ext k
    simp [NormedSpace.exp_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ]
  set g : ℂ → ℂ := fun t => F (action t) - F z
  have hg_diff : DifferentiableOn ℂ g U := by
    apply DifferentiableOn.sub
    · exact hF_holo.comp (differentiable_expAction_local Z z).differentiableOn (fun t ht => ht)
    · exact differentiableOn_const _
  have hg_analytic : AnalyticAt ℂ g 0 :=
    hg_diff.analyticAt (hU_open.mem_nhds h0U)
  obtain ⟨r0, hr0_pos, hreal_local⟩ :=
    distributional_to_generator_zero (d := d) n F hF_holo hF_dist Y hY z hz
  have hg_freq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    obtain ⟨r', hr'_pos, hr'_sub⟩ := Metric.isOpen_iff.mp hU_open 0 h0U
    set s := min (r / 2) (min (r' / 2) (r0 / 2)) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]
      have hs_le_r : s ≤ r / 2 := min_le_left _ _
      linarith)
    have hs_in_U : (s : ℂ) ∈ U := hr'_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]
      have hs_le_r' : s ≤ min (r' / 2) (r0 / 2) := min_le_right _ _
      have hs_le_r'' : min (r' / 2) (r0 / 2) ≤ r' / 2 := min_le_left _ _
      linarith)
    have hs_small : |s| < r0 := by
      rw [abs_of_pos hs_pos]
      have hs_le_r0 : s ≤ min (r' / 2) (r0 / 2) := min_le_right _ _
      have hs_le_r0' : min (r' / 2) (r0 / 2) ≤ r0 / 2 := min_le_right _ _
      linarith
    have hg_real : g (s : ℂ) = 0 := by
      simp only [g, sub_eq_zero]
      exact hreal_local s hs_small hs_in_U
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ hg_real
  have hg_zero := hg_analytic.frequently_zero_iff_eventually_zero.mp hg_freq
  exact hg_zero.mono (fun t ht _ => by
    simp only [g, sub_eq_zero] at ht
    exact ht)

/-- Full-domain distributional Euclidean single-generator invariance: once the
real-parameter bridge is available near `0`, the one-variable identity theorem
propagates the equality to any preconnected open subset of the parameter domain
that stays inside `ForwardTube`. This is the exact replacement for the old
pointwise Euclidean-input version. -/
theorem full_domain_generator_invariance_euclidean_distributional
    (n : ℕ) [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_dist :
      ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (hR : R.det = 1) (horth : R.transpose * R = 1)
        (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n |
            (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
              BHW.complexLorentzAction
                (ComplexLorentzGroup.ofEuclidean R hR horth)
                (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            F (BHW.complexLorentzAction
              (ComplexLorentzGroup.ofEuclidean R hR horth)
              (fun k => wickRotatePoint (x k))) * φ x =
          ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) * φ x)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : Y.transpose + Y = 0)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_pre : IsPreconnected U)
    (h0U : (0 : ℂ) ∈ U)
    (hU_sub : ∀ t ∈ U, (fun k (μ : Fin (d + 1)) =>
      ∑ ν, (NormedSpace.exp (t • (wickW * Y.map Complex.ofReal * wickWinv)) :
        Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n) :
    ∀ t ∈ U, F (fun k μ =>
      ∑ ν, (NormedSpace.exp (t • (wickW * Y.map Complex.ofReal * wickWinv)) :
        Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  set Z := wickW * Y.map Complex.ofReal * wickWinv
  set action : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t k μ => ∑ ν, (NormedSpace.exp (t • Z) : Matrix _ _ ℂ) μ ν * z k ν
  set g : ℂ → ℂ := fun t => F (action t) - F z
  have hg_diff : DifferentiableOn ℂ g U := by
    apply DifferentiableOn.sub
    · exact hF_holo.comp (differentiable_expAction_local Z z).differentiableOn
        (fun t ht => hU_sub t ht)
    · exact differentiableOn_const _
  have hg_analytic : AnalyticOnNhd ℂ g U :=
    hg_diff.analyticOnNhd hU_open
  obtain ⟨r0, hr0_pos, hreal_local⟩ :=
    distributional_to_generator_zero (d := d) n F hF_holo hF_dist Y hY z hz
  have hg_freq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    obtain ⟨r', hr'_pos, hr'_sub⟩ := Metric.isOpen_iff.mp hU_open 0 h0U
    set s := min (r / 2) (min (r' / 2) (r0 / 2)) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]
      have hs_le_r : s ≤ r / 2 := min_le_left _ _
      linarith)
    have hs_in_U : (s : ℂ) ∈ U := hr'_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]
      have hs_le_r' : s ≤ min (r' / 2) (r0 / 2) := min_le_right _ _
      have hs_le_r'' : min (r' / 2) (r0 / 2) ≤ r' / 2 := min_le_left _ _
      linarith)
    have hs_small : |s| < r0 := by
      rw [abs_of_pos hs_pos]
      have hs_le_r0 : s ≤ min (r' / 2) (r0 / 2) := min_le_right _ _
      have hs_le_r0' : min (r' / 2) (r0 / 2) ≤ r0 / 2 := min_le_right _ _
      linarith
    have hg_real : g (s : ℂ) = 0 := by
      simp only [g, sub_eq_zero]
      exact hreal_local s hs_small (hU_sub (s : ℂ) hs_in_U)
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ hg_real
  have hg_zero := hg_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hU_pre h0U hg_freq
  intro t ht
  have := hg_zero ht
  simp only [g, Pi.zero_apply, sub_eq_zero] at this
  exact this

end Task2Bridge

namespace Task3Bridge

open Task2Bridge

/-- The "Wick real part" of a complex Lorentz generator: projection onto the
Wick-rotated Euclidean real form. -/
def wickRePart (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun μ ν =>
    let w_inv_μ : ℂ := if μ = (0 : Fin (d + 1)) then -Complex.I else 1
    let w_ν : ℂ := if ν = (0 : Fin (d + 1)) then Complex.I else 1
    let w_μ : ℂ := if μ = (0 : Fin (d + 1)) then Complex.I else 1
    let w_inv_ν : ℂ := if ν = (0 : Fin (d + 1)) then -Complex.I else 1
    w_μ * (w_inv_μ * X μ ν * w_ν).re * w_inv_ν

/-- Undo Wick conjugation and take the real part entrywise. -/
def wickRePreimage (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun μ ν =>
    let w_inv_μ : ℂ := if μ = (0 : Fin (d + 1)) then -Complex.I else 1
    let w_ν : ℂ := if ν = (0 : Fin (d + 1)) then Complex.I else 1
    (w_inv_μ * X μ ν * w_ν).re

private theorem wickRePart_preimage_skew_aux
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    (wickRePreimage X).transpose + wickRePreimage X =
      (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
  ext i j
  unfold ComplexLorentzGroup.IsInLieAlgebra at hX
  have hij := congr_fun (congr_fun hX i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    ComplexLorentzGroup.ηℂ, Matrix.diagonal_apply, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hij
  by_cases hi : i = (0 : Fin (d + 1))
  · by_cases hj : j = (0 : Fin (d + 1))
    · subst hi
      subst hj
      have hre := (Complex.ext_iff.mp hij).1
      simp [minkowskiSignature] at hre
      simp [wickRePreimage]
      linarith
    · subst hi
      have him := (Complex.ext_iff.mp hij).2
      simp [minkowskiSignature, hj] at him
      simp [wickRePreimage, hj]
      linarith
  · by_cases hj : j = (0 : Fin (d + 1))
    · subst hj
      have him := (Complex.ext_iff.mp hij).2
      simp [minkowskiSignature, hi] at him
      simp [wickRePreimage, hi]
      linarith
    · have hre := (Complex.ext_iff.mp hij).1
      simp [minkowskiSignature, hi, hj] at hre
      simp [wickRePreimage, hi, hj]
      linarith

theorem wickRePart_preimage_skew
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    (wickRePreimage X).transpose + wickRePreimage X =
      (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
  wickRePart_preimage_skew_aux X hX

theorem wickRePart_eq_wick_conjugation_preimage
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    wickRePart X = wickW * (wickRePreimage X).map Complex.ofReal * wickWinv := by
  ext μ ν
  simp only [wickRePart, wickRePreimage, wickW, wickWinv,
    Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply,
    mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem norm_wickRePart_le
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖wickRePart X‖ ≤ ‖X‖ := by
  simp only [← coe_nnnorm, NNReal.coe_le_coe]
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  apply Finset.sup_le
  intro i _
  apply le_trans _ (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  apply Finset.sum_le_sum
  intro j _
  by_cases hi : i = (0 : Fin (d + 1))
  · by_cases hj : j = (0 : Fin (d + 1))
    · subst hi
      subst hj
      simp [wickRePart]
      simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (X 0 0)
    · subst hi
      simp [wickRePart, hj]
      simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (X 0 j)
  · by_cases hj : j = (0 : Fin (d + 1))
    · subst hj
      simp [wickRePart, hi]
      simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (X i 0)
    · simp [wickRePart, hi, hj]
      simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (X i j)

private theorem norm_wickImPart_le
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖wickRePart ((-Complex.I) • X)‖ ≤ ‖X‖ := by
  calc
    ‖wickRePart ((-Complex.I) • X)‖ ≤ ‖(-Complex.I) • X‖ :=
      norm_wickRePart_le ((-Complex.I) • X)
    _ = ‖(-Complex.I : ℂ)‖ * ‖X‖ := norm_smul _ _
    _ = ‖X‖ := by simp

private theorem norm_affine_combination_lt_euclidean
    (X₁ X₂ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX₁_le : ‖X₁‖ ≤ ‖X‖) (hX₂_le : ‖X₂‖ ≤ ‖X‖)
    {δ : ℝ} (hsmall : ‖X‖ < δ / 7) {s : ℂ} (hs : ‖s‖ < 2) :
    ‖X₁ + s • X₂‖ < δ :=
  calc
    ‖X₁ + s • X₂‖ ≤ ‖X₁‖ + ‖s • X₂‖ := norm_add_le _ _
    _ ≤ ‖X₁‖ + ‖s‖ * ‖X₂‖ := add_le_add (le_refl _) (norm_smul_le s X₂)
    _ ≤ ‖X‖ + 2 * ‖X‖ := add_le_add hX₁_le
        (mul_le_mul (le_of_lt hs) hX₂_le (norm_nonneg _) (by positivity))
    _ = 3 * ‖X‖ := by ring
    _ < δ := by nlinarith [norm_nonneg X]

private theorem norm_tsmul_affine_lt_euclidean
    (X₁ X₂ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX₁_le : ‖X₁‖ ≤ ‖X‖) (hX₂_le : ‖X₂‖ ≤ ‖X‖)
    {δ : ℝ} (hsmall : ‖X‖ < δ / 7)
    {s : ℂ} (hs : ‖s‖ < 2) {t : ℂ} (ht : ‖t‖ < 2) :
    ‖t • (X₁ + s • X₂)‖ < δ :=
  calc
    ‖t • (X₁ + s • X₂)‖ ≤ ‖t‖ * ‖X₁ + s • X₂‖ := norm_smul_le _ _
    _ ≤ 2 * (3 * ‖X‖) := by
        apply mul_le_mul (le_of_lt ht)
        · calc
            ‖X₁ + s • X₂‖ ≤ ‖X₁‖ + ‖s • X₂‖ := norm_add_le _ _
            _ ≤ ‖X₁‖ + ‖s‖ * ‖X₂‖ := add_le_add (le_refl _) (norm_smul_le s X₂)
            _ ≤ ‖X‖ + 2 * ‖X‖ := add_le_add hX₁_le
                (mul_le_mul (le_of_lt hs) hX₂_le (norm_nonneg _) (by positivity))
            _ = 3 * ‖X‖ := by ring
        · positivity
        · positivity
    _ = 6 * ‖X‖ := by ring
    _ < δ := by nlinarith [norm_nonneg X]

theorem wickRePart_isInLieAlgebra_of_preimage_skew
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX : (wickRePreimage X).transpose + wickRePreimage X =
      (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)) :
    ComplexLorentzGroup.IsInLieAlgebra (wickRePart X) := by
  rw [wickRePart_eq_wick_conjugation_preimage]
  exact wick_rotated_isInLieAlgebra (wickRePreimage X) hX

private theorem smul_isInLieAlgebra
    (c : ℂ) {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    ComplexLorentzGroup.IsInLieAlgebra (c • X) := by
  unfold ComplexLorentzGroup.IsInLieAlgebra at hX ⊢
  simpa [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add]
    using congrArg (fun M => c • M) hX

theorem wickRePart_isInLieAlgebra
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    ComplexLorentzGroup.IsInLieAlgebra (wickRePart X) := by
  exact wickRePart_isInLieAlgebra_of_preimage_skew X (wickRePart_preimage_skew X hX)

theorem wickImPart_isInLieAlgebra
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    ComplexLorentzGroup.IsInLieAlgebra (wickRePart ((-Complex.I) • X)) := by
  exact wickRePart_isInLieAlgebra ((-Complex.I) • X) (smul_isInLieAlgebra (-Complex.I) hX)

theorem wick_decomposition
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (_hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    X = wickRePart X + Complex.I • (wickRePart ((-Complex.I) • X)) := by
  ext μ ν
  by_cases hμ : μ = (0 : Fin (d + 1))
  · by_cases hν : ν = (0 : Fin (d + 1))
    · subst hμ
      subst hν
      apply Complex.ext <;> simp [wickRePart]
    · subst hμ
      apply Complex.ext <;> simp [wickRePart, hν]
  · by_cases hν : ν = (0 : Fin (d + 1))
    · subst hν
      apply Complex.ext <;> simp [wickRePart, hμ]
    · apply Complex.ext <;> simp [wickRePart, hμ, hν]

theorem exists_wick_generator_decomposition
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    ∃ Y₁ Y₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      Y₁.transpose + Y₁ = 0 ∧
      Y₂.transpose + Y₂ = 0 ∧
      X = wickW * Y₁.map Complex.ofReal * wickWinv +
        Complex.I • (wickW * Y₂.map Complex.ofReal * wickWinv) := by
  refine ⟨wickRePreimage X, wickRePreimage ((-Complex.I) • X), ?_, ?_, ?_⟩
  · exact wickRePart_preimage_skew X hX
  · exact wickRePart_preimage_skew ((-Complex.I) • X) (smul_isInLieAlgebra (-Complex.I) hX)
  · calc
      X = wickRePart X + Complex.I • (wickRePart ((-Complex.I) • X)) :=
        wick_decomposition X hX
      _ = wickW * (wickRePreimage X).map Complex.ofReal * wickWinv +
          Complex.I • (wickW * (wickRePreimage ((-Complex.I) • X)).map Complex.ofReal * wickWinv) := by
            rw [wickRePart_eq_wick_conjugation_preimage,
              wickRePart_eq_wick_conjugation_preimage]

private theorem wick_conjugation_add_smul
    (Y₁ Y₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (s : ℝ) :
    wickW * (Y₁ + s • Y₂).map Complex.ofReal * wickWinv =
      wickW * Y₁.map Complex.ofReal * wickWinv +
        (s : ℂ) • (wickW * Y₂.map Complex.ofReal * wickWinv) := by
  have hmap :
      (Y₁ + s • Y₂).map Complex.ofReal =
        Y₁.map Complex.ofReal + (s : ℂ) • Y₂.map Complex.ofReal := by
    ext i j
    change ((Y₁ i j + s * Y₂ i j : ℝ) : ℂ) =
      (Y₁ i j : ℂ) + (s : ℂ) * (Y₂ i j : ℂ)
    push_cast
    ring
  rw [hmap, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

set_option maxHeartbeats 800000 in
/-- Distributional-input analogue of the Euclidean near-identity core step. -/
theorem near_identity_core_euclidean_distributional
    (n : ℕ) [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_dist :
      ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (hR : R.det = 1) (horth : R.transpose * R = 1)
        (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n |
            (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
              BHW.complexLorentzAction
                (ComplexLorentzGroup.ofEuclidean R hR horth)
                (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            F (BHW.complexLorentzAction
              (ComplexLorentzGroup.ofEuclidean R hR horth)
              (fun k => wickRotatePoint (x k))) * φ x =
          ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) * φ x)
    {z : Fin n → Fin (d + 1) → ℂ} (hz : z ∈ ForwardTube d n)
    {δ : ℝ} (_hδ_pos : 0 < δ)
    (hA_in_FT : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < δ →
        (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν) ∈
          ForwardTube d n)
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX_lie : ComplexLorentzGroup.IsInLieAlgebra X) (hX_small : ‖X‖ < δ / 7) :
    F (fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  set X₁ := wickRePart X with hX₁_def
  set X₂ := wickRePart ((-Complex.I) • X) with hX₂_def
  set Y₁ := wickRePreimage X with hY₁_def
  set Y₂ := wickRePreimage ((-Complex.I) • X) with hY₂_def
  have hX_decomp : X = X₁ + Complex.I • X₂ := by
    simpa [hX₁_def, hX₂_def] using wick_decomposition X hX_lie
  have hY₁_lie : Y₁.transpose + Y₁ = 0 := by
    simpa [hY₁_def] using wickRePart_preimage_skew X hX_lie
  have hY₂_lie : Y₂.transpose + Y₂ = 0 := by
    simpa [hY₂_def] using
      wickRePart_preimage_skew ((-Complex.I) • X) (smul_isInLieAlgebra (-Complex.I) hX_lie)
  have hX₁_eq : X₁ = wickW * Y₁.map Complex.ofReal * wickWinv := by
    simpa [hX₁_def, hY₁_def] using wickRePart_eq_wick_conjugation_preimage X
  have hX₂_eq : X₂ = wickW * Y₂.map Complex.ofReal * wickWinv := by
    simpa [hX₂_def, hY₂_def] using
      wickRePart_eq_wick_conjugation_preimage ((-Complex.I) • X)
  have hX₁_le : ‖X₁‖ ≤ ‖X‖ := by
    simpa [hX₁_def] using norm_wickRePart_le X
  have hX₂_le : ‖X₂‖ ≤ ‖X‖ := by
    simpa [hX₂_def] using norm_wickImPart_le X
  have hsmall : ‖X‖ < δ / 7 := hX_small
  have hreal_param : ∀ s : ℝ, X₁ + (s : ℂ) • X₂ =
      wickW * (Y₁ + s • Y₂).map Complex.ofReal * wickWinv := by
    intro s
    rw [hX₁_eq, hX₂_eq, wick_conjugation_add_smul]
  have hstep1 : ∀ s : ℝ, ‖(s : ℂ)‖ < 2 →
      F (fun k μ => ∑ ν, (exp (X₁ + (s : ℂ) • X₂) : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
    intro s hs
    have hgen_lie : (Y₁ + s • Y₂).transpose + (Y₁ + s • Y₂) = 0 := by
      calc
        (Y₁ + s • Y₂).transpose + (Y₁ + s • Y₂)
            = (Y₁.transpose + Y₁) + s • (Y₂.transpose + Y₂) := by
                simp [Matrix.transpose_add, Matrix.transpose_smul, smul_add,
                  add_assoc, add_left_comm, add_comm]
        _ = 0 := by rw [hY₁_lie, hY₂_lie, smul_zero, add_zero]
    have hball_sub : ∀ t ∈ Metric.ball (0 : ℂ) 2,
        (fun k (μ : Fin (d + 1)) =>
          ∑ ν, (exp (t • (wickW * (Y₁ + s • Y₂).map Complex.ofReal * wickWinv)) :
            Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n := by
      intro t ht
      apply hA_in_FT
      rw [← hreal_param s]
      exact norm_tsmul_affine_lt_euclidean X₁ X₂ X hX₁_le hX₂_le hsmall hs
        (by rwa [Metric.mem_ball, dist_zero_right] at ht)
    have h1_in_ball : (1 : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]
      norm_num
    have hfull :=
      Task2Bridge.full_domain_generator_invariance_euclidean_distributional
        (d := d) n F hF_holo hF_dist (Y₁ + s • Y₂) hgen_lie z hz
        Metric.isOpen_ball (convex_ball _ _).isPreconnected
        (Metric.mem_ball_self (by positivity : (0 : ℝ) < 2))
        hball_sub 1 h1_in_ball
    simp only [one_smul] at hfull
    rw [← hreal_param s] at hfull
    exact hfull
  have hball_FT : ∀ s ∈ Metric.ball (0 : ℂ) 2,
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (X₁ + s • X₂) : Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n := by
    intro s hs
    exact hA_in_FT _ (norm_affine_combination_lt_euclidean X₁ X₂ X hX₁_le hX₂_le hsmall
      (by rwa [Metric.mem_ball, dist_zero_right] at hs))
  set action_s : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun s k μ => ∑ ν, (exp (X₁ + s • X₂) : Matrix _ _ ℂ) μ ν * z k ν
  set g : ℂ → ℂ := fun s => F (action_s s) - F z
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 2) := by
    apply DifferentiableOn.sub
    · apply hF_holo.comp ?_ hball_FT
      have h_affine : Differentiable ℂ (fun s : ℂ => X₁ + s • X₂) :=
        (differentiable_const X₁).add (differentiable_id.smul_const X₂)
      have h_exp_comp : Differentiable ℂ (fun s : ℂ => exp (X₁ + s • X₂)) :=
        fun s => (NormedSpace.exp_analytic (X₁ + s • X₂)).differentiableAt.comp s (h_affine s)
      exact (differentiable_pi.mpr fun k => differentiable_pi.mpr fun μ =>
        Differentiable.fun_sum fun ν _ =>
          ((differentiable_apply ν).comp ((differentiable_apply μ).comp h_exp_comp)).mul
            (differentiable_const _)).differentiableOn
    · exact differentiableOn_const _
  have hg_analytic : AnalyticOnNhd ℂ g (Metric.ball 0 2) :=
    hg_diff.analyticOnNhd Metric.isOpen_ball
  have hg_real : ∀ s : ℝ, ‖(s : ℂ)‖ < 2 → g (s : ℂ) = 0 := by
    intro s hs
    simp only [g, sub_eq_zero]
    exact hstep1 s hs
  have hg_freq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), g s = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    set s := min (r / 2) 1 with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_norm : ‖(s : ℂ)‖ < 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
      linarith [min_le_right (r / 2) 1]
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]
      linarith [min_le_left (r / 2) 1])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_norm)
  have hg_zero := hg_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball _ _).isPreconnected (Metric.mem_ball_self (by positivity : (0 : ℝ) < 2)) hg_freq
  have hI_in_ball : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
    norm_num
  have hgI := hg_zero hI_in_ball
  simp only [g, Pi.zero_apply, sub_eq_zero] at hgI
  rw [hX_decomp]
  exact hgI

end Task3Bridge
end BHW
