import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.UnitInterval
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedMaxRankIdentity

/-!
# BHW near-identity invariance on open source charts

This file exposes the local Hall-Wightman/BHW identity theorem in the form
needed by source-chart continuation: a holomorphic branch on an arbitrary open
source domain which is invariant under the real restricted Lorentz group is
locally invariant under the proper complex Lorentz group.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

variable {d : ℕ}

/-- The one-parameter matrix-exponential action is complex differentiable. -/
private theorem bhw_differentiable_expAction
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Differentiable ℂ (fun t : ℂ =>
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν) :
      ℂ → Fin n → Fin (d + 1) → ℂ) := by
  have hexp : Differentiable ℂ
      (fun t : ℂ => (exp (t • X) : Matrix _ _ ℂ)) :=
    fun t => (hasDerivAt_exp_smul_const X t).differentiableAt
  apply differentiable_pi.mpr
  intro k
  apply differentiable_pi.mpr
  intro μ
  apply Differentiable.fun_sum
  intro ν _
  exact
    ((differentiable_apply ν).comp ((differentiable_apply μ).comp hexp)).mul
      (differentiable_const _)

/-- The real matrix exponential maps to the complex matrix exponential under
entrywise `Complex.ofReal`. -/
theorem exp_map_ofReal_bridge
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (s : ℝ) :
    (exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal =
      (exp ((s : ℂ) • Y.map Complex.ofReal) : Matrix _ _ ℂ) := by
  have hcont : Continuous (Complex.ofRealHom.mapMatrix :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  have h1 : Complex.ofRealHom.mapMatrix (exp (s • Y)) =
      exp (Complex.ofRealHom.mapMatrix (s • Y)) :=
    map_exp (f := Complex.ofRealHom.mapMatrix) hcont (s • Y)
  have h2 : Complex.ofRealHom.mapMatrix (s • Y) =
      (s : ℂ) • Y.map Complex.ofReal := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
  change Complex.ofRealHom.mapMatrix (exp (s • Y)) = _
  rw [h1, h2]

/-- Entrywise real part of a complex Lorentz Lie-algebra matrix. -/
def reMatrixCLie (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => (X i j).re

/-- Entrywise imaginary part of a complex Lorentz Lie-algebra matrix. -/
def imMatrixCLie (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => (X i j).im

/-- A complex matrix decomposes into real and imaginary parts. -/
theorem matrix_re_im_decomp_CLie
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    X =
      (reMatrixCLie X).map Complex.ofReal +
        Complex.I • (imMatrixCLie X).map Complex.ofReal := by
  ext i j
  simp only [reMatrixCLie, imMatrixCLie, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im (X i j)).symm

/-- The real part of a complex Lorentz Lie-algebra matrix lies in the real
Lorentz Lie algebra. -/
theorem reMatrixCLie_isInLorentzAlgebra
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    IsInLorentzAlgebra d (reMatrixCLie X) := by
  have hX' : X.transpose * Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) +
      Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) * X = 0 := hX
  unfold IsInLorentzAlgebra
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    LorentzLieGroup.minkowskiMatrix, Matrix.diagonal_apply, reMatrixCLie,
    Matrix.zero_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hij := congr_fun (congr_fun hX' i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.zero_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hij
  have hre := congr_arg Complex.re hij
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, zero_mul, Complex.zero_re] at hre
  exact hre

/-- The imaginary part of a complex Lorentz Lie-algebra matrix lies in the
real Lorentz Lie algebra. -/
theorem imMatrixCLie_isInLorentzAlgebra
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    IsInLorentzAlgebra d (imMatrixCLie X) := by
  have hX' : X.transpose * Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) +
      Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) * X = 0 := hX
  unfold IsInLorentzAlgebra
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    LorentzLieGroup.minkowskiMatrix, Matrix.diagonal_apply, imMatrixCLie,
    Matrix.zero_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hij := congr_fun (congr_fun hX' i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.zero_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hij
  have him := congr_arg Complex.im hij
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add,
    Complex.zero_im] at him
  exact him

/-- The mapped real part has operator norm bounded by the original complex
matrix. -/
theorem norm_reMatrixCLie_map_le
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖(reMatrixCLie X).map Complex.ofReal‖ ≤ ‖X‖ := by
  simp only [← coe_nnnorm, NNReal.coe_le_coe]
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  apply Finset.sup_le
  intro i _
  apply le_trans _ (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.map_apply, reMatrixCLie]
  rw [show (Complex.ofReal (X i j).re : ℂ) = ((X i j).re : ℂ) from rfl]
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Complex.norm_real]
  exact Complex.abs_re_le_norm (X i j)

/-- The mapped imaginary part has operator norm bounded by the original
complex matrix. -/
theorem norm_imMatrixCLie_map_le
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖(imMatrixCLie X).map Complex.ofReal‖ ≤ ‖X‖ := by
  simp only [← coe_nnnorm, NNReal.coe_le_coe]
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  apply Finset.sup_le
  intro i _
  apply le_trans _ (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.map_apply, imMatrixCLie]
  rw [show (Complex.ofReal (X i j).im : ℂ) = ((X i j).im : ℂ) from rfl]
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Complex.norm_real]
  exact Complex.abs_im_le_norm (X i j)

/-- Near `1`, every proper complex Lorentz element is an exponential of a
small complex Lorentz Lie-algebra element.  This is the public BHW-facing
form of the local exponential chart used in the standard BHW proof. -/
theorem complexLorentz_exp_nhd_of_one (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∃ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ,
        ComplexLorentzGroup.IsInLieAlgebra X ∧
          Λ.val = NormedSpace.exp X ∧ ‖X‖ < ε := by
  set E := Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  let mexp : E → E := NormedSpace.exp
  have hexp_strict : HasStrictFDerivAt mexp
      ((ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E)) (0 : E) := by
    show HasStrictFDerivAt NormedSpace.exp _ _
    convert hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := E) using 1
  set Φ := hexp_strict.toOpenPartialHomeomorph mexp
  have h0_mem : (0 : E) ∈ Φ.source :=
    hexp_strict.mem_toOpenPartialHomeomorph_source
  have hS_nhds : Φ.source ∈ 𝓝 (0 : E) :=
    Φ.open_source.mem_nhds h0_mem
  have hinj : Set.InjOn mexp Φ.source := Φ.injOn
  set η := ComplexLorentzGroup.ηℂ (d := d)
  have hneg_nhds : ∀ᶠ X in 𝓝 (0 : E), -X ∈ Φ.source :=
    continuous_neg.continuousAt.preimage_mem_nhds
      (by rw [neg_zero]; exact hS_nhds)
  have hconj_cont : Continuous (fun X : E => η * X.transpose * η) :=
    (continuous_const.mul (Continuous.matrix_transpose continuous_id)).mul
      continuous_const
  have hconj_nhds : ∀ᶠ X in 𝓝 (0 : E), η * X.transpose * η ∈ Φ.source :=
    hconj_cont.continuousAt.preimage_mem_nhds
      (by simp only [Matrix.transpose_zero, mul_zero, zero_mul]; exact hS_nhds)
  have hball : ∀ᶠ X in 𝓝 (0 : E), ‖X‖ < ε :=
    Metric.eventually_nhds_iff.mpr
      ⟨ε, hε, fun _ hx => by rwa [dist_zero_right] at hx⟩
  have hS_ev : ∀ᶠ X in 𝓝 (0 : E), X ∈ Φ.source := hS_nhds
  have h_good : ∀ᶠ X in 𝓝 (0 : E),
      X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε :=
    hS_ev.and (hneg_nhds.and (hconj_nhds.and hball))
  have hmap : map mexp (𝓝 0) = 𝓝 (1 : E) := by
    have hsurj : (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E).range = ⊤ := by
      ext x
      exact ⟨fun _ => trivial, fun _ => ⟨x, by simp⟩⟩
    have := hexp_strict.map_nhds_eq_of_surj hsurj
    rwa [show mexp 0 = (1 : E) from NormedSpace.exp_zero] at this
  have h_mat : ∀ᶠ M in 𝓝 (1 : E),
      ∃ X : E, mexp X = M ∧ X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε := by
    rw [← hmap, Filter.eventually_map]
    exact h_good.mono fun X ⟨hXS, hnXS, hcXS, hXε⟩ =>
      ⟨X, rfl, hXS, hnXS, hcXS, hXε⟩
  have h_grp : ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∃ X : E, mexp X = Λ.val ∧ X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε := by
    have hca : ContinuousAt (fun Λ : ComplexLorentzGroup d => Λ.val) 1 :=
      ComplexLorentzGroup.continuous_val.continuousAt
    rw [ContinuousAt, ComplexLorentzGroup.one_val'] at hca
    exact hca.eventually h_mat
  apply h_grp.mono
  intro Λ ⟨X, hexpX, hXS, hnXS, hcXS, hXε⟩
  refine ⟨X, ?_, hexpX.symm, hXε⟩
  have h1 : mexp (η * X.transpose * η) = η * mexp X.transpose * η := by
    show NormedSpace.exp (η * X.transpose * η) =
      η * NormedSpace.exp X.transpose * η
    exact NormedSpace.exp_units_conj (ComplexLorentzGroup.ηℂ_unit) X.transpose
  have h2 : mexp X.transpose = (mexp X).transpose :=
    show NormedSpace.exp X.transpose = (NormedSpace.exp X).transpose from
      Matrix.exp_transpose X
  have h3 : (Λ⁻¹).val = η * Λ.val.transpose * η := rfl
  have h5 : mexp (η * X.transpose * η) = (Λ⁻¹).val := by
    rw [h1, h2, h3, hexpX]
  have h6 : (Λ⁻¹).val = mexp (-X) := by
    have hinvmul : (Λ⁻¹).val * Λ.val = 1 := by
      have : (Λ⁻¹ * Λ).val = 1 := by rw [inv_mul_cancel]; rfl
      rwa [ComplexLorentzGroup.mul_val] at this
    have hexp_rinv : mexp X * mexp (-X) = 1 := by
      show NormedSpace.exp X * NormedSpace.exp (-X) = 1
      rw [← NormedSpace.exp_add_of_commute
        (Commute.neg_right (Commute.refl X))]
      simp [NormedSpace.exp_zero]
    calc
      (Λ⁻¹).val = (Λ⁻¹).val * (mexp X * mexp (-X)) := by
        rw [hexp_rinv, mul_one]
      _ = (Λ⁻¹).val * mexp X * mexp (-X) := by rw [mul_assoc]
      _ = (Λ⁻¹).val * Λ.val * mexp (-X) := by rw [hexpX]
      _ = mexp (-X) := by rw [hinvmul, one_mul]
  have h7 : mexp (η * X.transpose * η) = mexp (-X) := by rw [h5, h6]
  have h8 : η * X.transpose * η = -X := hinj hcXS hnXS h7
  show ComplexLorentzGroup.IsInLieAlgebra X
  unfold ComplexLorentzGroup.IsInLieAlgebra
  have h9 : X.transpose * η = -(η * X) := by
    calc
      X.transpose * η = 1 * X.transpose * η := by rw [Matrix.one_mul]
      _ = (η * η) * X.transpose * η := by
        rw [ComplexLorentzGroup.ηℂ_sq (d := d)]
      _ = η * (η * X.transpose * η) := by simp only [Matrix.mul_assoc]
      _ = η * (-X) := by rw [h8]
      _ = -(η * X) := Matrix.mul_neg η X
  rw [h9]
  exact neg_add_cancel _

/-- Full-domain one-generator identity theorem on an arbitrary open source
domain. -/
private theorem bhw_full_domain_generator_invariance_on_open
    (n : ℕ)
    (Ω : Set (Fin n → Fin (d + 1) → ℂ))
    (B : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (_hΩ_open : IsOpen Ω)
    (hB_holo : DifferentiableOn ℂ B Ω)
    (hB_realLorentz :
      ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω →
        complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω →
          B (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ Ω)
    {U : Set ℂ}
    (hU_open : IsOpen U)
    (hU_pre : IsPreconnected U)
    (h0U : (0 : ℂ) ∈ U)
    (hU_sub : ∀ t ∈ U,
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) ∈ Ω) :
    ∀ t ∈ U,
      B (fun k μ =>
        ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) =
        B z := by
  set X := Y.map Complex.ofReal with hX_def
  set action : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t k μ => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν with haction_def
  set g : ℂ → ℂ := fun t => B (action t) - B z with hg_def
  have hg_diff : DifferentiableOn ℂ g U := by
    apply DifferentiableOn.sub
    · exact hB_holo.comp (bhw_differentiable_expAction X z).differentiableOn
        (fun t ht => by simpa [hX_def, haction_def] using hU_sub t ht)
    · exact differentiableOn_const _
  have hg_analytic : AnalyticOnNhd ℂ g U :=
    hg_diff.analyticOnNhd hU_open
  have hg_real : ∀ s : ℝ, (s : ℂ) ∈ U → g (s : ℂ) = 0 := by
    intro s hs
    simp only [hg_def, sub_eq_zero]
    have hbridge := exp_map_ofReal_bridge (d := d) Y s
    have hentry : ∀ μ ν : Fin (d + 1),
        (exp ((s : ℂ) • X) : Matrix _ _ ℂ) μ ν =
        ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) := by
      intro μ ν
      simp only [hX_def, ← hbridge, Matrix.map_apply]
    have haction_eq : action (s : ℂ) =
        complexLorentzAction
          (ComplexLorentzGroup.ofReal
            (expLorentz d (s • Y) (isInLorentzAlgebra_smul d hY s))) z := by
      ext k μ
      simp only [haction_def, complexLorentzAction]
      congr 1
      ext ν
      rw [hentry]
      rfl
    rw [haction_eq]
    exact hB_realLorentz
      (expLorentz d (s • Y) (isInLorentzAlgebra_smul d hY s))
      z hz (by simpa [← haction_eq] using hU_sub (s : ℂ) hs)
  have hg_freq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    obtain ⟨r', hr'_pos, hr'_sub⟩ := Metric.isOpen_iff.mp hU_open 0 h0U
    set s := min (r / 2) (r' / 2) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]
      linarith [min_le_left (r / 2) (r' / 2)])
    have hs_in_U : (s : ℂ) ∈ U := hr'_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]
      linarith [min_le_right (r / 2) (r' / 2)])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_in_U)
  have hg_zero := hg_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hU_pre h0U hg_freq
  intro t ht
  have := hg_zero ht
  simp only [hg_def, Pi.zero_apply, sub_eq_zero] at this
  simpa [hX_def, haction_def] using this

set_option maxHeartbeats 400000 in
private theorem bhw_norm_affine_combination_lt
    (X₁ X₂ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX₁_le : ‖X₁‖ ≤ ‖X‖)
    (hX₂_le : ‖X₂‖ ≤ ‖X‖)
    {δ : ℝ}
    (hsmall : ‖X‖ < δ / 7)
    {s : ℂ}
    (hs : ‖s‖ < 2) :
    ‖X₁ + s • X₂‖ < δ :=
  calc
    ‖X₁ + s • X₂‖ ≤ ‖X₁‖ + ‖s • X₂‖ := norm_add_le _ _
    _ ≤ ‖X₁‖ + ‖s‖ * ‖X₂‖ :=
      add_le_add (le_refl _) (norm_smul_le s X₂)
    _ ≤ ‖X‖ + 2 * ‖X‖ :=
      add_le_add hX₁_le
        (mul_le_mul (le_of_lt hs) hX₂_le (norm_nonneg _) (by positivity))
    _ = 3 * ‖X‖ := by ring
    _ < δ := by nlinarith [norm_nonneg X]

set_option maxHeartbeats 400000 in
private theorem bhw_norm_tsmul_affine_lt
    (X₁ X₂ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX₁_le : ‖X₁‖ ≤ ‖X‖)
    (hX₂_le : ‖X₂‖ ≤ ‖X‖)
    {δ : ℝ}
    (hsmall : ‖X‖ < δ / 7)
    {s : ℂ}
    (hs : ‖s‖ < 2)
    {t : ℂ}
    (ht : ‖t‖ < 2) :
    ‖t • (X₁ + s • X₂)‖ < δ :=
  calc
    ‖t • (X₁ + s • X₂)‖ ≤ ‖t‖ * ‖X₁ + s • X₂‖ := norm_smul_le _ _
    _ ≤ 2 * (3 * ‖X‖) := by
      apply mul_le_mul (le_of_lt ht)
      · calc
          ‖X₁ + s • X₂‖ ≤ ‖X₁‖ + ‖s • X₂‖ := norm_add_le _ _
          _ ≤ ‖X₁‖ + ‖s‖ * ‖X₂‖ :=
            add_le_add (le_refl _) (norm_smul_le s X₂)
          _ ≤ ‖X‖ + 2 * ‖X‖ :=
            add_le_add hX₁_le
              (mul_le_mul (le_of_lt hs) hX₂_le (norm_nonneg _) (by positivity))
          _ = 3 * ‖X‖ := by ring
      · positivity
      · positivity
    _ = 6 * ‖X‖ := by ring
    _ < δ := by nlinarith [norm_nonneg X]

set_option maxHeartbeats 800000 in
private theorem bhw_near_identity_core_on_open
    (n : ℕ)
    (Ω : Set (Fin n → Fin (d + 1) → ℂ))
    (B : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hΩ_open : IsOpen Ω)
    (hB_holo : DifferentiableOn ℂ B Ω)
    (hB_realLorentz :
      ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω →
        complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω →
          B (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ Ω)
    {δ : ℝ}
    (_hδ_pos : 0 < δ)
    (hA_in_Ω : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < δ →
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν) ∈ Ω)
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX_lie : ComplexLorentzGroup.IsInLieAlgebra X)
    (hX_small : ‖X‖ < δ / 7) :
    B (fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * z k ν) = B z := by
  set Y₁ := reMatrixCLie X
  set Y₂ := imMatrixCLie X
  set X₁ := Y₁.map Complex.ofReal with hX₁_def
  set X₂ := Y₂.map Complex.ofReal with hX₂_def
  have hY₁_lie := reMatrixCLie_isInLorentzAlgebra (d := d) hX_lie
  have hY₂_lie := imMatrixCLie_isInLorentzAlgebra (d := d) hX_lie
  have hX_decomp : X = X₁ + Complex.I • X₂ := matrix_re_im_decomp_CLie X
  have hX₁_le : ‖X₁‖ ≤ ‖X‖ := norm_reMatrixCLie_map_le X
  have hX₂_le : ‖X₂‖ ≤ ‖X‖ := norm_imMatrixCLie_map_le X
  have hsmall : ‖X‖ < δ / 7 := hX_small
  have hball_Ω : ∀ s ∈ Metric.ball (0 : ℂ) 2,
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (X₁ + s • X₂) : Matrix _ _ ℂ) μ ν * z k ν) ∈ Ω := by
    intro s hs
    exact hA_in_Ω _
      (bhw_norm_affine_combination_lt X₁ X₂ X hX₁_le hX₂_le hsmall
        (by rwa [Metric.mem_ball, dist_zero_right] at hs))
  have hreal_param :
      ∀ s : ℝ, X₁ + (s : ℂ) • X₂ = (Y₁ + s • Y₂).map Complex.ofReal := by
    intro s
    ext i j
    simp only [hX₁_def, hX₂_def, Matrix.add_apply, Matrix.map_apply,
      Matrix.smul_apply, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
  have hstep1 : ∀ s : ℝ, ‖(s : ℂ)‖ < 2 →
      B (fun k μ =>
        ∑ ν, (exp (X₁ + (s : ℂ) • X₂) : Matrix _ _ ℂ) μ ν * z k ν) = B z := by
    intro s hs
    rw [hreal_param s]
    have hgen_lie : IsInLorentzAlgebra d (Y₁ + s • Y₂) := by
      unfold IsInLorentzAlgebra at hY₁_lie hY₂_lie ⊢
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul,
        Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul]
      rw [add_add_add_comm, ← smul_add, hY₁_lie, hY₂_lie, smul_zero, add_zero]
    have hball_sub : ∀ t ∈ Metric.ball (0 : ℂ) 2,
        (fun k (μ : Fin (d + 1)) =>
          ∑ ν,
            (exp (t • (Y₁ + s • Y₂).map Complex.ofReal) :
              Matrix _ _ ℂ) μ ν * z k ν) ∈ Ω := by
      intro t ht
      apply hA_in_Ω
      have h_eq : (Y₁ + s • Y₂).map Complex.ofReal =
          X₁ + (s : ℂ) • X₂ :=
        (hreal_param s).symm
      rw [h_eq]
      exact bhw_norm_tsmul_affine_lt X₁ X₂ X hX₁_le hX₂_le hsmall hs
        (by rwa [Metric.mem_ball, dist_zero_right] at ht)
    have h1_in_ball : (1 : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]
      norm_num
    have := bhw_full_domain_generator_invariance_on_open
      (d := d) n Ω B hΩ_open hB_holo hB_realLorentz
      (Y₁ + s • Y₂) hgen_lie z hz Metric.isOpen_ball
      (convex_ball _ _).isPreconnected
      (Metric.mem_ball_self (by positivity : (0 : ℝ) < 2))
      hball_sub 1 h1_in_ball
    simp only [one_smul] at this
    exact this
  set action_s : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun s k μ => ∑ ν, (exp (X₁ + s • X₂) : Matrix _ _ ℂ) μ ν * z k ν
      with haction_s_def
  set g : ℂ → ℂ := fun s => B (action_s s) - B z with hg_def
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 2) := by
    apply DifferentiableOn.sub
    · apply hB_holo.comp _ hball_Ω
      have h_affine : Differentiable ℂ (fun s : ℂ => X₁ + s • X₂) :=
        (differentiable_const X₁).add (differentiable_id.smul_const X₂)
      have h_exp_comp : Differentiable ℂ (fun s : ℂ => exp (X₁ + s • X₂)) :=
        fun s =>
          (NormedSpace.exp_analytic (X₁ + s • X₂)).differentiableAt.comp
            s (h_affine s)
      exact
        (differentiable_pi.mpr fun k =>
          differentiable_pi.mpr fun μ =>
            Differentiable.fun_sum fun ν _ =>
              ((differentiable_apply ν).comp
                  ((differentiable_apply μ).comp h_exp_comp)).mul
                (differentiable_const _)).differentiableOn
    · exact differentiableOn_const _
  have hg_analytic : AnalyticOnNhd ℂ g (Metric.ball 0 2) :=
    hg_diff.analyticOnNhd Metric.isOpen_ball
  have hg_real : ∀ s : ℝ, ‖(s : ℂ)‖ < 2 → g (s : ℂ) = 0 := by
    intro s hs
    simp only [hg_def, sub_eq_zero]
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
    (convex_ball _ _).isPreconnected
    (Metric.mem_ball_self (by positivity : (0 : ℝ) < 2)) hg_freq
  have hI_in_ball : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
    norm_num
  have hgI := hg_zero hI_in_ball
  simp only [hg_def, Pi.zero_apply, sub_eq_zero] at hgI
  rw [hX_decomp]
  exact hgI

/-- BHW near-identity theorem on an arbitrary open source chart.  This is the
local input used to continue a previously constructed branch: the starting
branch need only be real-Lorentz invariant on its current open carrier, and
then it is invariant under sufficiently small proper complex Lorentz
transformations as long as the transformed point remains in the carrier. -/
theorem bhw_near_identity_invariance_on_open
    (n : ℕ)
    (Ω : Set (Fin n → Fin (d + 1) → ℂ))
    (B : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hΩ_open : IsOpen Ω)
    (hB_holo : DifferentiableOn ℂ B Ω)
    (hB_realLorentz :
      ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω →
        complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω →
          B (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ Ω) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      complexLorentzAction Λ z ∈ Ω →
        B (complexLorentzAction Λ z) = B z := by
  have hexp_action_cont : Continuous
      (fun A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        (fun k (μ : Fin (d + 1)) =>
          ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    apply continuous_finset_sum
    intro ν _
    refine Continuous.mul ?_ continuous_const
    exact
      (continuous_apply ν).comp
        ((continuous_apply μ).comp NormedSpace.exp_continuous)
  have h0_in_Ω :
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) μ ν *
          z k ν) ∈ Ω := by
    convert hz using 2
    ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ]
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp (hΩ_open.preimage hexp_action_cont) 0 h0_in_Ω
  have hA_in_Ω : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < δ →
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν) ∈ Ω :=
    fun A hA => hδ_sub (by rwa [Metric.mem_ball, dist_zero_right])
  apply (complexLorentz_exp_nhd_of_one (d := d) (δ / 7) (by positivity)).mono
  intro Λ ⟨X, hX_lie, hΛ_eq, hX_small⟩ hΛz
  have haction_eq : complexLorentzAction Λ z =
      fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * z k ν := by
    ext k μ
    simp only [complexLorentzAction, complexLorentzVectorAction]
    apply Finset.sum_congr rfl
    intro ν _
    rw [← hΛ_eq]
  rw [haction_eq]
  exact bhw_near_identity_core_on_open
    (d := d) n Ω B hΩ_open hB_holo hB_realLorentz hz hδ_pos
    hA_in_Ω hX_lie hX_small

/-- Open-neighborhood form of the BHW near-identity theorem. -/
theorem bhw_local_complexLorentz_invariance_of_real_invariance
    (n : ℕ)
    (Ω : Set (Fin n → Fin (d + 1) → ℂ))
    (B : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hΩ_open : IsOpen Ω)
    (hB_holo : DifferentiableOn ℂ B Ω)
    (hB_realLorentz :
      ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω →
        complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω →
          B (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ Ω) :
    ∃ C : Set (ComplexLorentzGroup d),
      IsOpen C ∧ (1 : ComplexLorentzGroup d) ∈ C ∧
        ∀ Λ, Λ ∈ C →
          complexLorentzAction Λ z ∈ Ω →
            B (complexLorentzAction Λ z) = B z := by
  have hev :=
    bhw_near_identity_invariance_on_open
      (d := d) n Ω B hΩ_open hB_holo hB_realLorentz z hz
  rcases mem_nhds_iff.mp hev with ⟨C, hC_sub, hC_open, h1C⟩
  exact ⟨C, hC_open, h1C, fun Λ hΛ hΛz => hC_sub hΛ hΛz⟩

/-- A function which is eventually equal to its value near every point is
locally constant. -/
private theorem isLocallyConstant_of_eventually_eq_nhds
    {X Y : Type*} [TopologicalSpace X] {f : X → Y}
    (h : ∀ x, ∀ᶠ y in 𝓝 x, f y = f x) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  intro x
  rw [isOpen_iff_mem_nhds]
  intro y hy
  change f y = f x at hy
  filter_upwards [h y] with z hz
  change f z = f x
  exact hz.trans hy

/-- A BHW branch satisfying the local real-Lorentz invariance hypothesis is
constant along any proper-complex Lorentz path whose source orbit remains in
the open carrier. -/
theorem bhw_branch_constant_along_complexLorentz_path
    (n : ℕ)
    (Ω : Set (Fin n → Fin (d + 1) → ℂ))
    (B : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hΩ_open : IsOpen Ω)
    (hB_holo : DifferentiableOn ℂ B Ω)
    (hB_realLorentz :
      ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω →
        complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω →
          B (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
    {Λ0 Λ1 : ComplexLorentzGroup d}
    (γ : Path Λ0 Λ1)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hγΩ : ∀ t : unitInterval, complexLorentzAction (γ t) z ∈ Ω) :
    B (complexLorentzAction Λ1 z) =
      B (complexLorentzAction Λ0 z) := by
  let f : unitInterval → ℂ :=
    fun t => B (complexLorentzAction (γ t) z)
  have hf_eventually : ∀ t0 : unitInterval, ∀ᶠ t in 𝓝 t0, f t = f t0 := by
    intro t0
    let z0 : Fin n → Fin (d + 1) → ℂ := complexLorentzAction (γ t0) z
    have hz0 : z0 ∈ Ω := hγΩ t0
    rcases bhw_local_complexLorentz_invariance_of_real_invariance
        (d := d) n Ω B hΩ_open hB_holo hB_realLorentz z0 hz0 with
      ⟨C, hC_open, h1C, hC_inv⟩
    have hdelta_cont : Continuous
        (fun t : unitInterval => γ t * (γ t0)⁻¹) :=
      γ.continuous.mul continuous_const
    have hdelta_pre :
        {t : unitInterval | γ t * (γ t0)⁻¹ ∈ C} ∈ 𝓝 t0 := by
      have hC_nhds : C ∈ 𝓝 (γ t0 * (γ t0)⁻¹) := by
        simpa using hC_open.mem_nhds h1C
      exact hdelta_cont.continuousAt.preimage_mem_nhds hC_nhds
    filter_upwards [hdelta_pre] with t ht
    have hact :
        complexLorentzAction (γ t * (γ t0)⁻¹)
            (complexLorentzAction (γ t0) z) =
          complexLorentzAction (γ t) z := by
      rw [← complexLorentzAction_mul]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hmem :
        complexLorentzAction (γ t * (γ t0)⁻¹) z0 ∈ Ω := by
      simpa [z0, hact] using hγΩ t
    have heq := hC_inv (γ t * (γ t0)⁻¹) ht hmem
    simpa [f, z0, hact] using heq
  have hf_loc : IsLocallyConstant f :=
    isLocallyConstant_of_eventually_eq_nhds hf_eventually
  have hconst :
      f (1 : unitInterval) = f (0 : unitInterval) :=
    IsLocallyConstant.apply_eq_of_isPreconnected
      hf_loc (PreconnectedSpace.isPreconnected_univ)
      (x := (1 : unitInterval)) (y := (0 : unitInterval))
      (by trivial) (by trivial)
  simpa [f, γ.source, γ.target] using hconst

namespace BHWJostLocalOrientedContinuationChart

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}

/-- Stored oriented local branches are constant along proper-complex Lorentz
paths as long as the whole source orbit remains in the chart carrier. -/
theorem branch_constant_along_complexLorentz_path
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    {Λ0 Λ1 : ComplexLorentzGroup d}
    (γ : Path Λ0 Λ1)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hγC : ∀ t : unitInterval, complexLorentzAction (γ t) z ∈ C.carrier) :
    C.branch (complexLorentzAction Λ1 z) =
      C.branch (complexLorentzAction Λ0 z) := by
  exact
    bhw_branch_constant_along_complexLorentz_path
      (d := d) n C.carrier C.branch C.carrier_open C.branch_holo
      (by
        intro R y hy hRy
        exact C.branch_complexLorentzInvariant
          (ComplexLorentzGroup.ofReal R) y hy hRy)
      γ z hγC

end BHWJostLocalOrientedContinuationChart

private theorem fin_chain_eq_zero_of_adjacent
    {α : Type*} {m : ℕ} {f : Fin (m + 1) → α}
    (h : ∀ j : Fin m, f j.castSucc = f j.succ) :
    f (Fin.last m) = f 0 := by
  by_cases hm : m = 0
  · subst hm
    rfl
  · have hLift :
        Relator.LiftFun (fun x y : Fin (m + 1) => x < y) Eq f f := by
      exact (Fin.liftFun_iff_succ (r := Eq) (f := f)).2 h
    have hlt : (0 : Fin (m + 1)) < Fin.last m := by
      rw [Fin.lt_def]
      exact Nat.pos_of_ne_zero hm
    exact (hLift hlt).symm

namespace BHWJostOrientedSourcePatchContinuationChain

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 z : Fin n → Fin (d + 1) → ℂ}

/-- If a single oriented source point lies in every transition oriented patch
of a finite chain, the stored oriented germs telescope from the terminal chart
back to the initial chart. -/
theorem terminal_Psi_eq_initial_Psi_of_mem_all_orientedTransitions
    (C : BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z)
    {G : SourceOrientedGramData d n}
    (hGtrans :
      ∀ j : Fin C.m, G ∈ (C.oriented_transition j).orientedPatch) :
    (C.localChart (Fin.last C.m)).Psi G = (C.localChart 0).Psi G := by
  let f : Fin (C.m + 1) → ℂ := fun j => (C.localChart j).Psi G
  have hadj : ∀ j : Fin C.m, f j.castSucc = f j.succ := by
    intro j
    exact (C.oriented_transition j).oriented_psi_agree (hGtrans j)
  exact fin_chain_eq_zero_of_adjacent (f := f) hadj

end BHWJostOrientedSourcePatchContinuationChain

/-- Generic max-rank seed propagation inside a connected intermediate
oriented domain.  If two oriented germ-holomorphic functions agree on a
nonempty relatively open max-rank seed in `D`, then they agree on a new
nonempty preconnected relatively open max-rank seed inside any nonempty
relatively open target patch `W ⊆ D`. -/
theorem exists_maxRankSeed_eqOn_of_connected_domain
    (hn : d + 1 ≤ n)
    {Φ Ψ : SourceOrientedGramData d n → ℂ}
    {D seed W : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    (hDmax_conn :
      IsConnected (D ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ D)
    (hΨ : SourceOrientedVarietyGermHolomorphicOn d n Ψ D)
    (hseed_rel : IsRelOpenInSourceOrientedGramVariety d n seed)
    (hseed_nonempty : seed.Nonempty)
    (hseed_sub_D : seed ⊆ D)
    (hseed_sub_max : seed ⊆ {G | SourceOrientedMaxRankAt d n G})
    (hseed_eq : Set.EqOn Φ Ψ seed)
    (hW_rel : IsRelOpenInSourceOrientedGramVariety d n W)
    (hW_nonempty : W.Nonempty)
    (hW_sub_D : W ⊆ D) :
    ∃ seedNext : Set (SourceOrientedGramData d n),
      IsRelOpenInSourceOrientedGramVariety d n seedNext ∧
      IsPreconnected seedNext ∧
      seedNext.Nonempty ∧
      seedNext ⊆ W ∩ {G | SourceOrientedMaxRankAt d n G} ∧
      Set.EqOn Φ Ψ seedNext := by
  let Wmax : Set (SourceOrientedGramData d n) :=
    W ∩ {G | SourceOrientedMaxRankAt d n G}
  have hWmax_rel : IsRelOpenInSourceOrientedGramVariety d n Wmax :=
    sourceOrientedRelOpen_inter_maxRank_relOpen
      (d := d) (n := n) hn hW_rel
  have hWmax_nonempty : Wmax.Nonempty :=
    sourceOrientedRelOpen_inter_maxRank_nonempty
      (d := d) (n := n) hn hW_rel hW_nonempty
  have hΦΨ_Dmax :
      Set.EqOn Φ Ψ (D ∩ {G | SourceOrientedMaxRankAt d n G}) :=
    sourceOrientedGramVariety_maxRank_eqOn_of_connected_fullFrame
      (d := d) (n := n) hn hD_rel hDmax_conn hseed_rel
      hseed_nonempty hseed_sub_D hseed_sub_max hΦ hΨ hseed_eq
  rcases hWmax_nonempty with ⟨G0, hG0Wmax⟩
  have hG0var : G0 ∈ sourceOrientedGramVariety d n :=
    IsRelOpenInSourceOrientedGramVariety.subset hW_rel hG0Wmax.1
  rcases sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame
      (d := d) (n := n) hn hG0var hG0Wmax.2 with
    ⟨_m, C⟩
  rcases C.connectedMaxRankPatch_inside_relOpen hWmax_rel hG0Wmax with
    ⟨P, hP_sub⟩
  refine ⟨P.V, P.V_relOpen, P.V_connected.isPreconnected,
    ⟨G0, P.center_mem⟩, ?_, ?_⟩
  · intro G hG
    exact (hP_sub hG).1
  · intro G hG
    have hGWmax : G ∈ Wmax := (hP_sub hG).1
    exact hΦΨ_Dmax ⟨hW_sub_D hGWmax.1, hGWmax.2⟩

namespace BHWJostOrientedTransitionData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {Cleft Cright : BHWJostLocalOrientedContinuationChart hd n τ U}
variable {p q : Fin n → Fin (d + 1) → ℂ}

/-- One propagated-seed step across an oriented transition.  If an accumulated
oriented germ `Φ` agrees with the left chart germ on a nonempty max-rank seed,
then the hard-range identity principle propagates that equality over the
connected max-rank part of an intermediate domain `D`.  Combining this with
the stored transition equality `Cleft.Psi = Cright.Psi` gives equality with
the right chart on the max-rank part of the transition patch. -/
theorem propagate_eqOn_to_right_maxRank
    (hn : d + 1 ≤ n)
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q)
    {Φ : SourceOrientedGramData d n → ℂ}
    {D seed : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    (hDmax_conn :
      IsConnected (D ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hD_sub_left : D ⊆ Cleft.orientedDomain)
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ D)
    (hseed_rel : IsRelOpenInSourceOrientedGramVariety d n seed)
    (hseed_nonempty : seed.Nonempty)
    (hseed_sub_D : seed ⊆ D)
    (hseed_sub_max : seed ⊆ {G | SourceOrientedMaxRankAt d n G})
    (hseed_eq : Set.EqOn Φ Cleft.Psi seed)
    (hT_sub_D : T.orientedPatch ⊆ D) :
    Set.EqOn Φ Cright.Psi
      (T.orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}) := by
  have hleft_holo :
      SourceOrientedVarietyGermHolomorphicOn d n Cleft.Psi D :=
    SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n) Cleft.Psi_holo hD_rel hD_sub_left
  have hΦ_left :
      Set.EqOn Φ Cleft.Psi
        (D ∩ {G | SourceOrientedMaxRankAt d n G}) :=
    sourceOrientedGramVariety_maxRank_eqOn_of_connected_fullFrame
      (d := d) (n := n) hn hD_rel hDmax_conn hseed_rel
      hseed_nonempty hseed_sub_D hseed_sub_max hΦ hleft_holo hseed_eq
  intro G hG
  have hGDmax : G ∈ D ∩ {G | SourceOrientedMaxRankAt d n G} :=
    ⟨hT_sub_D hG.1, hG.2⟩
  exact (hΦ_left hGDmax).trans (T.oriented_psi_agree hG.1)

/-- Seed-producing form of `propagate_eqOn_to_right_maxRank`.  After equality
has been propagated to the max-rank part of the next transition patch, choose
a max-rank point there and shrink a finite-coordinate max-rank chart to obtain
a nonempty preconnected relatively open seed on which the propagated equality
holds. -/
theorem exists_propagatedSeed_to_right
    (hn : d + 1 ≤ n)
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q)
    {Φ : SourceOrientedGramData d n → ℂ}
    {D seed : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    (hDmax_conn :
      IsConnected (D ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hD_sub_left : D ⊆ Cleft.orientedDomain)
    (hΦ : SourceOrientedVarietyGermHolomorphicOn d n Φ D)
    (hseed_rel : IsRelOpenInSourceOrientedGramVariety d n seed)
    (hseed_nonempty : seed.Nonempty)
    (hseed_sub_D : seed ⊆ D)
    (hseed_sub_max : seed ⊆ {G | SourceOrientedMaxRankAt d n G})
    (hseed_eq : Set.EqOn Φ Cleft.Psi seed)
    (hT_sub_D : T.orientedPatch ⊆ D) :
    ∃ seedNext : Set (SourceOrientedGramData d n),
      IsRelOpenInSourceOrientedGramVariety d n seedNext ∧
      IsPreconnected seedNext ∧
      seedNext.Nonempty ∧
      seedNext ⊆ T.orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G} ∧
      Set.EqOn Φ Cright.Psi seedNext := by
  let W : Set (SourceOrientedGramData d n) :=
    T.orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}
  have hW_rel : IsRelOpenInSourceOrientedGramVariety d n W :=
    sourceOrientedRelOpen_inter_maxRank_relOpen
      (d := d) (n := n) hn T.orientedPatch_relOpen
  have hW_nonempty : W.Nonempty :=
    sourceOrientedRelOpen_inter_maxRank_nonempty
      (d := d) (n := n) hn T.orientedPatch_relOpen
      T.orientedPatch_nonempty
  rcases hW_nonempty with ⟨G0, hG0W⟩
  have hG0var : G0 ∈ sourceOrientedGramVariety d n :=
    IsRelOpenInSourceOrientedGramVariety.subset
      T.orientedPatch_relOpen hG0W.1
  rcases sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame
      (d := d) (n := n) hn hG0var hG0W.2 with
    ⟨_m, C⟩
  rcases C.connectedMaxRankPatch_inside_relOpen hW_rel hG0W with
    ⟨P, hP_sub⟩
  have hprop :
      Set.EqOn Φ Cright.Psi
        (T.orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}) :=
    T.propagate_eqOn_to_right_maxRank
      (d := d) (n := n) hn hD_rel hDmax_conn hD_sub_left hΦ
      hseed_rel hseed_nonempty hseed_sub_D hseed_sub_max hseed_eq hT_sub_D
  refine ⟨P.V, P.V_relOpen, P.V_connected.isPreconnected,
    ⟨G0, P.center_mem⟩, ?_, ?_⟩
  · intro G hG
    exact (hP_sub hG).1
  · intro G hG
    exact hprop ((hP_sub hG).1)

end BHWJostOrientedTransitionData

namespace BHWJostOrientedMaxRankClosedLoopSeed

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}
variable {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}

/-- Package a source-realized max-rank closed-loop equality into the oriented
closed-loop seed consumed by the identity-principle layer.  This is the
bridge used after the genuine BHW/Jost finite-overlap argument has produced
terminal/initial branch equality on source representatives of a nonempty
oriented max-rank seed. -/
def of_sourceRealized_branch_eq
    {seed : Set (SourceOrientedGramData d n)}
    (hseed_rel : IsRelOpenInSourceOrientedGramVariety d n seed)
    (hseed_pre : IsPreconnected seed)
    (hseed_nonempty : seed.Nonempty)
    (hseed_sub :
      seed ⊆ L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G})
    (hsource_eq :
      ∀ G, G ∈ seed →
        ∃ y0 yF,
          y0 ∈ (L.chain.localChart 0).carrier ∧
          yF ∈ (L.chain.localChart (Fin.last L.chain.m)).carrier ∧
          sourceOrientedMinkowskiInvariant d n y0 = G ∧
          sourceOrientedMinkowskiInvariant d n yF = G ∧
          (L.chain.localChart (Fin.last L.chain.m)).branch yF =
            (L.chain.localChart 0).branch y0) :
    BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L where
  seed := seed
  seed_relOpen := hseed_rel
  seed_preconnected := hseed_pre
  seed_nonempty := hseed_nonempty
  seed_sub := hseed_sub
  seed_eq := by
    intro G hG
    rcases hsource_eq G hG with
      ⟨y0, yF, hy0, hyF, hy0G, hyFG, hbranch⟩
    have hfinal :
        (L.chain.localChart (Fin.last L.chain.m)).branch yF =
          (L.chain.localChart (Fin.last L.chain.m)).Psi G := by
      rw [(L.chain.localChart (Fin.last L.chain.m)).branch_eq_orientedPullback
        yF hyF, hyFG]
    have hstart :
        (L.chain.localChart 0).branch y0 =
          (L.chain.localChart 0).Psi G := by
      rw [(L.chain.localChart 0).branch_eq_orientedPullback y0 hy0, hy0G]
    calc
      (L.chain.localChart (Fin.last L.chain.m)).Psi G =
          (L.chain.localChart (Fin.last L.chain.m)).branch yF := hfinal.symm
      _ = (L.chain.localChart 0).branch y0 := hbranch
      _ = (L.chain.localChart 0).Psi G := hstart

/-- A common relatively open max-rank seed carried by every oriented
transition patch of a finite closed chain packages directly into the closed
loop seed.  This is the telescope form of the finite-overlap handoff: the
remaining BHW/Jost work is to produce such a seed from the actual overlap
construction. -/
def of_commonTransitionSeed
    {seed : Set (SourceOrientedGramData d n)}
    (hseed_rel : IsRelOpenInSourceOrientedGramVariety d n seed)
    (hseed_pre : IsPreconnected seed)
    (hseed_nonempty : seed.Nonempty)
    (hseed_closing : seed ⊆ L.closing_orientedPatch)
    (hseed_max : seed ⊆ {G | SourceOrientedMaxRankAt d n G})
    (hseed_trans :
      ∀ j : Fin L.chain.m,
        seed ⊆ (L.chain.oriented_transition j).orientedPatch) :
    BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L where
  seed := seed
  seed_relOpen := hseed_rel
  seed_preconnected := hseed_pre
  seed_nonempty := hseed_nonempty
  seed_sub := by
    intro G hG
    exact ⟨hseed_closing hG, hseed_max hG⟩
  seed_eq := by
    intro G hG
    exact
      BHWJostOrientedSourcePatchContinuationChain.terminal_Psi_eq_initial_Psi_of_mem_all_orientedTransitions
        L.chain (fun j => hseed_trans j hG)

/-- Closing-domain packaging for the propagated-seed route.  If terminal and
initial oriented germs agree on a max-rank seed inside a connected
intermediate domain `D`, and the closing oriented patch lies in the same
domain, then the generic seed-propagation theorem produces the exact
closed-loop seed required by the identity-principle layer. -/
theorem exists_of_connectedDomainPropagation
    (hn : d + 1 ≤ n)
    {D seed : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    (hDmax_conn :
      IsConnected (D ∩ {G | SourceOrientedMaxRankAt d n G}))
    (hD_sub_final :
      D ⊆ (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
    (hD_sub_start : D ⊆ (L.chain.localChart 0).orientedDomain)
    (hseed_rel : IsRelOpenInSourceOrientedGramVariety d n seed)
    (hseed_nonempty : seed.Nonempty)
    (hseed_sub_D : seed ⊆ D)
    (hseed_sub_max : seed ⊆ {G | SourceOrientedMaxRankAt d n G})
    (hseed_eq :
      Set.EqOn
        (L.chain.localChart (Fin.last L.chain.m)).Psi
        (L.chain.localChart 0).Psi
        seed)
    (hclosing_sub_D : L.closing_orientedPatch ⊆ D) :
    Nonempty (BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) := by
  have hFinal :
      SourceOrientedVarietyGermHolomorphicOn d n
        (L.chain.localChart (Fin.last L.chain.m)).Psi D :=
    SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n)
      (L.chain.localChart (Fin.last L.chain.m)).Psi_holo
      hD_rel hD_sub_final
  have hStart :
      SourceOrientedVarietyGermHolomorphicOn d n
        (L.chain.localChart 0).Psi D :=
    SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen
      (d := d) (n := n)
      (L.chain.localChart 0).Psi_holo hD_rel hD_sub_start
  rcases exists_maxRankSeed_eqOn_of_connected_domain
      (d := d) (n := n) hn hD_rel hDmax_conn hFinal hStart
      hseed_rel hseed_nonempty hseed_sub_D hseed_sub_max hseed_eq
      L.closing_orientedPatch_relOpen L.closing_orientedPatch_nonempty
      hclosing_sub_D with
    ⟨seedClosing, hseedClosing_rel, hseedClosing_pre,
      hseedClosing_nonempty, hseedClosing_sub, hseedClosing_eq⟩
  refine ⟨?S⟩
  exact
    { seed := seedClosing
      seed_relOpen := hseedClosing_rel
      seed_preconnected := hseedClosing_pre
      seed_nonempty := hseedClosing_nonempty
      seed_sub := by
        intro G hG
        exact hseedClosing_sub hG
      seed_eq := hseedClosing_eq }

end BHWJostOrientedMaxRankClosedLoopSeed

end BHW
