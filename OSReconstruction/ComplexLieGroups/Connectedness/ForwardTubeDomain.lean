import OSReconstruction.ComplexLieGroups.Connectedness.OrbitSetBasic
import OSReconstruction.ComplexLieGroups.GeodesicConvexity
import OSReconstruction.Wightman.Spacetime.MinkowskiGeometry

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Extract the k-th imaginary difference from z. -/
def imDiff (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) : Fin (d + 1) → ℝ :=
  fun μ => (z k μ - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im

/-- The imaginary difference is ℝ-linear in z. -/
lemma imDiff_linear (z₁ z₂ : Fin n → Fin (d + 1) → ℂ) (a b : ℝ) (k : Fin n) :
    imDiff (a • z₁ + b • z₂) k = a • imDiff z₁ k + b • imDiff z₂ k := by
  ext μ
  simp only [imDiff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k.val = 0
  · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, sub_zero]
  · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re]
    ring

/-- **The forward tube is ℝ-convex.** -/
theorem forwardTube_convex : Convex ℝ (ForwardTube d n) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab k
  show InOpenForwardCone d (imDiff (a • z₁ + b • z₂) k)
  rw [imDiff_linear]
  exact inOpenForwardCone_convex
    (Set.mem_setOf.mpr (hz₁ k)) (Set.mem_setOf.mpr (hz₂ k)) ha hb hab

/-- The complex Lorentz action is ℝ-linear in z. -/
lemma complexLorentzAction_real_linear
    (Λ : ComplexLorentzGroup d) (z₁ z₂ : Fin n → Fin (d + 1) → ℂ) (a b : ℝ) :
    complexLorentzAction Λ (a • z₁ + b • z₂) =
    a • complexLorentzAction Λ z₁ + b • complexLorentzAction Λ z₂ := by
  ext k μ
  simp only [complexLorentzAction, complexLorentzVectorAction, Pi.add_apply,
    Pi.smul_apply, Complex.real_smul]
  trans (↑a * ∑ ν, Λ.val μ ν * z₁ k ν + ↑b * ∑ ν, Λ.val μ ν * z₂ k ν)
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ν _
    ring
  · rfl

/-- **The intersection domain D_Λ is ℝ-convex.** -/
theorem d_lambda_convex (Λ : ComplexLorentzGroup d) :
    Convex ℝ {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} := by
  intro z₁ ⟨hz₁, hΛz₁⟩ z₂ ⟨hz₂, hΛz₂⟩ a b ha hb hab
  refine ⟨forwardTube_convex hz₁ hz₂ ha hb hab, ?_⟩
  rw [complexLorentzAction_real_linear]
  exact forwardTube_convex hΛz₁ hΛz₂ ha hb hab

/-- **The intersection domain D_Λ is preconnected** (convex implies preconnected). -/
theorem d_lambda_isPreconnected (Λ : ComplexLorentzGroup d) :
    IsPreconnected {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} :=
  (d_lambda_convex Λ).isPreconnected

/-- The action map z ↦ Λ·z is continuous (ℂ-linear in z). -/
theorem continuous_complexLorentzAction_snd (Λ : ComplexLorentzGroup d) :
    Continuous (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  simp only [complexLorentzAction]
  exact continuous_finset_sum Finset.univ
    (fun ν _ => continuous_const.mul ((continuous_apply ν).comp (continuous_apply k)))

/-- The action map z ↦ Λ·z is ℂ-differentiable (it is ℂ-linear in z). -/
theorem differentiable_complexLorentzAction_snd (Λ : ComplexLorentzGroup d) :
    Differentiable ℂ (fun z : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ z) := by
  apply differentiable_pi.mpr
  intro k
  apply differentiable_pi.mpr
  intro μ
  simp only [complexLorentzAction]
  apply Differentiable.fun_sum
  intro ν _
  apply Differentiable.const_mul
  have h1 : Differentiable ℂ (fun z : Fin n → Fin (d + 1) → ℂ => z k) := differentiable_apply k
  exact (differentiable_apply ν).comp h1

/-- D_Λ = {z ∈ FT : Λ·z ∈ FT} is open (intersection of two open preimages). -/
theorem isOpen_d_lambda (Λ : ComplexLorentzGroup d) :
    IsOpen {z | z ∈ ForwardTube d n ∧ complexLorentzAction Λ z ∈ ForwardTube d n} :=
  isOpen_forwardTube.inter (isOpen_forwardTube.preimage (continuous_complexLorentzAction_snd Λ))

/-! ### Real-Lorentz preservation infrastructure -/

/-- Complex difference vector associated to `imDiff`. -/
private def diffVec (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) : Fin (d + 1) → ℂ :=
  fun ν => z k ν - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) ν

/-- `imDiff` is the imaginary part of `diffVec`. -/
private lemma imDiff_eq_im_diffVec (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) :
    imDiff z k = fun μ => (diffVec z k μ).im := by
  ext μ
  simp [imDiff, diffVec]

/-- The Lorentz action commutes with taking successive differences. -/
private lemma diffVec_action (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) :
    diffVec (complexLorentzAction Λ z) k =
    fun μ => ∑ ν, Λ.val μ ν * diffVec z k ν := by
  ext μ
  simp only [diffVec, complexLorentzAction, complexLorentzVectorAction]
  by_cases hk : k.val = 0
  · simp [hk, sub_zero]
  · simp only [hk, ↓reduceDIte, complexLorentzVectorAction]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ν _
    ring

/-- Real Lorentz transformations preserve the forward tube.
    This is the configuration-level lift of
    `real_lorentz_preserves_forwardCone`. -/
theorem ofReal_preserves_forwardTube_base (R : RestrictedLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ ForwardTube d n := by
  intro k
  show InOpenForwardCone d (imDiff (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) k)
  rw [imDiff_eq_im_diffVec, diffVec_action]
  have h_im : (fun μ => (∑ ν, (ComplexLorentzGroup.ofReal R).val μ ν * diffVec z k ν).im) =
      (fun μ => ∑ ν, R.val.val μ ν * (diffVec z k ν).im) := by
    ext μ
    exact ofReal_im_action R (diffVec z k) μ
  rw [h_im]
  have hk : InOpenForwardCone d (imDiff z k) := hz k
  rw [imDiff_eq_im_diffVec] at hk
  exact real_lorentz_preserves_forwardCone R _ hk

/-- The forward tube is nonempty (for any n, d). -/
theorem forwardTube_nonempty : (ForwardTube d n).Nonempty := by
  -- Witness: z_k(μ) = (k+1) · i for μ = 0, and 0 otherwise.
  -- Then η_k = imDiff z k has η_k(0) = 1 > 0 and η_k(i>0) = 0, so Q(η_k) = -1 < 0.
  -- Use imDiff helper for cleaner reasoning.
  refine ⟨fun (k : Fin n) (μ : Fin (d + 1)) =>
    if μ = 0 then Complex.I * (↑(k : ℕ) + 1 : ℝ) else 0, fun k => ?_⟩
  set z : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => if μ = 0 then Complex.I * (↑(k : ℕ) + 1 : ℝ) else 0
  -- Compute imDiff z k
  have hη0 : imDiff z k 0 = 1 := by
    simp only [imDiff, z, ↓reduceIte]
    by_cases hk : (k : ℕ) = 0
    · simp [hk]
    · have hk1 : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk
      simp only [hk, ↓reduceDIte, ↓reduceIte, Complex.sub_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Nat.cast_sub hk1]
      ring
  have hηi : ∀ i : Fin d, imDiff z k (Fin.succ i) = 0 := by
    intro i
    have hs : (Fin.succ i : Fin (d + 1)) ≠ 0 := Fin.succ_ne_zero i
    by_cases hk : (k : ℕ) = 0
    · simp [imDiff, z, hs, hk]
    · simp [imDiff, z, hs, hk]
  constructor
  · -- η 0 > 0
    change imDiff z k 0 > 0
    rw [hη0]
    exact one_pos
  · -- Minkowski sum < 0
    change ∑ μ, minkowskiSignature d μ * imDiff z k μ ^ 2 < 0
    rw [minkowski_sum_decomp, hη0]
    simp only [hηi]
    norm_num

/-- For a one-point forward-tube configuration (`n = 1`), the complex Minkowski
quadratic form of that point is nonzero. -/
theorem forwardTube_one_complexQuadratic_ne_zero [NeZero d]
    (w : Fin 1 → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d 1) :
    (∑ μ : Fin (d + 1), (minkowskiSignature d μ : ℂ) * (w 0 μ) ^ 2) ≠ 0 := by
  let ξ : MinkowskiSpace d := fun μ => (w 0 μ).re
  let η : MinkowskiSpace d := fun μ => (w 0 μ).im
  have hcone : InOpenForwardCone d η := by
    have h0 := hw 0
    simpa [ForwardTube, η] using h0
  have hcone' : η 0 > 0 ∧ MinkowskiSpace.minkowskiNormSq d η < 0 := by
    refine ⟨hcone.1, ?_⟩
    simpa [InOpenForwardCone, MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature, minkowskiSignature, sq] using hcone.2
  have hsplit :
      (fun μ => w 0 μ) = (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I) := by
    ext μ
    simp [ξ, η, Complex.re_add_im]
  intro hq
  have hq0 : MinkowskiSpace.complexMinkowskiQuadratic d (fun μ => w 0 μ) = 0 := by
    simpa [MinkowskiSpace.complexMinkowskiQuadratic, MinkowskiSpace.metricSignature,
      minkowskiSignature] using hq
  have him_formula :
      (MinkowskiSpace.complexMinkowskiQuadratic d (fun μ => w 0 μ)).im =
        2 * MinkowskiSpace.minkowskiInner d ξ η := by
    calc
      (MinkowskiSpace.complexMinkowskiQuadratic d (fun μ => w 0 μ)).im =
          (MinkowskiSpace.complexMinkowskiQuadratic d
            (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).im := by
              simp [hsplit]
      _ = 2 * MinkowskiSpace.minkowskiInner d ξ η :=
        MinkowskiSpace.complexQuadratic_im (d := d) ξ η
  have horth : MinkowskiSpace.minkowskiInner d ξ η = 0 := by
    have hImZero :
        (MinkowskiSpace.complexMinkowskiQuadratic d (fun μ => w 0 μ)).im = 0 := by
      simp [hq0]
    linarith [him_formula, hImZero]
  have hξ_nonneg : MinkowskiSpace.minkowskiNormSq d ξ ≥ 0 :=
    MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg
      (d := d) ξ η hcone'.2 hcone'.1 horth
  have hre_formula :
      (MinkowskiSpace.complexMinkowskiQuadratic d (fun μ => w 0 μ)).re =
        MinkowskiSpace.minkowskiNormSq d ξ - MinkowskiSpace.minkowskiNormSq d η := by
    calc
      (MinkowskiSpace.complexMinkowskiQuadratic d (fun μ => w 0 μ)).re =
          (MinkowskiSpace.complexMinkowskiQuadratic d
            (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).re := by
              simp [hsplit]
      _ = MinkowskiSpace.minkowskiNormSq d ξ - MinkowskiSpace.minkowskiNormSq d η :=
        MinkowskiSpace.complexQuadratic_re (d := d) ξ η
  have hnorm_eq : MinkowskiSpace.minkowskiNormSq d ξ = MinkowskiSpace.minkowskiNormSq d η := by
    have hReZero :
        (MinkowskiSpace.complexMinkowskiQuadratic d (fun μ => w 0 μ)).re = 0 := by
      simp [hq0]
    linarith [hre_formula, hReZero]
  linarith [hξ_nonneg, hcone'.2, hnorm_eq]

end BHW
