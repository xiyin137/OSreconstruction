/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.Spacetime.MinkowskiGeometry
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Spectral Condition: Definitions and Equivalence

This file contains:
1. **Momentum-space spectral condition definitions**: Fourier transform on n-point
   Schwartz space, difference-variable reduction, `SpectralConditionDistribution`,
   `ForwardTubeAnalyticity`.
2. **Equivalence proof**: `SpectralConditionDistribution d W ↔ ForwardTubeAnalyticity d W`,
   using two axioms from hard analysis:
   - `cone_fourierLaplace_extension` (Vladimirov §25 Thm 25.1 / SW Thm 2-6)
   - `converse_paleyWiener_tube` (Vladimirov §26 Thm 26.1 / RS II §IX.3)

## Main Results

- `spectralConditionDistribution_iff_forwardTubeAnalyticity`:
  `SpectralConditionDistribution d W ↔ ForwardTubeAnalyticity d W`
-/

noncomputable section

open MeasureTheory Complex Filter Set Topology

/-! ### Momentum-Space Spectral Condition Definitions -/

section SpectralConditionDefinitions

variable (d : ℕ) [NeZero d]

/-- The product of closed forward light cones V̄₊ⁿ in momentum space.
    A momentum configuration (q₁, ..., qₙ) lies in this set iff each qₖ ∈ V̄₊. -/
def ProductForwardMomentumCone (n : ℕ) : Set (Fin n → Fin (d + 1) → ℝ) :=
  { q | ∀ k : Fin n, q k ∈ ForwardMomentumCone d }

/-- Uncurrying `(Fin n → Fin m → ℝ)` to `(Fin n × Fin m → ℝ)` as a linear equivalence. -/
private def uncurryLinearEquiv (d n : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin n × Fin (d + 1) → ℝ) where
  toFun f p := f p.1 p.2
  invFun g i j := g (i, j)
  left_inv _ := rfl
  right_inv _ := funext fun ⟨_, _⟩ => rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Continuous linear equivalence from `NPointSpacetime d n` to
    `EuclideanSpace ℝ (Fin n × Fin (d + 1))`, used to transfer the Fourier
    transform from Mathlib's inner-product-space formulation. -/
private noncomputable def nPointToEuclidean (n : ℕ) :
    NPointSpacetime d n ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin (d + 1)) :=
  (uncurryLinearEquiv d n).toContinuousLinearEquiv |>.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin (d + 1) => ℝ)).symm

/-- The Fourier transform of a Schwartz function on n-point spacetime,
    bundled as a `SchwartzMap`.

    Defined by transferring to `EuclideanSpace ℝ (Fin n × Fin (d + 1))` (which
    has `InnerProductSpace ℝ`), applying Mathlib's `fourierTransformCLM`, and
    transferring back. -/
noncomputable def SchwartzNPointSpace.fourierTransform {n : ℕ}
    (f : SchwartzNPointSpace d n) : SchwartzNPointSpace d n :=
  let e := nPointToEuclidean d n
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    (SchwartzMap.fourierTransformCLM ℂ
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f))

/-- Zero-basepoint section: embeds n difference variables into (n+1) absolute
    spacetime coordinates by setting the basepoint to zero and taking partial sums. -/
private noncomputable def diffVarSection (n : ℕ) :
    NPointSpacetime d n →L[ℝ] NPointSpacetime d (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ k μ => ∑ j : Fin k.val, ξ ⟨j.val, by omega⟩ μ
      map_add' := by
        intro ξ η; ext k μ; simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c ξ; ext k μ; simp [Finset.mul_sum] }

omit [NeZero d] in
@[simp] private theorem diffVarSection_zero (n : ℕ)
    (ξ : NPointSpacetime d n) (μ : Fin (d + 1)) :
    diffVarSection d n ξ 0 μ = 0 := by
  simp [diffVarSection]

omit [NeZero d] in
@[simp] private theorem diffVarSection_succ (n : ℕ)
    (ξ : NPointSpacetime d n) (k : Fin n) (μ : Fin (d + 1)) :
    diffVarSection d n ξ k.succ μ =
      diffVarSection d n ξ k.castSucc μ + ξ k μ := by
  change (∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ) =
    (∑ j : Fin k.val, ξ ⟨j.val, by omega⟩ μ) + ξ k μ
  rw [Fin.sum_univ_castSucc]
  simp [Fin.val_castSucc, Fin.val_last]

omit [NeZero d] in
private theorem diffVarSection_injective (n : ℕ) :
    Function.Injective (diffVarSection d n) := by
  intro ξ₁ ξ₂ h
  ext k μ
  have h_succ := congr_fun₂ h k.succ μ
  have h_cast := congr_fun₂ h k.castSucc μ
  simp only [diffVarSection_succ] at h_succ
  linarith

/-- Reduction to difference variables: precomposes a Schwartz function on (n+1)
    spacetime points with the zero-basepoint section map, producing a Schwartz
    function of n difference variables `ξⱼ = xⱼ₊₁ - xⱼ`. -/
noncomputable def diffVarReduction (n : ℕ) :
    SchwartzNPointSpace d (n + 1) →L[ℂ] SchwartzNPointSpace d n :=
  let hanti := (diffVarSection d n).toLinearMap.injective_iff_antilipschitz.mp
    (diffVarSection_injective d n)
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (diffVarSection d n).hasTemperateGrowth hanti.choose_spec.2

/-- **Spectral condition (distribution-level / Streater-Wightman form).**

    For each n, there exists a tempered distribution `w` on n copies of spacetime
    (the reduced Wightman function in difference variables ξⱼ = xⱼ - xⱼ₊₁) such that:
    1. `w` determines `W_{n+1}` via `diffVarReduction`.
    2. The Fourier transform of `w` has support in V̄₊ⁿ.

    Ref: Streater-Wightman, "PCT, Spin and Statistics, and All That", §3-1. -/
def SpectralConditionDistribution
    (W : (n : ℕ) → SchwartzNPointSpace d n → ℂ) : Prop :=
  ∀ (n : ℕ),
    ∃ (w : SchwartzNPointSpace d n → ℂ),
      Continuous w ∧ IsLinearMap ℂ w ∧
      (∀ f : SchwartzNPointSpace d (n + 1),
        W (n + 1) f = w (diffVarReduction d n f)) ∧
      (∀ φ : SchwartzNPointSpace d n,
        (∀ q : NPointSpacetime d n, φ q ≠ 0 →
          ∃ k : Fin n, q k ∉ ForwardMomentumCone d) →
        w (φ.fourierTransform) = 0)

/-- **Forward tube analyticity condition.**

    For each n, `W_n` extends to a holomorphic function on the forward tube `T_n`,
    with distributional boundary values recovering `W_n`. -/
def ForwardTubeAnalyticity
    (W : (n : ℕ) → SchwartzNPointSpace d n → ℂ) : Prop :=
  ∀ (n : ℕ),
    ∃ (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d n) ∧
      (∀ (f : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W n f)))

end SpectralConditionDefinitions

/-! ### Product Forward Tube and Paley-Wiener-Schwartz Axioms -/

variable {d : ℕ} [NeZero d]

/-- The product forward tube in difference coordinates. -/
def ProductForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  { ζ | ∀ k : Fin n, InOpenForwardCone d (fun μ => (ζ k μ).im) }

/-- The product forward tube is open. -/
private theorem isOpen_inOpenForwardCone' (d : ℕ) [NeZero d] :
    IsOpen { η : Fin (d + 1) → ℝ | InOpenForwardCone d η } := by
  simp only [InOpenForwardCone, Set.setOf_and]
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_apply 0)
  · have : Continuous (fun η : Fin (d + 1) → ℝ => MinkowskiSpace.minkowskiNormSq d η) := by
      simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
      apply continuous_finset_sum
      intro i _
      exact (continuous_const.mul (continuous_apply i)).mul (continuous_apply i)
    exact isOpen_lt this continuous_const

theorem isOpen_productForwardTube (n : ℕ) :
    IsOpen (ProductForwardTube d n) := by
  simp only [ProductForwardTube, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro k
  -- The k-th condition is the preimage of {η | InOpenForwardCone d η} under ζ ↦ (fun μ => (ζ k μ).im)
  let im_k : (Fin n → Fin (d + 1) → ℂ) → (Fin (d + 1) → ℝ) := fun ζ μ => (ζ k μ).im
  suffices IsOpen (im_k ⁻¹' { η | InOpenForwardCone d η }) by exact this
  apply (isOpen_inOpenForwardCone' d).preimage
  apply continuous_pi; intro μ
  exact Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply k))

/-- The open forward cone is stable under multiplication by a positive scalar. -/
private theorem inOpenForwardCone_smul (d : ℕ) [NeZero d]
    (c : ℝ) (hc : 0 < c) (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) :
    InOpenForwardCone d (c • η) := by
  constructor
  · simpa [Pi.smul_apply, smul_eq_mul] using mul_pos hc hη.1
  · have hscale : MinkowskiSpace.minkowskiNormSq d (c • η) =
        c ^ 2 * MinkowskiSpace.minkowskiNormSq d η := by
      simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
        Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      congr 1; ext μ; ring
    rw [hscale]
    exact mul_neg_of_pos_of_neg (pow_pos hc 2) hη.2

/-- A real point shifted by `iεη` lies in the product forward tube when `ε > 0`
    and each `η_k ∈ V₊°`. The imaginary part computes to `ε • η_k`. -/
private lemma shifted_point_in_productForwardTube {n : ℕ}
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : 0 < ε) (x : NPointSpacetime d n) :
    (fun k μ => (↑(x k μ) : ℂ) + ↑ε * ↑(η k μ) * Complex.I) ∈ ProductForwardTube d n := by
  intro k
  show InOpenForwardCone d (fun μ => ((↑(x k μ) : ℂ) + ↑ε * ↑(η k μ) * Complex.I).im)
  have him : (fun μ => ((↑(x k μ) : ℂ) + ↑ε * ↑(η k μ) * Complex.I).im) = ε • η k := by
    ext μ
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul,
      mul_zero, mul_one, zero_add, add_zero, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [him]
  exact inOpenForwardCone_smul d ε hε (η k) (hη k)

/-! ### Proof Infrastructure for the Forward Paley-Wiener-Schwartz Theorem

The proof of `cone_fourierLaplace_extension` follows Vladimirov §25 Thm 25.1.
The construction is the multivariate Fourier-Laplace transform:
- Define the kernel `ψ_z(q) = χ_Γ(q) · exp(i⟨z,q⟩)` where `χ_Γ` is a smooth
  cutoff for the product forward cone
- The Euclidean self-duality of `V₊` provides exponential damping
- `F(z) = w(FT[ψ_z])` is holomorphic by differentiating under the pairing
- Boundary values follow from `exp(-ε⟨η,q⟩) → 1` in Schwartz topology
-/

/-- The Euclidean inner product on spacetime (no Minkowski sign flip):
    `⟨η, p⟩_Eucl = ∑_μ η(μ) · p(μ)`. -/
private def euclideanDot (η p : Fin (d + 1) → ℝ) : ℝ :=
  ∑ μ, η μ * p μ

/-- **Quantitative self-duality of the forward cone**: for η ∈ V₊°, there exists c > 0 such that
    ⟨η, p⟩_Eucl ≥ c · ‖p‖ for all p ∈ V̄₊. This provides the uniform exponential
    damping needed for the Fourier-Laplace transform to converge.

    Follows from compactness of {p ∈ V̄₊ : ‖p‖ = 1} and continuity of
    the Euclidean inner product. -/
private lemma euclideanDot_lower_bound
    (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) :
    ∃ c : ℝ, c > 0 ∧ ∀ p : Fin (d + 1) → ℝ,
      p ∈ ForwardMomentumCone d → euclideanDot η p ≥ c * ‖p‖ := by
  obtain ⟨hη0, hηnorm⟩ := hη
  -- η₀² > spatialNormSq η (since η is timelike)
  have hη_dom := MinkowskiSpace.timelike_time_dominates_space d η hηnorm
  -- c := η₀ - √(spatialNormSq η) > 0
  set sη := Real.sqrt (MinkowskiSpace.spatialNormSq d η)
  have hsη_nn : 0 ≤ sη := Real.sqrt_nonneg _
  have hsη_lt : sη < η 0 := by
    calc sη < Real.sqrt ((η 0) ^ 2) :=
          Real.sqrt_lt_sqrt (MinkowskiSpace.spatialNormSq_nonneg d η) hη_dom
      _ = η 0 := Real.sqrt_sq (le_of_lt hη0)
  refine ⟨η 0 - sη, sub_pos.mpr hsη_lt, fun p hp => ?_⟩
  -- p ∈ V̄₊: minkowskiNormSq ≤ 0 and p₀ ≥ 0
  change MinkowskiSpace.IsCausal d p ∧ MinkowskiSpace.timeComponent d p ≥ 0 at hp
  have hp0 : p 0 ≥ 0 := hp.2
  have hp_causal : MinkowskiSpace.minkowskiNormSq d p ≤ 0 := hp.1
  have hp_spatial : MinkowskiSpace.spatialNormSq d p ≤ (p 0) ^ 2 := by
    have h1 := MinkowskiSpace.minkowskiNormSq_decomp d p; linarith
  -- Decompose euclideanDot = η₀p₀ + spatialInner
  have h_decomp : euclideanDot η p = η 0 * p 0 + MinkowskiSpace.spatialInner d η p := by
    unfold euclideanDot MinkowskiSpace.spatialInner
    rw [Fin.sum_univ_succ]
  -- |spatialInner η p| ≤ sη * p₀ (via Cauchy-Schwarz)
  have h_abs : |MinkowskiSpace.spatialInner d η p| ≤ sη * p 0 := by
    have h_sq : (MinkowskiSpace.spatialInner d η p) ^ 2 ≤ (sη * p 0) ^ 2 := by
      calc (MinkowskiSpace.spatialInner d η p) ^ 2
          ≤ MinkowskiSpace.spatialNormSq d η * MinkowskiSpace.spatialNormSq d p :=
            MinkowskiSpace.spatial_cauchy_schwarz d η p
        _ ≤ MinkowskiSpace.spatialNormSq d η * (p 0) ^ 2 :=
            mul_le_mul_of_nonneg_left hp_spatial (MinkowskiSpace.spatialNormSq_nonneg d η)
        _ = (sη * p 0) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (MinkowskiSpace.spatialNormSq_nonneg d η)]
    have h := Real.sqrt_le_sqrt h_sq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (mul_nonneg hsη_nn hp0)] at h
  -- euclideanDot η p ≥ (η₀ - sη) * p₀
  have h_lower : euclideanDot η p ≥ (η 0 - sη) * p 0 := by
    rw [h_decomp, sub_mul]
    linarith [neg_abs_le (MinkowskiSpace.spatialInner d η p)]
  -- ‖p‖ ≤ p₀ (sup norm: each component bounded by p₀)
  have h_norm_le : ‖p‖ ≤ p 0 := by
    apply (pi_norm_le_iff_of_nonneg hp0).mpr
    intro i
    rw [Real.norm_eq_abs]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_of_eq (abs_of_nonneg hp0)
    · have h_single : (p (Fin.succ j)) ^ 2 ≤ MinkowskiSpace.spatialNormSq d p := by
        unfold MinkowskiSpace.spatialNormSq
        exact Finset.single_le_sum (f := fun i => (p (Fin.succ i)) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      have h := Real.sqrt_le_sqrt (le_trans h_single hp_spatial)
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hp0] at h
  -- Conclude: (η₀ - sη) * p₀ ≥ (η₀ - sη) * ‖p‖
  linarith [mul_le_mul_of_nonneg_left h_norm_le (le_of_lt (sub_pos.mpr hsη_lt))]

/-- Complex n-point Euclidean dot product: `⟨z, q⟩ = ∑_k ∑_μ z_k(μ) · q_k(μ)`.
    For z = x + iy, Im⟨z, q⟩ = ∑_k ⟨y_k, q_k⟩_Eucl provides the damping. -/
private def complexNPointDot {n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ) (q : Fin n → Fin (d + 1) → ℝ) : ℂ :=
  ∑ k, ∑ μ, z k μ * ↑(q k μ)

/-- Smooth cutoff for the product forward momentum cone V̄₊ⁿ.
    Satisfies: χ = 1 on V̄₊ⁿ, 0 ≤ χ ≤ 1, C∞, supported in a neighborhood
    of V̄₊ⁿ. Built as product of single-cone cutoffs using `Real.smoothTransition`
    (cf. `SCV.smoothCutoff` in `FourierLaplaceCore.lean`). -/
private noncomputable def productConeCutoff (n : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) → ℝ :=
  fun q => ∏ k : Fin n,
    Real.smoothTransition (q k 0 + 1) *
    Real.smoothTransition (-(MinkowskiSpace.minkowskiNormSq d (q k)) + 1)

omit [NeZero d] in
private lemma productConeCutoff_smooth (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (productConeCutoff n : (Fin n → Fin (d + 1) → ℝ) → ℝ) := by
  unfold productConeCutoff
  apply contDiff_prod
  intro k _
  -- Each factor is smoothTransition(q k 0 + 1) * smoothTransition(-(minkowskiNormSq d (q k)) + 1)
  apply ContDiff.mul
  · -- smoothTransition(q k 0 + 1) is smooth
    exact Real.smoothTransition.contDiff.comp
      ((contDiff_apply_apply ℝ _ k 0).add contDiff_const)
  · -- smoothTransition(-(minkowskiNormSq d (q k)) + 1) is smooth
    apply Real.smoothTransition.contDiff.comp
    apply ContDiff.add _ contDiff_const
    apply ContDiff.neg
    -- minkowskiNormSq d (q k) = ∑ i, metricSignature d i * (q k i) * (q k i)
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    apply ContDiff.sum
    intro i _
    exact ((contDiff_const.mul (contDiff_apply_apply ℝ _ k i)).mul
      (contDiff_apply_apply ℝ _ k i))

omit [NeZero d] in
private lemma productConeCutoff_eq_one_on_cone {n : ℕ}
    {q : Fin n → Fin (d + 1) → ℝ} (hq : q ∈ ProductForwardMomentumCone d n) :
    productConeCutoff n q = 1 := by
  unfold productConeCutoff
  apply Finset.prod_eq_one
  intro k _
  have hk := hq k
  change MinkowskiSpace.IsCausal d (q k) ∧ MinkowskiSpace.timeComponent d (q k) ≥ 0 at hk
  have h_time : q k 0 ≥ 0 := hk.2
  have h_norm : MinkowskiSpace.minkowskiNormSq d (q k) ≤ 0 := hk.1
  rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), one_mul]

/-- The pointwise Fourier-Laplace kernel: `ψ_z(q) = χ_Γ(q) · exp(i⟨z, q⟩)`.
    This is the multivariate analogue of `SCV.psiZ` from `FourierLaplaceCore.lean`. -/
private noncomputable def psiZMulti {n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ) (q : Fin n → Fin (d + 1) → ℝ) : ℂ :=
  ↑(productConeCutoff n q) * Complex.exp (Complex.I * complexNPointDot z q)

/-- Smoothness of the kernel `ψ_z` in the `q` variable.
    Follows from `productConeCutoff_smooth` and smoothness of `exp ∘ linear`. -/
private lemma psiZMulti_contDiff {n : ℕ} (z : Fin n → Fin (d + 1) → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (psiZMulti z : (Fin n → Fin (d + 1) → ℝ) → ℂ) := by
  unfold psiZMulti
  apply ContDiff.mul
  · -- ↑(productConeCutoff n q) is smooth: ofRealCLM ∘ productConeCutoff
    exact Complex.ofRealCLM.contDiff.comp (productConeCutoff_smooth n)
  · -- exp(I * complexNPointDot z q) is smooth: exp ∘ linear
    apply ContDiff.comp Complex.contDiff_exp
    apply contDiff_const.mul
    -- complexNPointDot z q = ∑ k, ∑ μ, z k μ * ↑(q k μ) is smooth in q
    unfold complexNPointDot
    apply ContDiff.sum; intro k _
    apply ContDiff.sum; intro μ _
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ _ k μ))

/-- Rapid decay of `ψ_z` when `Im(z) ∈ V₊°ⁿ`.
    The exponential factor `exp(-∑_k ⟨Im(z_k), q_k⟩_Eucl)` decays as `exp(-c·‖q‖)`
    on supp(χ_Γ) by `euclideanDot_lower_bound`, dominating any polynomial growth.
    Combined with `productConeCutoff_smooth`, this gives Schwartz decay. -/
private lemma psiZMulti_rapid_decay {n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ProductForwardTube d n) :
    ∀ (k : ℕ) (m : ℕ),
      ∃ C : ℝ, ∀ q : Fin n → Fin (d + 1) → ℝ,
        ‖q‖ ^ k * ‖iteratedFDeriv ℝ m (psiZMulti z) q‖ ≤ C := by
  sorry

/-- The Fourier-Laplace kernel bundled as a Schwartz function.
    When Im(z) ∈ V₊°ⁿ, exponential damping from `euclideanDot_lower_bound`
    makes `ψ_z(q) = χ_Γ(q) · exp(i⟨z,q⟩)` rapidly decreasing, hence Schwartz.

    This is the multivariate analogue of `SCV.schwartzPsiZ` from
    `FourierLaplaceCore.lean`. -/
private noncomputable def schwartzPsiZMulti {n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ProductForwardTube d n) :
    SchwartzNPointSpace d n :=
  ⟨psiZMulti z, psiZMulti_contDiff z, psiZMulti_rapid_decay z hz⟩

@[simp] private lemma schwartzPsiZMulti_apply {n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ProductForwardTube d n)
    (q : Fin n → Fin (d + 1) → ℝ) :
    schwartzPsiZMulti z hz q = psiZMulti z q := rfl

/-- The Fourier-Laplace extension: `F(z) = w(FT[ψ_z])`.

    The tempered distribution `w` is applied to the n-point Fourier transform
    of the Schwartz kernel `ψ_z`. Since the distributional Fourier transform
    `ŵ(φ) := w(FT[φ])` has support in V̄₊ⁿ (by `hw_supp`), and `ψ_z` equals
    `exp(i⟨z,·⟩)` on V̄₊ⁿ (by `productConeCutoff_eq_one_on_cone`), the value
    `F(z)` captures the Fourier-Laplace transform of `ŵ`. -/
private noncomputable def coneFourierLaplace {n : ℕ}
    (w : SchwartzNPointSpace d n → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ProductForwardTube d n) : ℂ :=
  w ((schwartzPsiZMulti z hz).fourierTransform)

/-- **Holomorphy** of `z ↦ w(FT[ψ_z])` on the product forward tube.

    Proof strategy (following `SCV.paley_wiener_half_line`):
    1. Define `F(z) = if hz : z ∈ ProductForwardTube then coneFourierLaplace w z hz else 0`
    2. Show `z ↦ ψ_z` is holomorphic in the Schwartz topology by establishing
       polynomial seminorm bounds along horizontal lines (multivariate analogue
       of `SCV.schwartzPsiZ_seminorm_horizontal_bound`)
    3. Since `w` is continuous and ℂ-linear, `z ↦ w(FT[ψ_z])` is holomorphic
       as the composition of a holomorphic Schwartz-valued map with a CLM
    4. The `dite` construction agrees with `coneFourierLaplace` on the open tube,
       so `DifferentiableOn` follows -/
private lemma coneFourierLaplace_holomorphic {n : ℕ}
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w) :
    ∃ (F : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      (∀ z (hz : z ∈ ProductForwardTube d n),
        F z = coneFourierLaplace w z hz) ∧
      DifferentiableOn ℂ F (ProductForwardTube d n) := by
  sorry

/-- The smeared kernel `Ψ_ε`: the Schwartz function whose pointwise value at `p` is
    `∫ φ(x) · FT[ψ_{x+iεη}](p) dx`. This is Schwartz by:
    - Bochner integrability of `x ↦ φ(x) · FT[ψ_{x+iεη}](p)` (Schwartz decay of `φ`
      + uniform bounds on FT[ψ])
    - Smoothness + rapid decay of the resulting function (differentiation under
      the integral sign + dominated convergence) -/
private noncomputable def smearedKernel {n : ℕ}
    (φ : SchwartzNPointSpace d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : 0 < ε) : SchwartzNPointSpace d n :=
  ⟨fun p => ∫ x : NPointSpacetime d n,
      let ψFT : SchwartzNPointSpace d n := (schwartzPsiZMulti
        (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I)
        (shifted_point_in_productForwardTube η hη ε hε x)).fourierTransform
      φ x * ψFT p,
    sorry, sorry⟩

/-- **CLM interchange**: the smeared Fourier-Laplace integral equals `w` applied
    to the smeared kernel.

    Mathematical content:
    - Bundle `w` as a CLM (from `hw_cont` + `hw_lin`)
    - Show `x ↦ φ(x) • FT[ψ_{x+iεη}]` is Bochner integrable in
      `SchwartzNPointSpace` (uses `SchwartzMap.instCompleteSpace` +
      Schwartz decay of `φ` + uniform Schwartz seminorm bounds on `ψ`)
    - Apply `ContinuousLinearMap.integral_comp_comm` to interchange
    - The result identifies `w` of the Bochner integral with `w(smearedKernel)`

    Ref: `ContinuousLinearMap.integral_comp_comm` (Mathlib),
    `SchwartzMap.instCompleteSpace` (`SchwartzComplete.lean`) -/
private lemma smearedKernel_eq {n : ℕ}
    (w : SchwartzNPointSpace d n → ℂ) (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (φ : SchwartzNPointSpace d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k))
    (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointSpacetime d n,
      w ((schwartzPsiZMulti
          (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I)
          (shifted_point_in_productForwardTube η hη ε hε x)).fourierTransform) * (φ x) =
    w (smearedKernel φ η hη ε hε) := by
  sorry

/-- **Schwartz convergence of the smeared kernel**: as `ε → 0⁺`,
    `smearedKernel φ η ε → φ` in the Schwartz topology.

    Mathematical content (the core Fourier analysis):
    1. **Fubini**: `(smearedKernel φ η ε)(q)` computes to
       `χ_Γ(q) · exp(-ε⟨η,q⟩) · (FT⁻¹[φ])(q)` (up to normalization)
    2. **Damping**: `exp(-ε⟨η,q⟩) → 1` pointwise on `V̄₊ⁿ`
       with uniform Schwartz seminorm bounds via `euclideanDot_lower_bound`
    3. **Support**: `χ_Γ = 1` on `V̄₊ⁿ` by `productConeCutoff_eq_one_on_cone`
    4. **Fourier inversion**: `FT[FT⁻¹[φ]] = φ` -/
private lemma smearedKernel_tendsto {n : ℕ}
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_supp : ∀ φ : SchwartzNPointSpace d n,
      (∀ q : NPointSpacetime d n, φ q ≠ 0 →
        ∃ k : Fin n, q k ∉ ForwardMomentumCone d) →
      w (φ.fourierTransform) = 0)
    (φ : SchwartzNPointSpace d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : ∀ k, InOpenForwardCone d (η k)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        if hε : 0 < ε then smearedKernel φ η hη ε hε
        else (0 : SchwartzNPointSpace d n))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds φ) := by
  sorry

/-- **Boundary-value convergence**: `∫ F(x + iεη) φ(x) dx → w(φ)` as `ε → 0⁺`.

    Proof: Decomposed into three steps using `Filter.tendsto_congr'`:
    1. **Phase 1** (proved): Replace `F` with `w(FT[ψ])` via `hF_eq` +
       `shifted_point_in_productForwardTube` for ε > 0
    2. **Phase 2** (sorry'd): CLM interchange via `smearedKernel_eq`
    3. **Phase 3+4** (sorry'd + proved): Schwartz convergence
       `smearedKernel_tendsto` composed with continuity of `w` -/
private lemma coneFourierLaplace_boundaryValue {n : ℕ}
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (hw_supp : ∀ φ : SchwartzNPointSpace d n,
      (∀ q : NPointSpacetime d n, φ q ≠ 0 →
        ∃ k : Fin n, q k ∉ ForwardMomentumCone d) →
      w (φ.fourierTransform) = 0)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_eq : ∀ z (hz : z ∈ ProductForwardTube d n),
      F z = coneFourierLaplace w z hz) :
    ∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k : Fin n, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (w φ)) := by
  intro φ η hη
  -- Define the total wrapper for the smeared kernel
  let Ψ : ℝ → SchwartzNPointSpace d n := fun ε =>
    if hε : 0 < ε then smearedKernel φ η hη ε hε else 0
  -- Phase 3+4: w(Ψ_ε) → w(φ) by continuity of w + Schwartz convergence
  have hΨ_tendsto : Filter.Tendsto (w ∘ Ψ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (w φ)) :=
    hw_cont.continuousAt.tendsto.comp (smearedKernel_tendsto w hw_supp φ η hη)
  -- Phase 1+2: For ε > 0, ∫ F(x+iεη) * φ(x) = w(Ψ(ε))
  refine (Filter.tendsto_congr' ?_).mpr hΨ_tendsto
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Set.mem_Ioi] at hε
  simp only [Function.comp_def, Ψ, dif_pos hε]
  -- Phase 1: Replace F with w(FT[ψ]) inside the integral
  have h_pointwise : ∀ x : NPointSpacetime d n,
      F (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) =
      w ((schwartzPsiZMulti
        (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I)
        (shifted_point_in_productForwardTube η hη ε hε x)).fourierTransform) :=
    fun x => hF_eq _ _
  simp_rw [h_pointwise]
  -- Phase 2: CLM interchange
  exact smearedKernel_eq w hw_cont hw_lin φ η hη ε hε

/-- **Forward Paley-Wiener-Schwartz for the product forward cone**
    (Vladimirov §25 Thm 25.1 / SW Thm 2-6).

    Constructs the multivariate Fourier-Laplace extension `F(z) = w(FT[ψ_z])`
    and proves holomorphy on the product forward tube with distributional
    boundary values recovering `w`.

    Ref: Vladimirov, "Methods of the Theory of Generalized Functions", §25;
    Streater-Wightman, "PCT, Spin and Statistics, and All That", Thm 2-6. -/
theorem cone_fourierLaplace_extension (d n : ℕ) [NeZero d]
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (hw_supp : ∀ φ : SchwartzNPointSpace d n,
      (∀ q : NPointSpacetime d n, φ q ≠ 0 →
        ∃ k : Fin n, q k ∉ ForwardMomentumCone d) →
      w (φ.fourierTransform) = 0) :
    ∃ (F : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F (ProductForwardTube d n) ∧
      (∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k : Fin n, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (w φ))) := by
  obtain ⟨F, hF_eq, hF_holo⟩ := coneFourierLaplace_holomorphic w hw_cont hw_lin
  exact ⟨F, hF_holo, coneFourierLaplace_boundaryValue w hw_cont hw_lin hw_supp F hF_eq⟩

/-- **Converse Paley-Wiener-Schwartz** (Vladimirov §26 Thm 26.1 / RS II §IX.3). -/
 theorem converse_paleyWiener_tube (d n : ℕ) [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ProductForwardTube d n))
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (hF_bv : ∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k : Fin n, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (w φ))) :
    ∀ φ : SchwartzNPointSpace d n,
      (∀ q : NPointSpacetime d n, φ q ≠ 0 →
        ∃ k : Fin n, q k ∉ ForwardMomentumCone d) →
      w (φ.fourierTransform) = 0 := by
  sorry

/-! ### Complex Difference Coordinates -/

/-- Complex difference-coordinate map. -/
noncomputable def complexDiffCoord (d : ℕ) (n : ℕ) :
    (Fin (n + 1) → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → Fin (d + 1) → ℂ) where
  toFun z k μ := z k.succ μ - z k.castSucc μ
  map_add' u v := by ext k μ; simp [Pi.add_apply, add_sub_add_comm]
  map_smul' c u := by ext k μ; simp [Pi.smul_apply, smul_sub, mul_sub]

/-- Complex partial-sum section. -/
noncomputable def complexDiffVarSection (d : ℕ) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → Fin (d + 1) → ℂ) where
  toFun ζ k μ := ∑ j : Fin k.val, ζ ⟨j.val, by omega⟩ μ
  map_add' u v := by ext k μ; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext k μ; simp [Finset.mul_sum]

@[simp] lemma complexDiffVarSection_zero (n : ℕ) (ζ : Fin n → Fin (d + 1) → ℂ)
    (μ : Fin (d + 1)) : complexDiffVarSection d n ζ 0 μ = 0 := by
  simp [complexDiffVarSection]

lemma complexDiffVarSection_succ (n : ℕ) (ζ : Fin n → Fin (d + 1) → ℂ)
    (k : Fin n) (μ : Fin (d + 1)) :
    complexDiffVarSection d n ζ k.succ μ =
      complexDiffVarSection d n ζ k.castSucc μ + ζ k μ := by
  change (∑ j : Fin (k.val + 1), ζ ⟨j.val, by omega⟩ μ) =
    (∑ j : Fin k.val, ζ ⟨j.val, by omega⟩ μ) + ζ k μ
  rw [Fin.sum_univ_castSucc]
  simp [Fin.val_castSucc, Fin.val_last]

/-- `complexDiffCoord ∘ complexDiffVarSection = id`. -/
lemma complexDiffCoord_comp_section (n : ℕ) (ζ : Fin n → Fin (d + 1) → ℂ) :
    complexDiffCoord d n (complexDiffVarSection d n ζ) = ζ := by
  ext k μ
  simp only [complexDiffCoord, LinearMap.coe_mk, AddHom.coe_mk]
  rw [complexDiffVarSection_succ]
  ring

/-! ### Geometric Glue -/

/-- Difference coordinates map ForwardTube into ProductForwardTube. -/
lemma diffCoord_maps_forwardTube_to_productTube (n : ℕ)
    (z : Fin (n + 1) → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d (n + 1)) :
    complexDiffCoord d n z ∈ ProductForwardTube d n := by
  intro k
  exact hz k.succ

/-- Shifted partial-sum section maps ProductForwardTube into ForwardTube. -/
lemma shifted_section_maps_productTube_to_forwardTube (n : ℕ)
    (z₀ : Fin (d + 1) → ℂ) (hz₀ : InOpenForwardCone d (fun μ => (z₀ μ).im))
    (ζ : Fin n → Fin (d + 1) → ℂ) (hζ : ζ ∈ ProductForwardTube d n) :
    (fun k μ => z₀ μ + complexDiffVarSection d n ζ k μ) ∈ ForwardTube d (n + 1) := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · -- k = 0: prev = 0, section at 0 is 0, so successive difference is Im(z₀)
    simp only [Fin.val_zero, dite_true, Pi.zero_apply, sub_zero,
      complexDiffVarSection_zero, add_zero]
    exact hz₀
  · -- k = j.succ: successive difference is Im(ζ j)
    simp only [Fin.val_succ, dif_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
    -- The prev is z₀ + section ζ ⟨j.val, _⟩ which equals z₀ + section ζ j.castSucc
    -- Use complexDiffVarSection_succ: section j.succ = section j.castSucc + ζ j
    -- So the difference is ζ j
    convert hζ j using 1
    ext μ
    show (z₀ μ + complexDiffVarSection d n ζ (Fin.succ j) μ -
      (z₀ μ + complexDiffVarSection d n ζ ⟨j.val, by omega⟩ μ)).im = (ζ j μ).im
    have hcast : (⟨j.val, by omega⟩ : Fin (n + 1)) = j.castSucc := Fin.ext (by simp)
    rw [hcast, complexDiffVarSection_succ]
    congr 1; ring

/-- `InForwardCone` successive differences lie in open forward cone. -/
lemma inForwardCone_succ_implies_diffs_inOpenForwardCone (n : ℕ)
    (η : Fin (n + 1) → Fin (d + 1) → ℝ) (hη : InForwardCone d (n + 1) η) :
    ∀ k : Fin n, InOpenForwardCone d (fun μ => η k.succ μ - η k.castSucc μ) := by
  intro k
  exact hη k.succ

/-! ### Proof of the Main Equivalence -/

variable (d) in
/-- The reduced distribution in difference variables exists from translation invariance. -/
lemma exists_diffVar_distribution
    {W : (n : ℕ) → SchwartzNPointSpace d n → ℂ}
    (hW_tempered : ∀ n, Continuous (W n))
    (hW_linear : ∀ n, IsLinearMap ℂ (W n))
    (hW_transl : ∀ (n : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d n),
      (∀ x : NPointSpacetime d n, g.toFun x = f.toFun (fun i => x i + a)) →
      W n f = W n g)
    (n : ℕ) :
    ∃ (w : SchwartzNPointSpace d n → ℂ),
      Continuous w ∧ IsLinearMap ℂ w ∧
      (∀ f : SchwartzNPointSpace d (n + 1), W (n + 1) f = w (diffVarReduction d n f)) := by
  sorry

variable (d) in
/-- Forward direction helper: lift F from ProductForwardTube to ForwardTube. -/
lemma forwardTube_extension_of_productTube {n : ℕ}
    {W : (m : ℕ) → SchwartzNPointSpace d m → ℂ}
    (hW_tempered : ∀ m, Continuous (W m))
    (hW_linear : ∀ m, IsLinearMap ℂ (W m))
    (hW_transl : ∀ (m : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d m),
      (∀ x : NPointSpacetime d m, g.toFun x = f.toFun (fun i => x i + a)) →
      W m f = W m g)
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_det : ∀ f : SchwartzNPointSpace d (n + 1), W (n + 1) f = w (diffVarReduction d n f))
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ProductForwardTube d n))
    (hF_bv : ∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k : Fin n, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (w φ))) :
    ∃ (W_analytic : (Fin (n + 1) → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d (n + 1)) ∧
      (∀ (f : SchwartzNPointSpace d (n + 1)) (η : Fin (n + 1) → Fin (d + 1) → ℝ),
        InForwardCone d (n + 1) η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d (n + 1),
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W (n + 1) f))) := by
  -- Define W_analytic := F ∘ complexDiffCoord
  refine ⟨F ∘ (complexDiffCoord d n), ?_, ?_⟩
  · -- Holomorphicity
    intro z hz
    have hmaps := diffCoord_maps_forwardTube_to_productTube n z hz
    have hF_at := hF_holo.differentiableAt
      (IsOpen.mem_nhds (isOpen_productForwardTube n) hmaps)
    have hL_diff : DifferentiableAt ℂ (complexDiffCoord d n) z :=
      (complexDiffCoord d n).toContinuousLinearMap.differentiableAt
    exact (hF_at.comp z hL_diff).differentiableWithinAt
  · -- Boundary values
    sorry

variable (d) in
/-- Backward direction helper: construct F on ProductForwardTube from W_analytic. -/
lemma productTube_function_of_forwardTube {n : ℕ}
    {W : (m : ℕ) → SchwartzNPointSpace d m → ℂ}
    (hW_tempered : ∀ m, Continuous (W m))
    (hW_linear : ∀ m, IsLinearMap ℂ (W m))
    (hW_transl : ∀ (m : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d m),
      (∀ x : NPointSpacetime d m, g.toFun x = f.toFun (fun i => x i + a)) →
      W m f = W m g)
    (w : SchwartzNPointSpace d n → ℂ)
    (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (hw_det : ∀ f : SchwartzNPointSpace d (n + 1), W (n + 1) f = w (diffVarReduction d n f))
    (W_analytic : (Fin (n + 1) → Fin (d + 1) → ℂ) → ℂ)
    (hWa_holo : DifferentiableOn ℂ W_analytic (ForwardTube d (n + 1)))
    (hWa_bv : ∀ (f : SchwartzNPointSpace d (n + 1)) (η : Fin (n + 1) → Fin (d + 1) → ℝ),
      InForwardCone d (n + 1) η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointSpacetime d (n + 1),
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W (n + 1) f))) :
    ∃ (F : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F (ProductForwardTube d n) ∧
      (∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k : Fin n, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (w φ))) := by
  sorry

/-- The constant-1 Schwartz function on the 0-dimensional spacetime. -/
private noncomputable def schwartzConstOne (d : ℕ) [NeZero d] : SchwartzNPointSpace d 0 :=
  ⟨fun _ => 1, contDiff_const, fun k n =>
    ⟨‖iteratedFDeriv ℝ n (fun _ : NPointSpacetime d 0 => (1 : ℂ)) 0‖, fun x => by
      rw [show x = 0 from Subsingleton.elim x 0, norm_zero]
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · rw [zero_pow hk, zero_mul]; exact norm_nonneg _⟩⟩

@[simp] private lemma schwartzConstOne_apply (d : ℕ) [NeZero d] (x : NPointSpacetime d 0) :
    schwartzConstOne d x = 1 := rfl

private lemma schwartz_zero_eq_smul (d : ℕ) [NeZero d] (f : SchwartzNPointSpace d 0) :
    f = (f 0) • schwartzConstOne d := by
  ext x; rw [show x = 0 from Subsingleton.elim x 0]
  rw [SchwartzMap.smul_apply, smul_eq_mul, schwartzConstOne_apply, mul_one]

private lemma volume_nPointSpacetime_zero_eq_dirac (d : ℕ) [NeZero d] :
    (volume : Measure (NPointSpacetime d 0)) = Measure.dirac 0 := by
  rw [volume_pi, Measure.pi_of_empty (x := (0 : NPointSpacetime d 0))]

variable (d) in
/-- The zero-point case of ForwardTubeAnalyticity is trivial. -/
lemma forwardTubeAnalyticity_zero
    {W : (n : ℕ) → SchwartzNPointSpace d n → ℂ}
    (hW_tempered : ∀ n, Continuous (W n))
    (hW_linear : ∀ n, IsLinearMap ℂ (W n)) :
    ∃ (W_analytic : (Fin 0 → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d 0) ∧
      (∀ (f : SchwartzNPointSpace d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
        InForwardCone d 0 η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d 0,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W 0 f))) := by
  let e := schwartzConstOne d
  refine ⟨fun _ => W 0 e, differentiableOn_const _, ?_⟩
  intro f η _
  have h_integral : ∫ x : NPointSpacetime d 0, W 0 e * f x = W 0 f := by
    rw [volume_nPointSpacetime_zero_eq_dirac, MeasureTheory.integral_dirac]
    have hf_eq := schwartz_zero_eq_smul d f
    conv_rhs => rw [hf_eq, (hW_linear 0).map_smul, smul_eq_mul]
    ring
  refine Filter.Tendsto.congr (fun ε => ?_) tendsto_const_nhds
  change W 0 f = ∫ x : NPointSpacetime d 0, W 0 e * f x
  exact h_integral.symm

/-! ### Main Theorem -/

variable (d) in
/-- **Equivalence of the two spectral condition formulations.**
    Ref: Streater-Wightman, Theorem 3-5; Reed-Simon Vol. II, §IX.3. -/
theorem spectralConditionDistribution_iff_forwardTubeAnalyticity
    {W : (n : ℕ) → SchwartzNPointSpace d n → ℂ}
    (hW_tempered : ∀ n, Continuous (W n))
    (hW_linear : ∀ n, IsLinearMap ℂ (W n))
    (hW_transl : ∀ (n : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d n),
      (∀ x : NPointSpacetime d n, g.toFun x = f.toFun (fun i => x i + a)) →
      W n f = W n g) :
    SpectralConditionDistribution d W ↔ ForwardTubeAnalyticity d W := by
  constructor
  · intro hSpec n
    match n with
    | 0 => exact forwardTubeAnalyticity_zero d hW_tempered hW_linear
    | n + 1 =>
      obtain ⟨w, hw_cont, hw_lin, hw_det, hw_supp⟩ := hSpec n
      obtain ⟨F, hF_holo, hF_bv⟩ :=
        cone_fourierLaplace_extension d n w hw_cont hw_lin hw_supp
      exact forwardTube_extension_of_productTube d
        hW_tempered hW_linear hW_transl w hw_det F hF_holo hF_bv
  · intro hAnal n
    obtain ⟨W_analytic, hWa_holo, hWa_bv⟩ := hAnal (n + 1)
    obtain ⟨w, hw_cont, hw_lin, hw_det⟩ :=
      exists_diffVar_distribution d hW_tempered hW_linear hW_transl n
    refine ⟨w, hw_cont, hw_lin, hw_det, ?_⟩
    obtain ⟨F, hF_holo, hF_bv⟩ :=
      productTube_function_of_forwardTube d
        hW_tempered hW_linear hW_transl w hw_cont hw_lin hw_det
        W_analytic hWa_holo hWa_bv
    exact @converse_paleyWiener_tube d ‹_› d n ‹_› F hF_holo w hw_cont hw_lin hF_bv
