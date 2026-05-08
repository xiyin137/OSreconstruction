/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Algebra.Group.Quotient
import OSReconstruction.ComplexLieGroups.GeodesicConvexity
import OSReconstruction.ComplexLieGroups.AdjacentOverlapWitness
import OSReconstruction.ComplexLieGroups.Connectedness.Action
import OSReconstruction.ComplexLieGroups.Connectedness.DimensionZero
import OSReconstruction.ComplexLieGroups.Connectedness.ForwardTubeDomain
import OSReconstruction.ComplexLieGroups.Connectedness.OrbitSetBasic
import OSReconstruction.ComplexLieGroups.Connectedness.OrbitSetQuotient
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Preconnected
import OSReconstruction.ComplexLieGroups.Connectedness.Permutation
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected
import OSReconstruction.ComplexLieGroups.Connectedness.Topology
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesSCV
import OSReconstruction.ComplexLieGroups.D1OrbitSet
import OSReconstruction.SCV.IdentityTheorem

/-!
# Bargmann-Hall-Wightman Theorem

This file proves the Bargmann-Hall-Wightman theorem using the connectedness of
the complex Lorentz group SO⁺(1,d;ℂ) and the identity theorem.

## Main results

* `complex_lorentz_invariance` — real Lorentz invariance extends to complex Lorentz invariance
* `bargmann_hall_wightman_theorem` — the full BHW theorem

## Proof outline

### Complex Lorentz invariance (`complex_lorentz_invariance`)

**Step 1 — Near-identity invariance (identity theorem):**
Fix z₀ ∈ FT and a basis X₁,...,Xₘ of so(1,d;ℝ). The map
  Φ(c₁,...,cₘ) = F(exp(c₁X₁)·...·exp(cₘXₘ)·z₀)
is holomorphic in each cᵢ (separately) on an open set in ℂᵐ containing 0.
For real cᵢ, the product is a real Lorentz transformation, so Φ = F(z₀) on ℝᵐ.
By the 1D identity theorem applied variable-by-variable (SCV/Osgood + Analyticity),
Φ = F(z₀) on a polydisc near 0 in ℂᵐ. Since the exponential map is a local
diffeomorphism, this gives F(Λ·z₀) = F(z₀) for Λ near 1 in SO⁺(1,d;ℂ).

**Step 2 — Propagation (open-closed on connected orbit set):**
For fixed z ∈ FT, define U_z = {Λ : Λ·z ∈ FT} (open) and
S_z = {Λ ∈ U_z : F(Λ·z) = F(z)}.
- S_z is **open** in U_z: at Λ₀ ∈ S_z, apply Step 1 at z' = Λ₀·z ∈ FT,
  then translate via Λ ↦ ΛΛ₀ (continuous right multiplication).
- S_z is **closed** in U_z: if Λₙ → Λ₀ with F(Λₙ·z) = F(z) and
  Λ₀·z ∈ FT, then F(Λ₀·z) = lim F(Λₙ·z) = F(z) by continuity.
- 1 ∈ S_z and U_z is connected ⟹ S_z = U_z.

### Bargmann-Hall-Wightman theorem

1. **Extended tube T'_n**: Complex Lorentz invariance makes F_ext(Λ·w) := F(w)
   well-defined on T'_n = ⋃_Λ Λ·FT.
2. **Jost points**: Local commutativity gives F(π·x) = F(x) at real spacelike
   configurations for adjacent transpositions π.
3. **Edge-of-the-wedge**: Adjacent permuted tubes are glued via
   `SCV.edge_of_the_wedge_theorem`.
4. **Identity theorem**: Uniqueness on the connected permuted extended tube.

## References

* Bargmann, Hall, Wightman (1957), Nuovo Cimento 5, 1-14.
* Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-11.
* Jost (1965), *The General Theory of Quantized Fields*, Ch. IV.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-! ### Forward tube and related structures

`ForwardTube` is shared infrastructure (re-exported from
`ComplexLieGroups.DifferenceCoordinates` / `BHWCore`) and reused here.
`InOpenForwardCone`, `minkowski_sum_decomp`, `spatial_norm_lt_time`, and
`inOpenForwardCone_convex` are imported from `GeodesicConvexity.lean`. -/

/-! ### Convexity of forward tube and intersection domains -/

/-! ### Complex Lorentz invariance -/

/-- The one-parameter action `t ↦ exp(tX) · z` using the matrix exponential directly.
    Each entry is a power series in t, hence differentiable. -/
private theorem differentiable_expAction
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (z : Fin n → Fin (d + 1) → ℂ) :
    Differentiable ℂ (fun t : ℂ =>
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν) :
      ℂ → Fin n → Fin (d + 1) → ℂ) := by
  have hexp : Differentiable ℂ (fun t : ℂ => (exp (t • X) : Matrix _ _ ℂ)) :=
    fun t => (hasDerivAt_exp_smul_const X t).differentiableAt
  apply differentiable_pi.mpr; intro k
  apply differentiable_pi.mpr; intro μ
  apply Differentiable.fun_sum; intro ν _
  exact ((differentiable_apply ν).comp ((differentiable_apply μ).comp hexp)).mul
    (differentiable_const _)

/-- Bridge lemma: the real matrix exponential maps to complex via `map ofReal`.
    Specifically, `(exp(s • Y)).map ofReal = exp((s : ℂ) • Y.map ofReal)`. -/
private theorem exp_map_ofReal_bridge (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (s : ℝ) :
    (exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal =
      (exp ((s : ℂ) • Y.map Complex.ofReal) : Matrix _ _ ℂ) := by
  -- (exp(s•Y)).map ofReal = ofRealHom.mapMatrix (exp(s•Y))
  --                       = exp (ofRealHom.mapMatrix (s•Y))     by map_exp
  --                       = exp ((s:ℂ) • Y.map ofReal)          by smul commutation
  have hcont : Continuous (Complex.ofRealHom.mapMatrix :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  have h1 : Complex.ofRealHom.mapMatrix (exp (s • Y)) =
      exp (Complex.ofRealHom.mapMatrix (s • Y)) :=
    map_exp (f := Complex.ofRealHom.mapMatrix) hcont (s • Y)
  have h2 : Complex.ofRealHom.mapMatrix (s • Y) = (s : ℂ) • Y.map Complex.ofReal := by
    ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
  -- .map ofReal is the same as ofRealHom.mapMatrix
  change Complex.ofRealHom.mapMatrix (exp (s • Y)) = _
  rw [h1, h2]

/-- **Single-generator identity theorem.** For Y ∈ so(1,d;ℝ) and z ∈ FT,
    the function t ↦ F(exp(t · Y_ℂ) · z) equals F(z) for t near 0 in ℂ.

    Proof: The composed function g(t) = F(exp(tX)·z) - F(z) is:
    1. DifferentiableOn on the open set {t : exp(tX)·z ∈ FT}
    2. AnalyticAt 0 (by DifferentiableOn.analyticAt for ℂ-valued functions)
    3. Zero for real t (by real Lorentz invariance via the bridge lemma)
    4. Zero near 0 (by the 1D identity theorem) -/
private theorem single_generator_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : IsInLorentzAlgebra d Y)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) ∈
          ForwardTube d n →
      F (fun k μ =>
        ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  set X := Y.map Complex.ofReal with hX_def
  -- The action map
  set action : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t k μ => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν with haction_def
  -- The domain U = {t : action(t) ∈ FT} is open
  set U := {t : ℂ | action t ∈ ForwardTube d n} with hU_def
  have hU_open : IsOpen U :=
    isOpen_forwardTube.preimage (differentiable_expAction X z).continuous
  -- 0 ∈ U since action(0) = z ∈ FT
  have h0U : (0 : ℂ) ∈ U := by
    simp only [hU_def, haction_def, Set.mem_setOf_eq]
    convert hz using 2; ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ]
  -- Define g(t) = F(action(t)) - F(z)
  set g : ℂ → ℂ := fun t => F (action t) - F z with hg_def
  -- g is DifferentiableOn on U
  have hg_diff : DifferentiableOn ℂ g U := by
    apply DifferentiableOn.sub
    · exact hF_holo.comp (differentiable_expAction X z).differentiableOn (fun t ht => ht)
    · exact differentiableOn_const _
  -- g is AnalyticAt 0
  have hg_analytic : AnalyticAt ℂ g 0 :=
    hg_diff.analyticAt (hU_open.mem_nhds h0U)
  -- g(s) = 0 for s ∈ ℝ (real Lorentz invariance)
  have hg_real : ∀ s : ℝ, (s : ℂ) ∈ U → g (s : ℂ) = 0 := by
    intro s hs
    simp only [hg_def, sub_eq_zero]
    -- exp((s:ℂ) • X) = (exp(s • Y)).map ofReal
    have hbridge := exp_map_ofReal_bridge Y s
    -- The entries match: (exp((s:ℂ) • X)) μ ν = ((exp(s • Y)) μ ν : ℂ)
    have hentry : ∀ μ ν : Fin (d + 1),
        (exp ((s : ℂ) • X) : Matrix _ _ ℂ) μ ν =
        ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) := by
      intro μ ν
      have : (exp (s • Y) : Matrix _ _ ℝ).map Complex.ofReal = exp ((s : ℂ) • X) := hbridge
      exact (congr_fun (congr_fun this μ) ν).symm
    -- Rewrite the action to use real Lorentz entries
    have haction_eq : action (s : ℂ) =
        fun k μ => ∑ ν, ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) * z k ν := by
      ext k μ; simp only [haction_def]; congr 1; ext ν; rw [hentry]
    rw [haction_eq]
    -- Apply real Lorentz invariance
    exact hF_real_inv (expLorentz d (s • Y) (isInLorentzAlgebra_smul d hY s)) z hz
  -- g = 0 frequently near 0 in 𝓝[≠] 0
  have hg_freq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    intro ⟨U', hU'_open, h0_mem, hU'_sub⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_mem
    -- Pick a small positive real number s ∈ U' ∩ {0}ᶜ ∩ U
    obtain ⟨r', hr'_pos, hr'_sub⟩ := Metric.isOpen_iff.mp hU_open 0 h0U
    set s := min (r / 2) (r' / 2) with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have hs_in_U' : (s : ℂ) ∈ U' := hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_left (r / 2) (r' / 2)])
    have hs_in_U : (s : ℂ) ∈ U := hr'_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_right (r / 2) (r' / 2)])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_in_U)
  -- By the identity theorem: g = 0 on a neighborhood of 0
  have hg_zero := hg_analytic.frequently_zero_iff_eventually_zero.mp hg_freq
  -- Translate: F(action(t)) = F(z) eventually near 0
  exact hg_zero.mono (fun t ht _ => by
    simp only [hg_def, sub_eq_zero] at ht; exact ht)

/-! ### Infrastructure for the identity theorem proof -/

/-- The real part of a complex matrix (entry-wise). -/
private def reMatrix (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => (X i j).re

/-- The imaginary part of a complex matrix (entry-wise). -/
private def imMatrix (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => (X i j).im

/-- A complex matrix decomposes as Re(X).map ofReal + I • Im(X).map ofReal. -/
private theorem matrix_re_im_decomp (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    X = (reMatrix X).map Complex.ofReal + Complex.I • (imMatrix X).map Complex.ofReal := by
  ext i j
  simp only [reMatrix, imMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [mul_comm]; exact (Complex.re_add_im (X i j)).symm

/-- If X ∈ so(1,d;ℂ) then Re(X) ∈ so(1,d;ℝ).
    Proof: Xᵀηℂ + ηℂX = 0 with ηℂ real → taking real parts gives
    Re(X)ᵀη + ηRe(X) = 0 since η = diag(±1) is real. -/
private theorem reMatrix_isInLorentzAlgebra
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    IsInLorentzAlgebra d (reMatrix X) := by
  -- hX : Xᵀ * ηℂ + ηℂ * X = 0 where ηℂ = diag(minkowskiSignature)
  -- Convert to explicit form with Matrix.diagonal
  have hX' : X.transpose * Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) +
      Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) * X = 0 := hX
  -- Work entry-wise
  unfold IsInLorentzAlgebra
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    LorentzLieGroup.minkowskiMatrix, Matrix.diagonal_apply, reMatrix, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  -- Goal: (X j i).re * η j + η i * (X i j).re = 0
  -- Extract entry (i,j) from hX' and take real part
  have hij := congr_fun (congr_fun hX' i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hij
  -- hij : X j i * ↑(η j) + ↑(η i) * X i j = 0. Take Re.
  have hre := congr_arg Complex.re hij
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_mul, Complex.zero_re] at hre
  exact hre

/-- If X ∈ so(1,d;ℂ) then Im(X) ∈ so(1,d;ℝ). Same argument as for Re(X),
    taking imaginary parts instead. -/
private theorem imMatrix_isInLorentzAlgebra
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
    IsInLorentzAlgebra d (imMatrix X) := by
  have hX' : X.transpose * Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) +
      Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ)) * X = 0 := hX
  unfold IsInLorentzAlgebra
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    LorentzLieGroup.minkowskiMatrix, Matrix.diagonal_apply, imMatrix, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hij := congr_fun (congr_fun hX' i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.zero_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hij
  -- hij : X j i * ↑(η j) + ↑(η i) * X i j = 0. Take Im.
  have him := congr_arg Complex.im hij
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, Complex.zero_im] at him
  exact him

/-- The ℓ∞ operator norm of Re(X).map ofReal is bounded by the norm of X.
    Entry-wise |Re(z)| ≤ |z|, so each row sum is bounded. -/
private theorem norm_reMatrix_map_le (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖(reMatrix X).map Complex.ofReal‖ ≤ ‖X‖ := by
  simp only [← coe_nnnorm, NNReal.coe_le_coe]
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  apply Finset.sup_le
  intro i _
  apply le_trans _ (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.map_apply, reMatrix]
  rw [show (Complex.ofReal (X i j).re : ℂ) = ((X i j).re : ℂ) from rfl]
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Complex.norm_real]
  exact Complex.abs_re_le_norm (X i j)

/-- The ℓ∞ operator norm of Im(X).map ofReal is bounded by the norm of X.
    Entry-wise |Im(z)| ≤ |z|, so each row sum is bounded. -/
private theorem norm_imMatrix_map_le (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖(imMatrix X).map Complex.ofReal‖ ≤ ‖X‖ := by
  simp only [← coe_nnnorm, NNReal.coe_le_coe]
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  apply Finset.sup_le
  intro i _
  apply le_trans _ (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.map_apply, imMatrix]
  rw [show (Complex.ofReal (X i j).im : ℂ) = ((X i j).im : ℂ) from rfl]
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Complex.norm_real]
  exact Complex.abs_im_le_norm (X i j)

set_option maxHeartbeats 800000 in
/-- **Exponential neighborhood lemma.** The exponential map from the Lie algebra
    so(1,d;ℂ) covers a neighborhood of 1 in the complex Lorentz group, with
    a norm bound on the Lie algebra element.

    Uses `hasStrictFDerivAt_exp_zero` (derivative of exp at 0 is the identity)
    + `HasStrictFDerivAt.map_nhds_eq_of_surj` (IFT: exp maps neighborhoods of 0
    onto neighborhoods of 1) + algebraic argument (log of Lorentz ∈ Lie algebra). -/
private theorem exp_nhd_of_one (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∃ (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ),
        ComplexLorentzGroup.IsInLieAlgebra X ∧ Λ.val = NormedSpace.exp X ∧ ‖X‖ < ε := by
  set E := Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  -- Use mexp for the matrix exponential to avoid conflict with Complex.exp
  let mexp : E → E := NormedSpace.exp
  -- Step 1: IFT for exp at 0.
  have hexp_strict : HasStrictFDerivAt mexp
      ((ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E)) (0 : E) := by
    show HasStrictFDerivAt NormedSpace.exp _ _
    convert hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := E) using 1
  -- Get partial homeomorphism: exp is injective on source S, with 0 ∈ S.
  set Φ := hexp_strict.toOpenPartialHomeomorph mexp
  have h0_mem : (0 : E) ∈ Φ.source := hexp_strict.mem_toOpenPartialHomeomorph_source
  have hS_nhds : Φ.source ∈ 𝓝 (0 : E) := Φ.open_source.mem_nhds h0_mem
  have hinj : Set.InjOn mexp Φ.source := Φ.injOn
  -- Step 2: Filter conditions for the injectivity argument.
  set η := ComplexLorentzGroup.ηℂ (d := d)
  -- Negation sends 0 to 0 and is continuous → Φ.source preimage near 0
  have hneg_nhds : ∀ᶠ X in 𝓝 (0 : E), -X ∈ Φ.source :=
    continuous_neg.continuousAt.preimage_mem_nhds (by rw [neg_zero]; exact hS_nhds)
  -- η-conjugate-transpose sends 0 to 0 and is continuous
  have hconj_cont : Continuous (fun X : E => η * X.transpose * η) :=
    (continuous_const.mul (Continuous.matrix_transpose continuous_id)).mul continuous_const
  have hconj_nhds : ∀ᶠ X in 𝓝 (0 : E), η * X.transpose * η ∈ Φ.source :=
    hconj_cont.continuousAt.preimage_mem_nhds
      (by simp only [Matrix.transpose_zero, mul_zero, zero_mul]; exact hS_nhds)
  -- ‖X‖ < ε near 0
  have hball : ∀ᶠ X in 𝓝 (0 : E), ‖X‖ < ε :=
    Metric.eventually_nhds_iff.mpr ⟨ε, hε, fun _ hx => by rwa [dist_zero_right] at hx⟩
  -- Combine all conditions
  have hS_ev : ∀ᶠ X in 𝓝 (0 : E), X ∈ Φ.source := hS_nhds
  have h_good : ∀ᶠ X in 𝓝 (0 : E),
      X ∈ Φ.source ∧ -X ∈ Φ.source ∧ η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε :=
    hS_ev.and (hneg_nhds.and (hconj_nhds.and hball))
  -- Step 3: exp maps nhds 0 → nhds 1 (surjectivity).
  have hmap : map mexp (𝓝 0) = 𝓝 (1 : E) := by
    have hsurj : (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E).range = ⊤ := by
      ext x; exact ⟨fun _ => trivial, fun _ => ⟨x, by simp⟩⟩
    have := hexp_strict.map_nhds_eq_of_surj hsurj
    rwa [show mexp 0 = (1 : E) from NormedSpace.exp_zero] at this
  -- Push the good set through mexp to get a nhds 1 set in matrices
  have h_mat : ∀ᶠ M in 𝓝 (1 : E),
      ∃ X : E, mexp X = M ∧ X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε := by
    rw [← hmap, Filter.eventually_map]
    exact h_good.mono fun X ⟨hXS, hnXS, hcXS, hXε⟩ =>
      ⟨X, rfl, hXS, hnXS, hcXS, hXε⟩
  -- Step 4: Pull back to the ComplexLorentzGroup topology via continuous val.
  have h_grp : ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∃ X : E, mexp X = Λ.val ∧ X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε := by
    have hca : ContinuousAt (fun Λ : ComplexLorentzGroup d => Λ.val) 1 :=
      ComplexLorentzGroup.continuous_val.continuousAt
    rw [ContinuousAt, ComplexLorentzGroup.one_val'] at hca
    exact hca.eventually h_mat
  -- Step 5: For each such Λ, prove the Lie algebra condition using injectivity.
  apply h_grp.mono
  intro Λ ⟨X, hexpX, hXS, hnXS, hcXS, hXε⟩
  refine ⟨X, ?_, hexpX.symm, hXε⟩
  -- Need: X ∈ so(1,d;ℂ), i.e., Xᵀ * η + η * X = 0
  -- Key algebra: mexp(η Xᵀ η) = η mexp(Xᵀ) η = η (mexp X)ᵀ η = Λ⁻¹.val = mexp(-X)
  -- By injectivity on S: η Xᵀ η = -X, hence Xᵀ η + η X = 0
  -- mexp(η Xᵀ η) = η mexp(Xᵀ) η (by exp_units_conj with η² = 1)
  have h1 : mexp (η * X.transpose * η) = η * mexp X.transpose * η := by
    show NormedSpace.exp (η * X.transpose * η) = η * NormedSpace.exp X.transpose * η
    -- ↑ηℂ_unit = η and ↑(ηℂ_unit⁻¹) = η definitionally (since η² = 1)
    exact NormedSpace.exp_units_conj (ComplexLorentzGroup.ηℂ_unit) X.transpose
  -- mexp(Xᵀ) = (mexp X)ᵀ
  have h2 : mexp X.transpose = (mexp X).transpose :=
    show NormedSpace.exp X.transpose = (NormedSpace.exp X).transpose from
      Matrix.exp_transpose X
  -- The group inverse: (Λ⁻¹).val = η Λ.valᵀ η
  have h3 : (Λ⁻¹).val = η * Λ.val.transpose * η := rfl
  -- Combine: mexp(η Xᵀ η) = η (mexp X)ᵀ η = Λ⁻¹.val
  have h5 : mexp (η * X.transpose * η) = (Λ⁻¹).val := by
    rw [h1, h2, h3, hexpX]
  -- Show (Λ⁻¹).val = mexp(-X) via left-inverse uniqueness
  have h6 : (Λ⁻¹).val = mexp (-X) := by
    have hinvmul : (Λ⁻¹).val * Λ.val = 1 := by
      have : (Λ⁻¹ * Λ).val = 1 := by rw [inv_mul_cancel]; rfl
      rwa [ComplexLorentzGroup.mul_val] at this
    have hexp_rinv : mexp X * mexp (-X) = 1 := by
      show NormedSpace.exp X * NormedSpace.exp (-X) = 1
      rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl X))]
      simp [NormedSpace.exp_zero]
    calc (Λ⁻¹).val
        = (Λ⁻¹).val * (mexp X * mexp (-X)) := by rw [hexp_rinv, mul_one]
      _ = (Λ⁻¹).val * mexp X * mexp (-X) := by rw [mul_assoc]
      _ = (Λ⁻¹).val * Λ.val * mexp (-X) := by rw [hexpX]
      _ = mexp (-X) := by rw [hinvmul, one_mul]
  -- Therefore: mexp(η Xᵀ η) = mexp(-X)
  have h7 : mexp (η * X.transpose * η) = mexp (-X) := by rw [h5, h6]
  -- By injectivity: η Xᵀ η = -X
  have h8 : η * X.transpose * η = -X := hinj hcXS hnXS h7
  -- Deduce: Xᵀ η + η X = 0
  show ComplexLorentzGroup.IsInLieAlgebra X
  unfold ComplexLorentzGroup.IsInLieAlgebra
  -- From h8: η Xᵀ η = -X → multiply by η on left: η²Xᵀη = -ηX → Xᵀη = -ηX
  have h9 : X.transpose * η = -(η * X) := by
    calc X.transpose * η
        = 1 * X.transpose * η := by rw [Matrix.one_mul]
      _ = (η * η) * X.transpose * η := by rw [ComplexLorentzGroup.ηℂ_sq (d := d)]
      _ = η * (η * X.transpose * η) := by simp only [Matrix.mul_assoc]
      _ = η * (-X) := by rw [h8]
      _ = -(η * X) := Matrix.mul_neg η X
  -- Xᵀη + ηX = -ηX + ηX = 0
  rw [h9]; exact neg_add_cancel _

/-- **Full-domain single-generator identity theorem.** For Y ∈ so(1,d;ℝ),
    the function F(exp(t·Y_ℂ)·z) = F(z) for ALL t in any preconnected
    open subset of {t : exp(t·Y_ℂ)·z ∈ FT} containing 0.

    Upgrade of `single_generator_invariance` from "eventually near 0"
    to "on the whole connected domain", using the Mathlib identity theorem
    `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`. -/
private theorem full_domain_generator_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : IsInLorentzAlgebra d Y)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_pre : IsPreconnected U)
    (h0U : (0 : ℂ) ∈ U)
    (hU_sub : ∀ t ∈ U, (fun k (μ : Fin (d + 1)) =>
      ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n) :
    ∀ t ∈ U, F (fun k μ =>
      ∑ ν, (exp (t • Y.map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  set X := Y.map Complex.ofReal with hX_def
  set action : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun t k μ => ∑ ν, (exp (t • X) : Matrix _ _ ℂ) μ ν * z k ν with haction_def
  set g : ℂ → ℂ := fun t => F (action t) - F z with hg_def
  -- g is DifferentiableOn on U
  have hg_diff : DifferentiableOn ℂ g U := by
    apply DifferentiableOn.sub
    · exact hF_holo.comp (differentiable_expAction X z).differentiableOn
        (fun t ht => hU_sub t ht)
    · exact differentiableOn_const _
  -- g is AnalyticOnNhd on U
  have hg_analytic : AnalyticOnNhd ℂ g U :=
    hg_diff.analyticOnNhd hU_open
  -- g(s) = 0 for real s near 0 in U
  have hg_real : ∀ s : ℝ, (s : ℂ) ∈ U → g (s : ℂ) = 0 := by
    intro s hs
    simp only [hg_def, sub_eq_zero]
    have hbridge := exp_map_ofReal_bridge Y s
    have hentry : ∀ μ ν : Fin (d + 1),
        (exp ((s : ℂ) • X) : Matrix _ _ ℂ) μ ν =
        ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) := by
      intro μ ν
      simp only [hX_def, ← hbridge, Matrix.map_apply]
    have haction_eq : action (s : ℂ) =
        fun k μ => ∑ ν, ((exp (s • Y) : Matrix _ _ ℝ) μ ν : ℂ) * z k ν := by
      ext k μ; simp only [haction_def]; congr 1; ext ν; rw [hentry]
    rw [haction_eq]
    exact hF_real_inv (expLorentz d (s • Y) (isInLorentzAlgebra_smul d hY s)) z hz
  -- g = 0 frequently near 0 in 𝓝[≠] 0
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
        abs_of_pos hs_pos]; linarith [min_le_left (r / 2) (r' / 2)])
    have hs_in_U : (s : ℂ) ∈ U := hr'_sub (by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs_pos]; linarith [min_le_right (r / 2) (r' / 2)])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_in_U)
  -- By the identity theorem: g = 0 on all of U
  have hg_zero := hg_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hU_pre h0U hg_freq
  -- Translate back to F
  intro t ht
  have := hg_zero ht
  simp only [hg_def, Pi.zero_apply, sub_eq_zero] at this
  exact this

set_option maxHeartbeats 400000 in
/-- Helper: for ‖X₁‖ ≤ ‖X‖, ‖X₂‖ ≤ ‖X‖, ‖X‖ < δ/7, and s ∈ ball(0,R),
    we get ‖X₁ + s • X₂‖ < δ (when R ≤ 2). -/
private theorem norm_affine_combination_lt
    (X₁ X₂ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX₁_le : ‖X₁‖ ≤ ‖X‖) (hX₂_le : ‖X₂‖ ≤ ‖X‖)
    {δ : ℝ} (hsmall : ‖X‖ < δ / 7) {s : ℂ} (hs : ‖s‖ < 2) :
    ‖X₁ + s • X₂‖ < δ :=
  calc ‖X₁ + s • X₂‖ ≤ ‖X₁‖ + ‖s • X₂‖ := norm_add_le _ _
    _ ≤ ‖X₁‖ + ‖s‖ * ‖X₂‖ := add_le_add (le_refl _) (norm_smul_le s X₂)
    _ ≤ ‖X‖ + 2 * ‖X‖ := add_le_add hX₁_le
        (mul_le_mul (le_of_lt hs) hX₂_le (norm_nonneg _) (by positivity))
    _ = 3 * ‖X‖ := by ring
    _ < δ := by nlinarith [norm_nonneg X]

set_option maxHeartbeats 400000 in
/-- Helper: for ‖s‖ < 2, ‖t‖ < 2, and ‖X‖ < δ/7:
    ‖t • (X₁ + s • X₂)‖ < δ. -/
private theorem norm_tsmul_affine_lt
    (X₁ X₂ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX₁_le : ‖X₁‖ ≤ ‖X‖) (hX₂_le : ‖X₂‖ ≤ ‖X‖)
    {δ : ℝ} (hsmall : ‖X‖ < δ / 7)
    {s : ℂ} (hs : ‖s‖ < 2) {t : ℂ} (ht : ‖t‖ < 2) :
    ‖t • (X₁ + s • X₂)‖ < δ :=
  calc ‖t • (X₁ + s • X₂)‖ ≤ ‖t‖ * ‖X₁ + s • X₂‖ := norm_smul_le _ _
    _ ≤ 2 * (3 * ‖X‖) := by
        apply mul_le_mul (le_of_lt ht)
        · calc ‖X₁ + s • X₂‖ ≤ ‖X₁‖ + ‖s • X₂‖ := norm_add_le _ _
            _ ≤ ‖X₁‖ + ‖s‖ * ‖X₂‖ :=
                add_le_add (le_refl _) (norm_smul_le s X₂)
            _ ≤ ‖X‖ + 2 * ‖X‖ := add_le_add hX₁_le
                (mul_le_mul (le_of_lt hs) hX₂_le (norm_nonneg _) (by positivity))
            _ = 3 * ‖X‖ := by ring
        · positivity
        · positivity
    _ = 6 * ‖X‖ := by ring
    _ < δ := by nlinarith [norm_nonneg X]

set_option maxHeartbeats 800000 in
/-- Core analytic argument for near-identity invariance:
    Given δ such that exp(A)·z ∈ FT for ‖A‖ < δ, and X ∈ so(1,d;ℂ) with ‖X‖ < δ/7,
    show F(exp(X)·z) = F(z). Extracted as a separate lemma for reuse in the
    uniform version. -/
private theorem near_identity_core (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    {z : Fin n → Fin (d + 1) → ℂ} (hz : z ∈ ForwardTube d n)
    {δ : ℝ} (_hδ_pos : 0 < δ)
    (hA_in_FT : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < δ →
        (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν) ∈
          ForwardTube d n)
    {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX_lie : ComplexLorentzGroup.IsInLieAlgebra X) (hX_small : ‖X‖ < δ / 7) :
    F (fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
  -- === Decompose X = X₁ + I•X₂ ===
  set Y₁ := reMatrix X
  set Y₂ := imMatrix X
  set X₁ := Y₁.map Complex.ofReal with hX₁_def
  set X₂ := Y₂.map Complex.ofReal with hX₂_def
  have hY₁_lie := reMatrix_isInLorentzAlgebra hX_lie
  have hY₂_lie := imMatrix_isInLorentzAlgebra hX_lie
  have hX_decomp : X = X₁ + Complex.I • X₂ := matrix_re_im_decomp X
  -- Norm bounds: ‖X₁‖ ≤ ‖X‖, ‖X₂‖ ≤ ‖X‖
  have hX₁_le : ‖X₁‖ ≤ ‖X‖ := norm_reMatrix_map_le X
  have hX₂_le : ‖X₂‖ ≤ ‖X‖ := norm_imMatrix_map_le X
  have hsmall : ‖X‖ < δ / 7 := hX_small
  -- Helper: for s ∈ ball(0,2), exp(X₁ + s•X₂)·z ∈ FT
  have hball_FT : ∀ s ∈ Metric.ball (0 : ℂ) 2,
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp (X₁ + s • X₂) : Matrix _ _ ℂ) μ ν * z k ν) ∈ ForwardTube d n := by
    intro s hs
    exact hA_in_FT _ (norm_affine_combination_lt X₁ X₂ X hX₁_le hX₂_le hsmall
      (by rwa [Metric.mem_ball, dist_zero_right] at hs))
  -- For real s, X₁ + (s:ℂ)•X₂ = (Y₁ + s•Y₂).map ofReal
  have hreal_param : ∀ s : ℝ, X₁ + (s : ℂ) • X₂ = (Y₁ + s • Y₂).map Complex.ofReal := by
    intro s; ext i j
    simp only [hX₁_def, hX₂_def, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
      Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
  -- === Step 1: F(exp(X₁ + s•X₂)·z) = F(z) for real s ∈ ball(0,2) ===
  have hstep1 : ∀ s : ℝ, ‖(s : ℂ)‖ < 2 →
      F (fun k μ => ∑ ν, (exp (X₁ + (s : ℂ) • X₂) : Matrix _ _ ℂ) μ ν * z k ν) = F z := by
    intro s hs
    rw [hreal_param s]
    have hgen_lie : IsInLorentzAlgebra d (Y₁ + s • Y₂) := by
      unfold IsInLorentzAlgebra at hY₁_lie hY₂_lie ⊢
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul,
        Matrix.mul_add, Matrix.mul_smul]
      rw [add_add_add_comm, ← smul_add, hY₁_lie, hY₂_lie, smul_zero, add_zero]
    have hball_sub : ∀ t ∈ Metric.ball (0 : ℂ) 2,
        (fun k (μ : Fin (d + 1)) => ∑ ν,
          (exp (t • (Y₁ + s • Y₂).map Complex.ofReal) : Matrix _ _ ℂ) μ ν * z k ν) ∈
            ForwardTube d n := by
      intro t ht
      apply hA_in_FT
      have h_eq : (Y₁ + s • Y₂).map Complex.ofReal = X₁ + (↑s : ℂ) • X₂ :=
        (hreal_param s).symm
      rw [h_eq]
      exact norm_tsmul_affine_lt X₁ X₂ X hX₁_le hX₂_le hsmall hs
        (by rwa [Metric.mem_ball, dist_zero_right] at ht)
    have h1_in_ball : (1 : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]; norm_num
    have := full_domain_generator_invariance n F hF_holo hF_real_inv
      (Y₁ + s • Y₂) hgen_lie z hz Metric.isOpen_ball
      (convex_ball _ _).isPreconnected (Metric.mem_ball_self (by positivity : (0 : ℝ) < 2))
      hball_sub 1 h1_in_ball
    simp only [one_smul] at this
    exact this
  -- === Step 2: Identity theorem in s on ball(0,2) ===
  set action_s : ℂ → Fin n → Fin (d + 1) → ℂ :=
    fun s k μ => ∑ ν, (exp (X₁ + s • X₂) : Matrix _ _ ℂ) μ ν * z k ν with haction_s_def
  set g : ℂ → ℂ := fun s => F (action_s s) - F z with hg_def
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 2) := by
    apply DifferentiableOn.sub
    · apply hF_holo.comp _ hball_FT
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
    intro s hs; simp only [hg_def, sub_eq_zero]; exact hstep1 s hs
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
        abs_of_pos hs_pos]; linarith [min_le_left (r / 2) 1])
    exact hU'_sub ⟨hs_in_U', hs_ne⟩ (hg_real s hs_norm)
  have hg_zero := hg_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball _ _).isPreconnected (Metric.mem_ball_self (by positivity : (0 : ℝ) < 2)) hg_freq
  -- === Step 3: Evaluate at s = I ===
  have hI_in_ball : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num
  have hgI := hg_zero hI_in_ball
  simp only [hg_def, Pi.zero_apply, sub_eq_zero] at hgI
  rw [hX_decomp]
  exact hgI

/-- **Near-identity invariance.** If F is holomorphic on the forward tube and
    real-Lorentz invariant, then F is invariant under complex Lorentz transformations
    in a neighborhood of 1 (when the image stays in the forward tube). -/
theorem near_identity_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  -- === Step 0: Continuity gives δ such that ‖A‖ < δ → exp(A)·z ∈ FT ===
  have hexp_action_cont : Continuous (fun A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν)) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    apply continuous_finset_sum; intro ν _
    refine Continuous.mul ?_ continuous_const
    exact (continuous_apply ν).comp ((continuous_apply μ).comp NormedSpace.exp_continuous)
  have h0_in_FT : (fun k (μ : Fin (d + 1)) =>
      ∑ ν, (exp (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) μ ν * z k ν) ∈ ForwardTube d n := by
    convert hz using 2; ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_forwardTube.preimage hexp_action_cont) 0 h0_in_FT
  -- Key: for ‖A‖ < δ, exp(A)·z ∈ FT
  have hA_in_FT : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < δ →
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν) ∈
        ForwardTube d n :=
    fun A hA => hδ_sub (by rwa [Metric.mem_ball, dist_zero_right])
  -- === Step 0.5: Use exp_nhd_of_one with norm bound δ/7 ===
  apply (exp_nhd_of_one (δ / 7) (by positivity)).mono
  intro Λ ⟨X, hX_lie, hΛ_eq, hX_small⟩ hΛz
  -- Λ.val = exp X, ‖X‖ < δ/7, X ∈ so(1,d;ℂ)
  -- Goal: F(complexLorentzAction Λ z) = F z
  -- Rewrite action in terms of exp X
  have haction_eq : complexLorentzAction Λ z =
      fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * z k ν := by
    ext k μ
    simp only [complexLorentzAction, complexLorentzVectorAction]
    apply Finset.sum_congr rfl
    intro ν _
    rw [← hΛ_eq]
  rw [haction_eq]
  exact near_identity_core n F hF_holo hF_real_inv hz hδ_pos hA_in_FT hX_lie hX_small

set_option maxHeartbeats 800000 in
/-- **Uniform near-identity invariance.** For z₀ ∈ FT, there exist a neighborhood U
    of z₀ and a neighborhood V of 1 ∈ G such that for all w ∈ U ∩ FT and Λ ∈ V:
    F(Λ·w) = F(w) (when Λ·w ∈ FT). Uses joint continuity of (A, w) ↦ exp(A)·w
    to get a uniform δ, then applies `near_identity_core`. -/
theorem uniform_near_identity_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z₀ : Fin n → Fin (d + 1) → ℂ) (hz₀ : z₀ ∈ ForwardTube d n) :
    ∃ U ∈ 𝓝 z₀, ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∀ w ∈ U, w ∈ ForwardTube d n →
        complexLorentzAction Λ w ∈ ForwardTube d n →
        F (complexLorentzAction Λ w) = F w := by
  -- Joint continuity: the map (A, w) ↦ exp(A)·w is continuous
  have hΦ_cont : Continuous (fun (p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ ×
      (Fin n → Fin (d + 1) → ℂ)) =>
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (exp p.1 : Matrix _ _ ℂ) μ ν * p.2 k ν)) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    apply continuous_finset_sum; intro ν _
    refine Continuous.mul ?_ ?_
    · -- Continuous (fun a => (exp a.1) μ ν)
      have h_exp_fst : Continuous (fun a : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ ×
          (Fin n → Fin (d + 1) → ℂ) => exp a.1) :=
        NormedSpace.exp_continuous.comp continuous_fst
      have h_entry : Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M μ ν) :=
        (continuous_apply ν).comp (continuous_apply μ)
      exact h_entry.comp h_exp_fst
    · -- Continuous (fun a => a.2 k ν)
      have h_entry2 : Continuous (fun f : Fin n → Fin (d + 1) → ℂ => f k ν) :=
        (continuous_apply ν).comp (continuous_apply k)
      exact h_entry2.comp continuous_snd
  -- At (0, z₀): exp(0)·z₀ = z₀ ∈ FT
  have h0z₀ : (fun k (μ : Fin (d + 1)) =>
      ∑ ν, (exp (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : Matrix _ _ ℂ) μ ν * z₀ k ν) ∈
        ForwardTube d n := by
    convert hz₀ using 2; ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  -- Get ε > 0 such that ‖A‖ < ε ∧ ‖w - z₀‖ < ε → exp(A)·w ∈ FT
  obtain ⟨ε, hε_pos, hε_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_forwardTube.preimage hΦ_cont) (0, z₀) h0z₀
  -- U = B(z₀, ε)
  refine ⟨Metric.ball z₀ ε, Metric.ball_mem_nhds z₀ hε_pos, ?_⟩
  -- For Λ ∈ exp_nhd_of_one(ε/7) and w ∈ B(z₀, ε) ∩ FT: apply near_identity_core
  apply (exp_nhd_of_one (ε / 7) (by positivity)).mono
  intro Λ ⟨X, hX_lie, hΛ_eq, hX_small⟩ w hw_ball hw_FT hΛw
  -- Rewrite action in terms of exp X
  have haction_eq : complexLorentzAction Λ w =
      fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * w k ν := by
    ext k μ
    simp only [complexLorentzAction, complexLorentzVectorAction]
    apply Finset.sum_congr rfl
    intro ν _
    rw [← hΛ_eq]
  rw [haction_eq]
  -- For w ∈ B(z₀, ε): ‖A‖ < ε → exp(A)·w ∈ FT
  have hA_in_FT_w : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < ε →
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * w k ν) ∈
        ForwardTube d n := by
    intro A hA
    have h_mem : (A, w) ∈ Metric.ball (0, z₀) ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨by rwa [dist_zero_right], Metric.mem_ball.mp hw_ball⟩
    exact hε_sub h_mem
  exact near_identity_core n F hF_holo hF_real_inv hw_FT hε_pos hA_in_FT_w hX_lie hX_small

/- NOTE (2026-02-25): the proof now runs a global T-set clopen argument on
   `G`, but still uses preconnectedness of the nonempty-domain set
   `U = {Λ | ∃ w ∈ FT, Λ·w ∈ FT}`. In the current implementation that reduces
   to `orbitSet_isPreconnected` via `isPreconnected_sUnion`. -/

/-- **Identity theorem on open convex domains via 1D line restriction.**
    If f is ℂ-differentiable on an open convex set D and f =ᶠ 0 near some z₁ ∈ D,
    then f ≡ 0 on D. Proof: for w ∈ D, restrict f to the complex line l(t) = z₁ + t(w - z₁).
    The pullback f ∘ l : ℂ → ℂ is holomorphic on l⁻¹(D) (open, convex, thus connected),
    vanishes near t = 0, hence vanishes at t = 1 by the 1D identity theorem (Cauchy). -/
theorem eq_zero_on_convex_of_eventuallyEq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set E} (hD_open : IsOpen D) (hD_conv : Convex ℝ D)
    {f : E → ℂ} (hf : DifferentiableOn ℂ f D)
    {z₁ : E} (hz₁ : z₁ ∈ D) (hf_zero : f =ᶠ[𝓝 z₁] 0) :
    ∀ w ∈ D, f w = 0 := by
  intro w hw
  -- Complex line from z₁ to w
  let l : ℂ → E := fun t => z₁ + t • (w - z₁)
  have hl_diff : Differentiable ℂ l :=
    (differentiable_const z₁).add (differentiable_id.smul (differentiable_const (w - z₁)))
  -- S = l⁻¹(D) is open
  have hS_open : IsOpen (l ⁻¹' D) := hD_open.preimage hl_diff.continuous
  -- S is ℝ-convex (l is ℝ-affine, D is ℝ-convex)
  have hS_conv : Convex ℝ (l ⁻¹' D) := by
    intro s₁ hs₁ s₂ hs₂ a b ha hb hab
    show l (a • s₁ + b • s₂) ∈ D
    have key : l (a • s₁ + b • s₂) = a • l s₁ + b • l s₂ := by
      show z₁ + (a • s₁ + b • s₂) • (w - z₁) =
        a • (z₁ + s₁ • (w - z₁)) + b • (z₁ + s₂ • (w - z₁))
      rw [add_smul (a • s₁ : ℂ) (b • s₂ : ℂ) (w - z₁),
          smul_assoc (a : ℝ) (s₁ : ℂ) (w - z₁ : E),
          smul_assoc (b : ℝ) (s₂ : ℂ) (w - z₁ : E),
          smul_add (a : ℝ) (z₁ : E) (s₁ • (w - z₁)),
          smul_add (b : ℝ) (z₁ : E) (s₂ • (w - z₁))]
      nth_rw 1 [show z₁ = a • z₁ + b • (z₁ : E) from by rw [← add_smul, hab, one_smul]]
      abel
    rw [key]; exact hD_conv hs₁ hs₂ ha hb hab
  -- 0 ∈ S (l(0) = z₁ ∈ D) and 1 ∈ S (l(1) = w ∈ D)
  have h0S : (0 : ℂ) ∈ l ⁻¹' D := by
    show l 0 ∈ D; simp only [l, zero_smul, add_zero]; exact hz₁
  have h1S : (1 : ℂ) ∈ l ⁻¹' D := by
    show l 1 ∈ D; change z₁ + 1 • (w - z₁) ∈ D; rw [one_smul]
    convert hw using 1; abel
  -- f ∘ l is holomorphic on S hence analytic (1D Cauchy integral formula)
  have hfl_analytic : AnalyticOnNhd ℂ (f ∘ l) (l ⁻¹' D) :=
    (hf.comp hl_diff.differentiableOn (Set.mapsTo_preimage l D)).analyticOnNhd hS_open
  -- f ∘ l vanishes near t = 0 (since l(0) = z₁ and f =ᶠ 0 near z₁)
  have hfl_zero : (f ∘ l) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    have : Tendsto l (𝓝 0) (𝓝 z₁) := by
      convert hl_diff.continuous.continuousAt.tendsto using 1
      simp only [l, zero_smul, add_zero]
    exact this.eventually hf_zero
  -- By identity theorem: f ∘ l ≡ 0 on S (preconnected since convex)
  have h_eq := hfl_analytic.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hS_conv.isPreconnected h0S hfl_zero
  -- f(w) = (f ∘ l)(1) = 0
  have h_val := h_eq h1S
  simp only [Function.comp] at h_val
  have h_lw : l 1 = w := by show z₁ + (1 : ℂ) • (w - z₁) = w; rw [one_smul]; abel
  rwa [h_lw] at h_val

/-- For any Λ₀ in the orbit set of w, there is a neighborhood of Λ₀ in the group
    such that any element in the neighborhood can be connected to Λ₀ by a path
    staying entirely within the orbit set.

    The proof uses the exponential map: for Λ₁ near 1, write Λ₀⁻¹ * Λ = expLieAlg(X)
    for small X (via `exp_nhd_of_one`). The path t ↦ Λ₀ * expLieAlg(tX) stays in
    the orbit set because for small ‖X‖, `expLieAlg(tX)·w` stays close to `w`,
    keeping `Λ₀·(expLieAlg(tX)·w)` close to `Λ₀·w ∈ FT` (open). -/
private lemma orbitSet_locallyPathConnected (w : Fin n → Fin (d + 1) → ℂ)
    (_hw : w ∈ ForwardTube d n) (Λ₀ : ComplexLorentzGroup d)
    (hΛ₀ : complexLorentzAction Λ₀ w ∈ ForwardTube d n) :
    ∀ᶠ Λ in 𝓝 Λ₀, ∃ γ : Path Λ₀ Λ,
      ∀ t, complexLorentzAction (γ t) w ∈ ForwardTube d n := by
  -- Step 1: The map A ↦ (Λ₀ * exp(A)) · w is continuous at A = 0 in the matrix space,
  -- and maps 0 to Λ₀ · w ∈ FT (open). So there exists δ > 0 such that for ‖A‖ < δ,
  -- (Λ₀ * exp(A)) · w ∈ FT, i.e., exp(A) · w ∈ FT after Λ₀ acts.
  set E := Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  -- The action as a function of the matrix A (not restricted to the Lie algebra)
  have hcont : Continuous (fun A : E =>
      (fun k (μ : Fin (d + 1)) => ∑ ν, (Λ₀.val * NormedSpace.exp A) μ ν * w k ν)) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    apply continuous_finset_sum; intro ν _
    have hentry : Continuous (fun A : E => (Λ₀.val * NormedSpace.exp A) μ ν) := by
      have : Continuous (fun A : E => Λ₀.val * NormedSpace.exp A) :=
        continuous_const.mul NormedSpace.exp_continuous
      exact (continuous_apply_apply μ ν).comp this
    exact hentry.mul continuous_const
  -- At A = 0, we get Λ₀ · w ∈ FT
  have h0 : (fun k (μ : Fin (d + 1)) => ∑ ν, (Λ₀.val * NormedSpace.exp (0 : E)) μ ν * w k ν)
      ∈ ForwardTube d n := by
    have : (fun k (μ : Fin (d + 1)) => ∑ ν, (Λ₀.val * NormedSpace.exp (0 : E)) μ ν * w k ν) =
        complexLorentzAction Λ₀ w := by
      ext k μ
      simp [NormedSpace.exp_zero, complexLorentzAction, complexLorentzVectorAction]
    rw [this]; exact hΛ₀
  -- Get δ > 0 such that ‖A‖ < δ → (Λ₀ * exp(A)) · w ∈ FT
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_forwardTube.preimage hcont) 0 h0
  -- For ‖A‖ < δ, the action stays in FT
  have hA_FT : ∀ A : E, ‖A‖ < δ →
      (fun k (μ : Fin (d + 1)) => ∑ ν, (Λ₀.val * NormedSpace.exp A) μ ν * w k ν)
      ∈ ForwardTube d n :=
    fun A hA => hδ_sub (by rwa [Metric.mem_ball, dist_zero_right])
  -- Step 2: Use exp_nhd_of_one to get a neighborhood of 1 where Λ₁ = expLieAlg(X)
  -- with ‖X‖ < δ. Then left-translate by Λ₀ to get a nhd of Λ₀.
  -- Left multiplication by Λ₀ is continuous
  have h_left_cont : Continuous (Λ₀ * · : ComplexLorentzGroup d → ComplexLorentzGroup d) := by
    have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
    rw [hind.continuous_iff]
    exact continuous_const.mul ComplexLorentzGroup.continuous_val
  -- The exp neighborhood of 1 pulled back to a neighborhood of Λ₀ via left mult
  have h_nhd : ∀ᶠ Λ in 𝓝 Λ₀,
      ∃ X : E, ComplexLorentzGroup.IsInLieAlgebra X ∧
        (Λ₀⁻¹ * Λ).val = NormedSpace.exp X ∧ ‖X‖ < δ := by
    -- Λ₀⁻¹ * · is continuous and maps Λ₀ to 1
    have h_inv_left : Continuous (Λ₀⁻¹ * · : ComplexLorentzGroup d → ComplexLorentzGroup d) := by
      have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
      rw [hind.continuous_iff]
      exact continuous_const.mul ComplexLorentzGroup.continuous_val
    -- exp_nhd_of_one gives a filter neighborhood of 1
    have h_exp_nhd := exp_nhd_of_one (d := d) δ hδ_pos
    -- Pull back through Λ₀⁻¹ * · : maps Λ₀ ↦ 1
    have h_tendsto : Tendsto (Λ₀⁻¹ * ·) (𝓝 Λ₀) (𝓝 (1 : ComplexLorentzGroup d)) := by
      rw [← inv_mul_cancel Λ₀]
      exact h_inv_left.continuousAt
    exact (h_tendsto.eventually h_exp_nhd).mono
      fun Λ ⟨X, hX_lie, hΛ_eq, hX_small⟩ => ⟨X, hX_lie, hΛ_eq, hX_small⟩
  apply h_nhd.mono
  -- For each such Λ, construct the path and verify orbit condition
  intro Λ ⟨X, hX_lie, hΛ_eq, hX_small⟩
  -- Establish Λ = Λ₀ * expLieAlg(X)
  have hΛ_prod : Λ = Λ₀ * ComplexLorentzGroup.expLieAlg X hX_lie := by
    apply ComplexLorentzGroup.ext
    show Λ.val = Λ₀.val * NormedSpace.exp X
    have h1 : Λ₀⁻¹.val * Λ.val = NormedSpace.exp X := by
      rw [← ComplexLorentzGroup.mul_val]; exact hΛ_eq
    calc Λ.val = Λ₀.val * (Λ₀⁻¹.val * Λ.val) := by
          rw [← Matrix.mul_assoc, ← ComplexLorentzGroup.mul_val,
            show (Λ₀ * Λ₀⁻¹).val = (1 : Matrix _ _ ℂ) from by
              rw [mul_inv_cancel]; rfl,
            Matrix.one_mul]
      _ = Λ₀.val * NormedSpace.exp X := by rw [h1]
  -- Construct the path: t ↦ Λ₀ * expLieAlg(tX)
  set γ : Path Λ₀ Λ := {
    toFun := fun t => Λ₀ * ComplexLorentzGroup.expLieAlg
      ((↑↑t : ℂ) • X) (ComplexLorentzGroup.isInLieAlgebra_smul _ hX_lie)
    continuous_toFun := by
      have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
      rw [hind.continuous_iff]
      show Continuous (fun t : ↥unitInterval =>
        Λ₀.val * NormedSpace.exp ((↑↑t : ℂ) • X))
      exact continuous_const.mul
        (NormedSpace.exp_continuous.comp
          ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const))
    source' := by
      show Λ₀ * ComplexLorentzGroup.expLieAlg _ _ = Λ₀
      ext; simp [ComplexLorentzGroup.expLieAlg, ComplexLorentzGroup.mul_val,
        NormedSpace.exp_zero]
    target' := by
      show Λ₀ * ComplexLorentzGroup.expLieAlg _ _ = Λ
      have : ((1 : unitInterval) : ℝ) = 1 := rfl
      simp only [this, Complex.ofReal_one, one_smul]
      exact hΛ_prod.symm
  } with hγ_def
  -- Verify orbit condition: for all t ∈ [0,1], (γ t) · w ∈ FT
  refine ⟨γ, fun t => ?_⟩
  -- (γ t) · w = (Λ₀ * expLieAlg(tX)) · w, and expLieAlg(tX).val = exp(tX)
  -- The action equals (fun k μ => ∑ ν, (Λ₀.val * exp(tX)) μ ν * w k ν) ∈ FT by hA_FT
  have haction_eq : complexLorentzAction (γ t) w =
      (fun k (μ : Fin (d + 1)) =>
        ∑ ν, (Λ₀.val * NormedSpace.exp ((↑↑t : ℂ) • X)) μ ν * w k ν) := by
    rfl
  rw [haction_eq]
  apply hA_FT
  -- ‖(t : ℂ) • X‖ ≤ ‖X‖ < δ
  calc ‖(↑↑t : ℂ) • X‖ = ‖(↑↑t : ℂ)‖ * ‖X‖ := norm_smul _ _
    _ ≤ 1 * ‖X‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (t.2.1)]
        exact t.2.2
    _ = ‖X‖ := one_mul _
    _ < δ := hX_small

private lemma isOpen_orbitSet_pathComponent (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n) (Λ₀ : ComplexLorentzGroup d)
    (hΛ₀ : complexLorentzAction Λ₀ w ∈ ForwardTube d n) :
    IsOpen (pathComponentIn (orbitSet w) Λ₀) := by
  have hlocal : ∀ x ∈ orbitSet w,
      ∀ᶠ y in 𝓝 x, ∃ γ : Path x y, ∀ t, γ t ∈ orbitSet w := by
    intro x hx
    refine (orbitSet_locallyPathConnected w hw x hx).mono ?_
    intro y hy
    rcases hy with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    intro t
    exact hγ t
  exact isOpen_pathComponentIn_of_eventually_joined hlocal Λ₀ hΛ₀

/- **The orbit set O_w = {Λ ∈ G : Λ·w ∈ FT} is preconnected.**

    The orbit set is an open subset of the connected complex Lorentz group G
    containing the identity (since 1·w = w ∈ FT). It is locally path-connected
    by `orbitSet_locallyPathConnected` (using the exponential map + convexity of FT).

    **Correct proof approach (Fiber/Quotient argument):**
    The orbit map φ_w : G → G·w sending Λ ↦ Λ·w restricts to a map
    O_w → G·w ∩ FT. The fiber of φ_w is the stabilizer Stab(w), which for
    w with Im(w) ∈ V⁺ is isomorphic to SO(d;ℂ) — a connected group.
    The base G·w ∩ FT is connected (intersection of an irreducible complex
    variety with a convex tube domain). By the fiber bundle connectivity theorem
    (connected fiber + connected base → connected total space), O_w is connected.

    **Alternative (Polar decomposition):** Every Λ ∈ SO⁺(1,d;ℂ) decomposes
    as Λ = R · exp(iX) with R ∈ SO⁺↑(1,d;ℝ) and X ∈ so(1,d;ℝ). The path
    t ↦ R · exp(itX) connects R to Λ. Since R preserves FT and exp(iX)·w ∈ FT,
    geodesic convexity of V⁺ under the Lorentz group gives exp(itX)·w ∈ FT
    for all t ∈ [0,1].

    Ref: Streater & Wightman, *PCT, Spin and Statistics*, proof of Theorem 2-11.
    See also `test/proofideas_orbit_preconnected.lean` for detailed analysis.

    NOTE: A previous general topology lemma claiming that an open locally
    path-connected subset of a path-connected group containing 1 is preconnected
    was FALSE (counterexample: G = ℝ, S = (-2,-1) ∪ (-½,½) ∪ (1,2)).
    See GitHub issue #30. The correct proof requires the specific Lie-theoretic
    structure of the Lorentz group orbit, not just general topology. -/

lemma ofReal_one_eq :
    ComplexLorentzGroup.ofReal (1 : RestrictedLorentzGroup d) = 1 := by
  ext i j
  show (↑((1 : RestrictedLorentzGroup d).val.val i j) : ℂ) = (1 : Matrix _ _ ℂ) i j
  change (↑((1 : Matrix _ _ ℝ) i j) : ℂ) = _
  simp [Matrix.one_apply]; split_ifs <;> simp

lemma ofReal_mul_eq (R₁ R₂ : RestrictedLorentzGroup d) :
    ComplexLorentzGroup.ofReal (R₁ * R₂) =
    ComplexLorentzGroup.ofReal R₁ * ComplexLorentzGroup.ofReal R₂ := by
  ext i j
  simp only [ComplexLorentzGroup.ofReal, ComplexLorentzGroup.mul_val, Matrix.mul_apply]
  change (↑((R₁.val.val * R₂.val.val) i j) : ℂ) = _
  rw [Matrix.mul_apply]; push_cast; rfl

lemma continuous_ofReal :
    Continuous (ComplexLorentzGroup.ofReal : RestrictedLorentzGroup d → ComplexLorentzGroup d) := by
  apply continuous_induced_rng.mpr
  show Continuous (fun R : RestrictedLorentzGroup d => (ComplexLorentzGroup.ofReal R).val)
  exact continuous_pi fun i => continuous_pi fun j =>
    Complex.continuous_ofReal.comp ((continuous_apply j).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_subtype_val)))

/-- Real Lorentz transformations preserve the forward tube.
    Since R is real, Im(R·v) = R·Im(v), and R preserves V₊. -/
theorem ofReal_preserves_forwardTube (R : RestrictedLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ ForwardTube d n := by
  exact ofReal_preserves_forwardTube_base (d := d) (n := n) R z hz

private lemma orbitSet_mem_mul_ofReal_left (w : Fin n → Fin (d + 1) → ℂ)
    (R : RestrictedLorentzGroup d)
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ orbitSet w) :
    (ComplexLorentzGroup.ofReal R * Λ) ∈ orbitSet w := by
  have hΛw : complexLorentzAction Λ w ∈ ForwardTube d n := hΛ
  have hR : complexLorentzAction (ComplexLorentzGroup.ofReal R)
      (complexLorentzAction Λ w) ∈ ForwardTube d n :=
    ofReal_preserves_forwardTube R _ hΛw
  simpa [orbitSet, complexLorentzAction_mul] using hR

private lemma orbitSet_joined_one_ofReal
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (R : RestrictedLorentzGroup d) :
    JoinedIn (orbitSet w) (1 : ComplexLorentzGroup d) (ComplexLorentzGroup.ofReal R) := by
  have hj : JoinedIn Set.univ (1 : RestrictedLorentzGroup d) R :=
    (RestrictedLorentzGroup.isPathConnected (d := d)).joinedIn 1
      (Set.mem_univ _) R (Set.mem_univ _)
  rcases joinedIn_univ.mp hj with ⟨γ⟩
  refine ⟨
    { toFun := fun t => ComplexLorentzGroup.ofReal (γ t)
      continuous_toFun := continuous_ofReal.comp γ.continuous_toFun
      source' := by
        rw [γ.source]
        exact ofReal_one_eq
      target' := by
        rw [γ.target] },
    ?_⟩
  intro t
  show complexLorentzAction (ComplexLorentzGroup.ofReal (γ t)) w ∈ ForwardTube d n
  exact ofReal_preserves_forwardTube (γ t) w hw

private lemma orbitSet_joined_mul_ofReal_left
    (w : Fin n → Fin (d + 1) → ℂ)
    {Λ : ComplexLorentzGroup d} (hΛ : Λ ∈ orbitSet w)
    (R : RestrictedLorentzGroup d) :
    JoinedIn (orbitSet w) Λ (ComplexLorentzGroup.ofReal R * Λ) := by
  have hj : JoinedIn Set.univ (1 : RestrictedLorentzGroup d) R :=
    (RestrictedLorentzGroup.isPathConnected (d := d)).joinedIn 1
      (Set.mem_univ _) R (Set.mem_univ _)
  rcases joinedIn_univ.mp hj with ⟨γ⟩
  refine ⟨
    { toFun := fun t => ComplexLorentzGroup.ofReal (γ t) * Λ
      continuous_toFun := (continuous_ofReal.comp γ.continuous_toFun).mul continuous_const
      source' := by
        rw [γ.source, ofReal_one_eq, one_mul]
      target' := by
        rw [γ.target] },
    ?_⟩
  intro t
  exact orbitSet_mem_mul_ofReal_left w (γ t) hΛ

private lemma orbitSet_mem_mul_ofReal_right_of_stabilizes
    (w : Fin n → Fin (d + 1) → ℂ)
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ orbitSet w)
    (R : RestrictedLorentzGroup d)
    (hRw : complexLorentzAction (ComplexLorentzGroup.ofReal R) w = w) :
    (Λ * ComplexLorentzGroup.ofReal R) ∈ orbitSet w := by
  change complexLorentzAction (Λ * ComplexLorentzGroup.ofReal R) w ∈ ForwardTube d n
  rw [complexLorentzAction_mul, hRw]
  exact hΛ

private lemma orbitSet_joined_mul_ofReal_right_of_stabilizerPath
    (w : Fin n → Fin (d + 1) → ℂ)
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ orbitSet w)
    (R : RestrictedLorentzGroup d)
    (hstabPath :
      JoinedIn
        {S : RestrictedLorentzGroup d |
          complexLorentzAction (ComplexLorentzGroup.ofReal S) w = w}
        1 R) :
    JoinedIn (orbitSet w) Λ (Λ * ComplexLorentzGroup.ofReal R) := by
  rcases hstabPath with ⟨γ, hγ⟩
  refine ⟨
    { toFun := fun t => Λ * ComplexLorentzGroup.ofReal (γ t)
      continuous_toFun := continuous_const.mul (continuous_ofReal.comp γ.continuous_toFun)
      source' := by
        rw [γ.source, ofReal_one_eq, mul_one]
      target' := by
        rw [γ.target] },
    ?_⟩
  intro t
  exact orbitSet_mem_mul_ofReal_right_of_stabilizes w hΛ (γ t) (hγ t)

private lemma ofReal_range_subset_pathComponentIn_orbitSet_one
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n) :
    Set.range (ComplexLorentzGroup.ofReal : RestrictedLorentzGroup d → ComplexLorentzGroup d) ⊆
      pathComponentIn (orbitSet w) (1 : ComplexLorentzGroup d) := by
  rintro Λ ⟨R, rfl⟩
  exact orbitSet_joined_one_ofReal w hw R

private lemma ofReal_mul_mem_pathComponentIn_orbitSet_one
    (w : Fin n → Fin (d + 1) → ℂ)
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ pathComponentIn (orbitSet w) (1 : ComplexLorentzGroup d))
    (R : RestrictedLorentzGroup d) :
    ComplexLorentzGroup.ofReal R * Λ ∈ pathComponentIn (orbitSet w) (1 : ComplexLorentzGroup d) := by
  have hΛ_orbit : Λ ∈ orbitSet w := hΛ.target_mem
  exact hΛ.trans (orbitSet_joined_mul_ofReal_left w hΛ_orbit R)

private theorem orbitSet_isPreconnected_of_joinedIn_one
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n)
    (hjoin : ∀ (Λ : ComplexLorentzGroup d), Λ ∈ orbitSet w →
      JoinedIn (orbitSet w) (1 : ComplexLorentzGroup d) Λ) :
    IsPreconnected (orbitSet w) := by
  have h_one : (1 : ComplexLorentzGroup d) ∈ orbitSet w := by
    simpa [orbitSet, complexLorentzAction_one] using hw
  let oneS : orbitSet w := ⟨1, h_one⟩
  have hjoined_subtype : ∀ y : orbitSet w, Joined oneS y := by
    intro y
    exact (joinedIn_iff_joined (x_in := h_one) (y_in := y.2)).mp (hjoin y y.2)
  haveI : PathConnectedSpace (orbitSet w) := by
    refine PathConnectedSpace.mk ?_ ?_
    · exact ⟨oneS⟩
    · intro x y
      exact (hjoined_subtype x).symm.trans (hjoined_subtype y)
  exact (isPreconnected_iff_preconnectedSpace).2
    (inferInstance : PreconnectedSpace (orbitSet w))

private theorem orbitSet_isPreconnected_of_doubleCoset_generation_with_stabilizerPath
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n)
    (Λ0 : ComplexLorentzGroup d)
    (hΛ0 : Λ0 ∈ orbitSet w)
    (hjoin0 : JoinedIn (orbitSet w) (1 : ComplexLorentzGroup d) Λ0)
    (hgen : ∀ Λ ∈ orbitSet w,
      ∃ R1 R2 : RestrictedLorentzGroup d,
        JoinedIn
          {S : RestrictedLorentzGroup d |
            complexLorentzAction (ComplexLorentzGroup.ofReal S) w = w}
          1 R2 ∧
        Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2) :
    IsPreconnected (orbitSet w) := by
  have hjoin : ∀ (Λ : ComplexLorentzGroup d), Λ ∈ orbitSet w →
      JoinedIn (orbitSet w) (1 : ComplexLorentzGroup d) Λ := by
    intro Λ hΛ
    rcases hgen Λ hΛ with ⟨R1, R2, hR2path, rfl⟩
    have hmid : (Λ0 * ComplexLorentzGroup.ofReal R2) ∈ orbitSet w := by
      exact orbitSet_mem_mul_ofReal_right_of_stabilizes w hΛ0 R2 (hR2path.target_mem)
    have h0_to_mid :
        JoinedIn (orbitSet w) (1 : ComplexLorentzGroup d)
          (Λ0 * ComplexLorentzGroup.ofReal R2) :=
      hjoin0.trans
        (orbitSet_joined_mul_ofReal_right_of_stabilizerPath w hΛ0 R2 hR2path)
    have hmid_to_goal :
        JoinedIn (orbitSet w)
          (Λ0 * ComplexLorentzGroup.ofReal R2)
          (ComplexLorentzGroup.ofReal R1 * (Λ0 * ComplexLorentzGroup.ofReal R2)) :=
      orbitSet_joined_mul_ofReal_left w hmid R1
    have hmid_to_goal' :
        JoinedIn (orbitSet w)
          (Λ0 * ComplexLorentzGroup.ofReal R2)
          (ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2) := by
      simpa [mul_assoc] using hmid_to_goal
    exact h0_to_mid.trans hmid_to_goal'
  exact orbitSet_isPreconnected_of_joinedIn_one w hw hjoin

/-- **The orbit set O_w is preconnected.**
    One-point geometric input for `nonemptyDomain_isPreconnected`.

    NOTE (2026-02-25): The previous proof route used a global endpoint-to-interval
    geodesic cone lemma, which is false as stated and has been removed. A corrected
    proof must use stronger hypotheses (or a different path construction). -/
private theorem orbitSet_onePoint_isPreconnected (w : Fin 1 → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d 1) :
    IsPreconnected {Λ : ComplexLorentzGroup d |
      complexLorentzAction Λ w ∈ ForwardTube d 1} := by
  by_cases hd : d = 1
  · subst hd
    have hw_core : w ∈ BHWCore.ForwardTube 1 1 := by
      simpa [ForwardTube] using hw
    have hpre_core := orbitSet_isPreconnected_d1 (n := 1) w hw_core
    simpa [complexLorentzAction, BHWCore.complexLorentzAction, ForwardTube] using hpre_core
  · -- Remaining geometric blocker for `d > 1`.
    by_cases h0 : d = 0
    · subst h0
      let S : Set (ComplexLorentzGroup 0) :=
        {Λ : ComplexLorentzGroup 0 | complexLorentzAction Λ w ∈ ForwardTube 0 1}
      haveI : Subsingleton (ComplexLorentzGroup 0) := complexLorentzGroup_d0_subsingleton
      have hsubs : S.Subsingleton := by
        intro a _ b _
        exact Subsingleton.elim a b
      simpa [S] using hsubs.isPreconnected
    · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨m, hm⟩
      subst hm
      exact orbitSet_forwardTube_one_isPreconnected (m := m) w hw

private lemma forwardTube_one_iff
    (w : Fin 1 → Fin (d + 1) → ℂ) :
    w ∈ ForwardTube d 1 ↔ InOpenForwardCone d (fun μ => (w 0 μ).im) := by
  constructor
  · intro hw
    simpa [ForwardTube] using hw 0
  · intro h k
    fin_cases k
    simpa [ForwardTube] using h

private lemma forwardTube_of_affine_steps [NeZero n]
    (v : Fin (d + 1) → ℂ) :
    (fun k : Fin n => fun μ => ((k.val + 1 : ℂ) * v μ)) ∈ ForwardTube d n ↔
      InOpenForwardCone d (fun μ => (v μ).im) := by
  constructor
  · intro hw
    have h0 := hw ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    simpa [ForwardTube] using h0
  · intro hv k
    by_cases hk : k = 0
    · subst hk
      simpa [ForwardTube] using hv
    · have hk0 : k.val ≠ 0 := by
        intro hkval
        exact hk (Fin.ext hkval)
      have hpred : (k.val - 1 + 1 : ℕ) = k.val := by
        omega
      have hpredR : (((k.val - 1 : ℕ) : ℝ) + 1) = k.val := by
        exact_mod_cast hpred
      have hvec :
          (fun μ =>
            (k.val + 1 : ℝ) * (v μ).im - (k.val : ℝ) * (v μ).im)
            = fun μ => (v μ).im := by
        ext μ
        ring
      simpa [ForwardTube, hk0, hpredR, hvec]

private lemma action_affine_steps
    (Λ : ComplexLorentzGroup d)
    (v : Fin (d + 1) → ℂ) :
    complexLorentzAction (n := n) Λ (fun k : Fin n => fun μ => ((k.val + 1 : ℂ) * v μ))
      =
    (fun k : Fin n => fun μ => ((k.val + 1 : ℂ) * (∑ ν, Λ.val μ ν * v ν))) := by
  ext k μ
  simp [complexLorentzAction]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ν _
  ring

/-- For `n > 0`, the nonempty-domain set is independent of `n` and reduces to
the `n = 1` witness form. -/
private lemma nonemptyDomain_eq_n1 (hn : n ≠ 0) :
    {Λ : ComplexLorentzGroup d |
      ∃ w : Fin n → Fin (d + 1) → ℂ,
        w ∈ ForwardTube d n ∧ complexLorentzAction (n := n) Λ w ∈ ForwardTube d n}
      =
    {Λ : ComplexLorentzGroup d |
      ∃ w : Fin 1 → Fin (d + 1) → ℂ,
        w ∈ ForwardTube d 1 ∧ complexLorentzAction (n := 1) Λ w ∈ ForwardTube d 1} := by
  haveI : NeZero n := ⟨hn⟩
  ext Λ
  constructor
  · intro hΛ
    rcases hΛ with ⟨w, hwFT, hΛwFT⟩
    let w1 : Fin 1 → Fin (d + 1) → ℂ := fun _ => w ⟨0, Nat.pos_of_ne_zero hn⟩
    refine ⟨w1, ?_, ?_⟩
    · have h0 := hwFT ⟨0, Nat.pos_of_ne_zero hn⟩
      exact (forwardTube_one_iff (d := d) w1).2 (by simpa [w1, ForwardTube] using h0)
    · have h0 := hΛwFT ⟨0, Nat.pos_of_ne_zero hn⟩
      exact (forwardTube_one_iff (d := d) (complexLorentzAction (n := 1) Λ w1)).2 (by
        simpa [w1, complexLorentzAction, ForwardTube] using h0)
  · intro hΛ
    rcases hΛ with ⟨w1, hw1FT, hΛw1FT⟩
    let v : Fin (d + 1) → ℂ := w1 0
    let wn : Fin n → Fin (d + 1) → ℂ :=
      fun k μ => ((k.val + 1 : ℂ) * v μ)
    refine ⟨wn, ?_, ?_⟩
    · have hv : InOpenForwardCone d (fun μ => (v μ).im) := by
        simpa [v] using (forwardTube_one_iff (d := d) w1).1 hw1FT
      exact (forwardTube_of_affine_steps (d := d) (n := n) v).2 hv
    · have hΛv : InOpenForwardCone d (fun μ => ((∑ ν, Λ.val μ ν * v ν)).im) := by
        have h1 : InOpenForwardCone d (fun μ => (complexLorentzAction (n := 1) Λ w1 0 μ).im) :=
          (forwardTube_one_iff (d := d) (complexLorentzAction (n := 1) Λ w1)).1 hΛw1FT
        simpa [complexLorentzAction, complexLorentzVectorAction, v] using h1
      have hstepFT :
          (fun k : Fin n => fun μ => ((k.val + 1 : ℂ) * (∑ ν, Λ.val μ ν * v ν))) ∈
            ForwardTube d n :=
        (forwardTube_of_affine_steps (d := d) (n := n)
          (fun μ => (∑ ν, Λ.val μ ν * v ν))).2 hΛv
      simpa [wn, v, action_affine_steps (d := d) (n := n) Λ v] using hstepFT

/-- The nonempty-domain set
    `U = {Λ : G | ∃ w ∈ FT, Λ·w ∈ FT}` is open in `G`. -/
private theorem nonemptyDomain_isOpen :
    IsOpen {Λ : ComplexLorentzGroup d |
      ∃ w, w ∈ ForwardTube d n ∧ complexLorentzAction Λ w ∈ ForwardTube d n} := by
  set S : Set (ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ)) :=
    {p | p.2 ∈ ForwardTube d n ∧ complexLorentzAction p.1 p.2 ∈ ForwardTube d n}
  have hS_open : IsOpen S := by
    have h1 : IsOpen {p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) |
        p.2 ∈ ForwardTube d n} :=
      isOpen_forwardTube.preimage continuous_snd
    have hcont : Continuous
        (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
          complexLorentzAction p.1 p.2) := by
      apply continuous_pi; intro k
      apply continuous_pi; intro μ
      simp only [complexLorentzAction]
      apply continuous_finset_sum; intro ν _
      apply Continuous.mul
      · have hval : Continuous
            (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) => p.1.val) :=
          ComplexLorentzGroup.continuous_val.comp continuous_fst
        have hrow : Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M μ) :=
          continuous_apply μ
        have hentry : Continuous (fun r : Fin (d + 1) → ℂ => r ν) :=
          continuous_apply ν
        exact hentry.comp (hrow.comp hval)
      · exact (continuous_apply ν).comp ((continuous_apply k).comp continuous_snd)
    have h2 : IsOpen {p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) |
        complexLorentzAction p.1 p.2 ∈ ForwardTube d n} :=
      isOpen_forwardTube.preimage hcont
    simpa [S] using h1.inter h2
  have hU_eq : {Λ : ComplexLorentzGroup d |
      ∃ w, w ∈ ForwardTube d n ∧ complexLorentzAction Λ w ∈ ForwardTube d n} =
      Prod.fst '' S := by
    ext Λ
    constructor
    · rintro ⟨w, hw, hΛw⟩
      exact ⟨(Λ, w), by simpa [S] using And.intro hw hΛw, rfl⟩
    · rintro ⟨⟨Λ', w⟩, hp, hfst⟩
      simp at hfst
      subst hfst
      exact ⟨w, by simpa [S] using hp⟩
  rw [hU_eq]
  exact isOpenMap_fst _ hS_open

/-- The set U = {Λ ∈ G : D_Λ ≠ ∅} of group elements with nonempty domain is connected.
    U = ⋃_{w ∈ FT} O_w where each O_w is preconnected and all contain 1, so the
    union is preconnected by `isPreconnected_sUnion`. -/
theorem nonemptyDomain_isPreconnected :
    IsPreconnected {Λ : ComplexLorentzGroup d |
      ∃ w, w ∈ ForwardTube d n ∧ complexLorentzAction Λ w ∈ ForwardTube d n} := by
  by_cases hn : n = 0
  · subst hn
    have hft0 : ∀ z : Fin 0 → Fin (d + 1) → ℂ, z ∈ ForwardTube d 0 := by
      intro z k
      exact Fin.elim0 k
    have hU_univ : {Λ : ComplexLorentzGroup d |
        ∃ w, w ∈ ForwardTube d 0 ∧ complexLorentzAction (n := 0) Λ w ∈ ForwardTube d 0}
          = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr ?_
      intro Λ
      exact ⟨(fun k => Fin.elim0 k), hft0 _, hft0 _⟩
    haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
      pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
    rw [hU_univ]
    exact PreconnectedSpace.isPreconnected_univ (α := ComplexLorentzGroup d)
  · have hU_eq_n1 := nonemptyDomain_eq_n1 (d := d) (n := n) hn
    rw [hU_eq_n1]
    -- Express the `n = 1` domain as a union of one-point orbit sets.
    have hU1_eq : {Λ : ComplexLorentzGroup d |
        ∃ w : Fin 1 → Fin (d + 1) → ℂ,
          w ∈ ForwardTube d 1 ∧
            complexLorentzAction (n := 1) Λ w ∈ ForwardTube d 1} =
      ⋃₀ {S | ∃ w : Fin 1 → Fin (d + 1) → ℂ, w ∈ ForwardTube d 1 ∧
        S = {Λ : ComplexLorentzGroup d |
          complexLorentzAction (n := 1) Λ w ∈ ForwardTube d 1}} := by
      ext Λ
      simp only [Set.mem_setOf_eq, Set.mem_sUnion]
      constructor
      · rintro ⟨w, hw, hΛw⟩
        exact ⟨_, ⟨w, hw, rfl⟩, hΛw⟩
      · rintro ⟨_, ⟨w, hw, rfl⟩, hΛw⟩
        exact ⟨w, hw, hΛw⟩
    rw [hU1_eq]
    apply isPreconnected_sUnion (1 : ComplexLorentzGroup d)
    · -- Each one-point orbit set contains 1.
      rintro S ⟨w, hw, rfl⟩
      simpa [complexLorentzAction_one] using hw
    · -- Each one-point orbit set is preconnected.
      rintro S ⟨w, hw, rfl⟩
      exact orbitSet_onePoint_isPreconnected (d := d) w hw


end BHW
