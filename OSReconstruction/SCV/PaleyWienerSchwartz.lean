/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.ConeCutoffSchwartz
import OSReconstruction.SCV.FourierLaplaceCore
import OSReconstruction.SCV.Osgood
import OSReconstruction.GeneralResults.ScalarFTC
import OSReconstruction.GeneralResults.SchwartzCutoffExp
import OSReconstruction.GeneralResults.SchwartzDamping
import OSReconstruction.GeneralResults.SchwartzFubini
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Algebra.Order.Chebyshev

/-!
# Paley-Wiener-Schwartz Bridge for Tube Domains

The core theorem connecting Fourier support in the dual cone C* to the
Fourier-Laplace representation with growth bounds.

Given a tempered distribution T with Fourier support in C*, the function
`F(z) = T(ψ_z)` (where ψ_z is an appropriate Schwartz family parametrized
by z ∈ T(C)) is holomorphic on the tube T(C), has tempered distributional
boundary values, and satisfies the global Vladimirov growth bound.

## Main results

- `multiDimPsiZ` — the multi-dimensional Schwartz family ψ_z for z in a tube
- `fourierLaplaceExtMultiDim` — F(z) = T(ψ_z), the Fourier-Laplace extension
- `fourierLaplaceExtMultiDim_holomorphic` — F is holomorphic on the tube
  (via pointwise-scalarized difference quotients + Osgood/Hartogs)
- `fourierLaplaceExtMultiDim_growth` — global Vladimirov growth bound
- `fourierLaplaceExtMultiDim_boundaryValue` — tempered distributional BV

## Lean 4 workarounds

**Fréchet calculus**: z ↦ ψ_z is NOT expressible as `Differentiable ℂ` into
Schwartz space (Schwartz space is Fréchet, not normed). Workaround: apply T
first, then show the scalar F(z) = T(ψ_z) is holomorphic via:
1. Fix z, compute difference quotient (F(z+he_j) - F(z))/h
2. Move inside T by linearity: T((ψ_{z+he_j} - ψ_z)/h)
3. Bound the remainder in Schwartz seminorms using integral MVT
   (pointwise scalarize: fix x and multi-indices, apply norm_integral_le_integral_norm)
4. Get separate holomorphicity in each z_j
5. Apply `osgood_lemma` for joint holomorphicity

**Bochner integral**: Cannot integrate Schwartz-valued curves. All integrals
are scalarized to ℂ before applying Lean's Bochner integral.

## References

- Vladimirov, "Methods of Generalized Functions", §25
- Hörmander, "The Analysis of Linear PDOs I", §7.4
- Streater-Wightman, "PCT, Spin and Statistics", Theorems 2-6, 2-9
-/

open scoped Classical ComplexConjugate BigOperators NNReal ContDiff
open MeasureTheory Complex
noncomputable section

variable {m : ℕ}

private theorem iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl_of_contDiff
    {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E₁ × E₂ → F) (hf : ContDiff ℝ ∞ f) (y : E₂) (l : ℕ) (x : E₁) :
    iteratedFDeriv ℝ l (fun x' => f (x', y)) x =
      (iteratedFDeriv ℝ l f (x, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂) := by
  have htranslate : ∀ x',
      iteratedFDeriv ℝ l (fun z : E₁ × E₂ => f (z + (0, y))) (x', (0 : E₂)) =
        iteratedFDeriv ℝ l f (x' + 0, (0 : E₂) + y) := by
    intro x'
    rw [iteratedFDeriv_comp_add_right' l (0, y)]
    simp [Prod.add_def]
  have hcomp : ContDiff ℝ ∞ (fun z : E₁ × E₂ => f (z + ((0 : E₁), y))) :=
    hf.comp ((contDiff_id.add contDiff_const).of_le le_top)
  have hinl_comp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (ContinuousLinearMap.inl ℝ E₁ E₂) hcomp x (by exact_mod_cast le_top (a := (l : ℕ∞)))
  have hlhs :
      (fun x' => f (x', y)) =
        (fun z : E₁ × E₂ => f (z + (0, y))) ∘ (ContinuousLinearMap.inl ℝ E₁ E₂) := by
    ext x'
    simp [ContinuousLinearMap.inl_apply]
  rw [hlhs, hinl_comp]
  exact congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F =>
      A.compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂))
    (by simpa [ContinuousLinearMap.inl_apply] using htranslate x)

private theorem hasFDerivAt_iteratedFDeriv_partialEval₂_of_contDiff
    {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E₁ × E₂ → F) (hf : ContDiff ℝ ∞ f) (l : ℕ) (x : E₁) (y : E₂) :
    HasFDerivAt
      (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x)
      ((ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
          (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)).comp
        ((fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)).comp
          (ContinuousLinearMap.inr ℝ E₁ E₂)))
      y := by
  let A :
      ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁) F :=
    ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
      (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)
  let H :
      E₂ → ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F :=
    fun y' => iteratedFDeriv ℝ l f (x, y')
  have hH :
      HasFDerivAt H
        ((fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)).comp
          (ContinuousLinearMap.inr ℝ E₁ E₂))
        y := by
    have hfull :
        HasFDerivAt (iteratedFDeriv ℝ l f)
          (fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)) (x, y) := by
      have hf' : ContDiff ℝ (l + 1) f := hf.of_le (by exact_mod_cast le_top)
      exact
        hf'.differentiable_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self l) (x, y) |>.hasFDerivAt
    simpa [H] using hfull.comp y (hasFDerivAt_prodMk_right x y)
  have hEq :
      (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x) = A ∘ H := by
    funext y'
    simp [A, H, iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl_of_contDiff,
      hf]
  rw [hEq]
  exact A.hasFDerivAt.comp y hH

private theorem norm_fderiv_iteratedFDeriv_partialEval₂_le_of_contDiff
    {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E₁ × E₂ → F) (hf : ContDiff ℝ ∞ f) (l : ℕ) (x : E₁) (y : E₂) :
    ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x) y‖ ≤
      ‖iteratedFDeriv ℝ (l + 1) f (x, y)‖ := by
  let A :
      ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁) F :=
    ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
      (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)
  calc
    ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x) y‖
      = ‖A.comp
          ((fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)).comp
            (ContinuousLinearMap.inr ℝ E₁ E₂))‖ := by
          rw [show
              fderiv ℝ (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x) y =
                A.comp
                  ((fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)).comp
                    (ContinuousLinearMap.inr ℝ E₁ E₂)) by
              simpa [A] using
                (hasFDerivAt_iteratedFDeriv_partialEval₂_of_contDiff f hf l x y).fderiv]
    _ ≤ ‖A‖ *
          ‖(fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)).comp
            (ContinuousLinearMap.inr ℝ E₁ E₂)‖ := by
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 *
          ‖(fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)).comp
            (ContinuousLinearMap.inr ℝ E₁ E₂)‖ := by
          have hA :
              ‖A‖ ≤ ∏ _ : Fin l, ‖ContinuousLinearMap.inl ℝ E₁ E₂‖ := by
            simpa [A] using
              (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
                (𝕜 := ℝ) (ι := Fin l)
                (E := fun _ : Fin l => E₁)
                (E₁ := fun _ : Fin l => E₁ × E₂)
                (G := _)
                (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂))
          have hone_prod : ∏ _ : Fin l, ‖ContinuousLinearMap.inl ℝ E₁ E₂‖ ≤ (1 : ℝ) := by
            apply Finset.prod_le_one
            · intro i hi
              exact norm_nonneg _
            · intro i hi
              exact ContinuousLinearMap.norm_inl_le_one ℝ E₁ E₂
          have hA1 : ‖A‖ ≤ (1 : ℝ) := hA.trans hone_prod
          nlinarith [hA1, norm_nonneg
            ((fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)).comp
              (ContinuousLinearMap.inr ℝ E₁ E₂))]
    _ = ‖(fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)).comp
          (ContinuousLinearMap.inr ℝ E₁ E₂)‖ := by simp
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)‖ *
          ‖ContinuousLinearMap.inr ℝ E₁ E₂‖ := by
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)‖ * 1 := by
          have hinr : ‖ContinuousLinearMap.inr ℝ E₁ E₂‖ ≤ (1 : ℝ) :=
            ContinuousLinearMap.norm_inr_le_one ℝ E₁ E₂
          nlinarith [hinr, norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ l f) (x, y))]
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ l f) (x, y)‖ := by simp
    _ = ‖iteratedFDeriv ℝ (l + 1) f (x, y)‖ := by
          exact norm_fderiv_iteratedFDeriv

-- FixedConeCutoff and fixedConeCutoff_exists are now in DualCone.lean

/-! ### Multi-dimensional Schwartz family ψ_z

For z = x + iy in the tube T(C) with y ∈ C, the Schwartz function ψ_z is
the product of 1D cutoff-exponentials:

  ψ_z(ξ) = ∏_j χ(ξ_j) · exp(i z_j ξ_j)

where χ is the smooth cutoff from `FourierLaplaceCore.lean`. The exponential
factor exp(iz·ξ) = exp(ix·ξ - y·ξ) has Gaussian-type decay in ξ when y ∈ C
(since y·ξ ≥ 0 for ξ ∈ C*, and the cutoff handles ξ outside C*).

For the multi-D case, we use a tensor product construction: ψ_z is the
product of 1D families in each coordinate, making seminorm estimates
reduce to the 1D bounds from `schwartzPsiZ_seminorm_horizontal_bound`. -/

/-- The multi-dimensional exponential-cutoff Schwartz function with explicit
    cutoff radius `R > 0`, parametrized by `z ∈ T(C)`.

    This is the abstract dynamic-scaling family `ψ_{z,R}`. The fixed-radius
    family used for holomorphicity is `multiDimPsiZ`, defined below by
    specializing to `R = 1`.

    The key property is that for z = x + iy with y ∈ C:
    - ψ_{z,R} ∈ S(ℝ^m) (Schwartz class)
    - ψ_{z,R}(ξ) = χ_R(ξ) exp(iz·ξ) for a smooth cutoff χ_R adapted to C*
    - The Schwartz seminorms of ψ_{z,R} have polynomial growth in x and
      inverse-boundary-distance growth in y

    **Construction** (dynamic scaling trick, see docs/vladimirov_tillmann_gemini_reviews.md):
    1. Build a `FixedConeCutoff` χ₁ via convolution: χ₁ = 1_A * φ where
       A = {ξ : dist(ξ,C*) ≤ 1/2} and φ is a smooth bump in B_{1/2}(0).
    2. Scale dynamically: χ_R(ξ) = χ₁(ξ/R).
    3. For holomorphicity: evaluate at fixed R=1 (F(z) is independent of R
       because supp(T̂) ⊆ C* and all cutoffs agree there).
    4. For growth bound: evaluate at R = 1/(1+‖y‖). The boundary layer
       shrinks, giving exp(R‖y‖) ≤ e (constant), and chain rule gives
       (1+‖y‖)^|α| for derivatives — exactly the polynomial growth.

    **Warning**: A FIXED cutoff (R=1) produces exp(‖y‖) blowup in the
    transition region, destroying the polynomial growth bound. The dynamic
    scaling is essential. -/
def multiDimPsiZR {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (R : ℝ) (hR : 0 < R)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  let χ := (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  psiZRSchwartz hC_open hC_cone hC_salient χ R hR z hz

/-- The fixed-radius (`R = 1`) Schwartz family used for holomorphicity proofs. -/
abbrev multiDimPsiZ {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  multiDimPsiZR C hC_open hC_conv hC_cone hC_salient 1 zero_lt_one z hz

/-- The dynamic radius used in the Vladimirov growth estimate. -/
def multiDimPsiZRadius {m : ℕ} (z : Fin m → ℂ) : ℝ :=
  (1 + ‖fun i => (z i).im‖)⁻¹

theorem multiDimPsiZRadius_pos {m : ℕ} (z : Fin m → ℂ) :
    0 < multiDimPsiZRadius z := by
  have h : 0 < 1 + ‖fun i => (z i).im‖ := by positivity
  simpa [multiDimPsiZRadius] using inv_pos.mpr h

/-- The dynamically scaled Schwartz family used for the global growth bound. -/
def multiDimPsiZDynamic {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  multiDimPsiZR C hC_open hC_conv hC_cone hC_salient
    (multiDimPsiZRadius z) (multiDimPsiZRadius_pos z) z hz

/-- Tube-safe version of `multiDimPsiZ`, extended by `0` outside the tube. -/
def multiDimPsiZExt {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  if hz : z ∈ SCV.TubeDomain C then
    multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz
  else 0

theorem multiDimPsiZExt_eq {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z =
      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz := by
  simp [multiDimPsiZExt, hz]

theorem multiDimPsiZExt_eq_zero {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∉ SCV.TubeDomain C) :
    multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z = 0 := by
  simp [multiDimPsiZExt, hz]

theorem update_mem_tubeDomain_of_small {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) :
    ∃ δ > 0, ∀ h : ℂ, ‖h‖ < δ →
      Function.update z j (z j + h) ∈ SCV.TubeDomain C := by
  -- The tube domain is open, so z has an open ball around it in the tube
  have hopen := SCV.tubeDomain_isOpen hC_open
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen z hz
  refine ⟨ε, hε, fun h hh => hball ?_⟩
  rw [Metric.mem_ball]
  calc dist (Function.update z j (z j + h)) z
      = ‖Function.update z j (z j + h) - z‖ := dist_eq_norm _ _
    _ ≤ ‖h‖ := by
        apply pi_norm_le_iff_of_nonneg (norm_nonneg h) |>.mpr
        intro i
        by_cases hij : i = j
        · subst hij; simp [Function.update_self]
        · simp [Function.update_of_ne hij, sub_self]
    _ < ε := hh

private lemma update_mem_tubeDomain_of_small_segment {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) :
    ∃ δ > 0, ∀ h : ℂ, ‖h‖ < δ → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Function.update z j (z j + (s : ℂ) * h) ∈ SCV.TubeDomain C := by
  obtain ⟨δ, hδ, hδ_mem⟩ := update_mem_tubeDomain_of_small C hC_open z hz j
  refine ⟨δ, hδ, ?_⟩
  intro h hh s hs
  apply hδ_mem
  calc
    ‖(s : ℂ) * h‖ = |s| * ‖h‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * ‖h‖ := by
      gcongr
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := hs.2
      rw [abs_of_nonneg hs0]
      exact hs1
    _ = ‖h‖ := by ring
    _ < δ := hh

/-! ### Quantitative pointwise bounds -/

private lemma pairing_self_lower_bound {m : ℕ} (ξ : Fin m → ℝ) :
    ‖ξ‖ ^ 2 ≤ ((Fintype.card (Fin m) : ℝ) + 1) * ∑ i, ξ i * ξ i := by
  have hsum_nonneg : 0 ≤ ∑ i, ‖ξ i‖ := by
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  have hnorm_le : ‖ξ‖ ≤ ∑ i, ‖ξ i‖ := by
    refine (pi_norm_le_iff_of_nonneg hsum_nonneg).2 ?_
    intro i
    exact Finset.single_le_sum
      (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
  have hsq_sum :
      (∑ i, ‖ξ i‖) ^ 2 ≤
        (Fintype.card (Fin m) : ℝ) * ∑ i, ‖ξ i‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin m => ‖ξ i‖))
  have hsum_sq_eq : ∑ i, ‖ξ i‖ ^ 2 = ∑ i, ξ i * ξ i := by
    congr with i
    simpa [sq, Real.norm_eq_abs] using (sq_abs (ξ i))
  calc
    ‖ξ‖ ^ 2 ≤ (∑ i, ‖ξ i‖) ^ 2 := by
      gcongr
    _ ≤ (Fintype.card (Fin m) : ℝ) * ∑ i, ‖ξ i‖ ^ 2 := hsq_sum
    _ ≤ ((Fintype.card (Fin m) : ℝ) + 1) * ∑ i, ‖ξ i‖ ^ 2 := by
      have hsq_nonneg : 0 ≤ ∑ i, ‖ξ i‖ ^ 2 := by positivity
      nlinarith
    _ = ((Fintype.card (Fin m) : ℝ) + 1) * ∑ i, ξ i * ξ i := by
      rw [hsum_sq_eq]

/-- Uniform coercivity in terms of boundary distance.

For an open cone `C`, the pairing with dual-cone vectors is bounded below by a
universal multiple of `Metric.infDist y Cᶜ`.

The constant here is crude but sufficient for Vladimirov-type growth bounds. -/
private lemma dualConeFlat_coercivity_infDist
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_cone : IsCone C) :
    ∃ c₀ > 0, ∀ (y : Fin m → ℝ) (hy : y ∈ C) (ξ : Fin m → ℝ) (hξ : ξ ∈ DualConeFlat C),
      c₀ * Metric.infDist y Cᶜ * ‖ξ‖ ≤ ∑ i, y i * ξ i := by
  let c₀ : ℝ := (2 * ((Fintype.card (Fin m) : ℝ) + 1))⁻¹
  refine ⟨c₀, by
    dsimp [c₀]
    exact inv_pos.mpr (by positivity), ?_⟩
  intro y hy ξ hξ
  by_cases hξ0 : ξ = 0
  · simp [hξ0, c₀]
  let d : ℝ := Metric.infDist y Cᶜ
  by_cases hd : d = 0
  · simp [d, hd, c₀]
    rw [mem_dualConeFlat] at hξ
    exact hξ y hy
  have hDual_cone :
      ∀ (η : Fin m → ℝ), η ∈ DualConeFlat C →
        ∀ (t : ℝ), 0 < t → t • η ∈ DualConeFlat C := by
    intro η hη t ht
    rw [mem_dualConeFlat] at hη ⊢
    intro w hw
    have hpair := hη w hw
    calc
      ∑ i, w i * (t • η) i = t * ∑ i, w i * η i := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        simp [Pi.smul_apply]
        ring
      _ ≥ 0 := mul_nonneg ht.le hpair
  have hξ_norm_pos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
  let u : Fin m → ℝ := ‖ξ‖⁻¹ • ξ
  have hu_dual : u ∈ DualConeFlat C := by
    dsimp [u]
    exact hDual_cone ξ hξ ‖ξ‖⁻¹ (inv_pos.mpr hξ_norm_pos)
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hξ_norm_pos.le),
      inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr hξ0
  have hpair_u_lower :
      ‖ξ‖ / ((Fintype.card (Fin m) : ℝ) + 1) ≤ ∑ i, u i * ξ i := by
    have hsum_sq_lower :
        ‖ξ‖ ^ 2 / ((Fintype.card (Fin m) : ℝ) + 1) ≤ ∑ i, ξ i * ξ i := by
      have hs := pairing_self_lower_bound ξ
      have hcard_pos : 0 < ((Fintype.card (Fin m) : ℝ) + 1) := by positivity
      have hs' : ‖ξ‖ ^ 2 ≤ (∑ i, ξ i * ξ i) * ((Fintype.card (Fin m) : ℝ) + 1) := by
        simpa [mul_comm] using hs
      exact (div_le_iff₀ hcard_pos).2 hs'
    have hpair_u_eq : ∑ i, u i * ξ i = ‖ξ‖⁻¹ * ∑ i, ξ i * ξ i := by
      dsimp [u]
      calc
        ∑ i, (‖ξ‖⁻¹ • ξ) i * ξ i = ∑ i, (‖ξ‖⁻¹ * (ξ i * ξ i)) := by
          congr with i
          simp [Pi.smul_apply]
          ring
        _ = ‖ξ‖⁻¹ * ∑ i, ξ i * ξ i := by
          rw [Finset.mul_sum]
    rw [hpair_u_eq]
    have hinv_nonneg : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.mpr hξ_norm_pos.le
    calc
      ‖ξ‖ / ((Fintype.card (Fin m) : ℝ) + 1)
          = ‖ξ‖⁻¹ * (‖ξ‖ ^ 2 / ((Fintype.card (Fin m) : ℝ) + 1)) := by
              field_simp [norm_ne_zero_iff.mpr hξ0,
                show ((Fintype.card (Fin m) : ℝ) + 1) ≠ 0 by linarith]
      _ ≤ ‖ξ‖⁻¹ * ∑ i, ξ i * ξ i := by
            exact mul_le_mul_of_nonneg_left hsum_sq_lower hinv_nonneg
  let t : ℝ := d / 2
  have ht_pos : 0 < t := by
    have hd_nonneg : 0 ≤ d := Metric.infDist_nonneg
    have hd_ne : 0 ≠ d := by simpa [eq_comm] using hd
    have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg hd_ne
    dsimp [t]
    linarith
  have hw_mem : y - t • u ∈ C := by
    by_contra hw_not
    have hw_compl : y - t • u ∈ Cᶜ := hw_not
    have hdist_le : d ≤ dist y (y - t • u) := by
      dsimp [d]
      exact Metric.infDist_le_dist_of_mem hw_compl
    have hdist_eq : dist y (y - t • u) = t := by
      rw [dist_eq_norm]
      calc
        ‖y - (y - t • u)‖ = ‖t • u‖ := by
          congr 1
          ext i
          simp [Pi.sub_apply, sub_eq_add_neg]
        _ = |t| * ‖u‖ := norm_smul _ _
        _ = t := by
          rw [abs_of_nonneg ht_pos.le, hu_norm, mul_one]
    have hlt : dist y (y - t • u) < d := by
      have hd_nonneg : 0 ≤ d := Metric.infDist_nonneg
      have hd_ne : 0 ≠ d := by simpa [eq_comm] using hd
      have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg hd_ne
      rw [hdist_eq]
      dsimp [t]
      nlinarith
    exact (not_lt_of_ge hdist_le) hlt
  have hpair_nonneg : 0 ≤ ∑ i, (y - t • u) i * ξ i := by
    rw [mem_dualConeFlat] at hξ
    exact hξ (y - t • u) hw_mem
  have hmain :
      (d / 2) * (‖ξ‖ / ((Fintype.card (Fin m) : ℝ) + 1)) ≤ ∑ i, y i * ξ i := by
    have hpair_expand :
        ∑ i, (y - t • u) i * ξ i = ∑ i, y i * ξ i - t * ∑ i, u i * ξ i := by
      dsimp [t]
      calc
        ∑ i, (y - (d / 2) • u) i * ξ i
            = ∑ i, (y i * ξ i - ((d / 2) • u) i * ξ i) := by
                congr with i
                simp [Pi.sub_apply]
                ring
        _ = ∑ i, y i * ξ i - ∑ i, ((d / 2) • u) i * ξ i := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ i, y i * ξ i - (d / 2) * ∑ i, u i * ξ i := by
              congr 1
              calc
                ∑ i, ((d / 2) • u) i * ξ i = ∑ i, ((d / 2) * (u i * ξ i)) := by
                  congr with i
                  simp [Pi.smul_apply]
                  ring
                _ = (d / 2) * ∑ i, u i * ξ i := by
                  rw [Finset.mul_sum]
    rw [hpair_expand] at hpair_nonneg
    have hpair_u_lower' :
        t * (‖ξ‖ / ((Fintype.card (Fin m) : ℝ) + 1)) ≤ t * ∑ i, u i * ξ i := by
      exact mul_le_mul_of_nonneg_left hpair_u_lower ht_pos.le
    have haux : t * ∑ i, u i * ξ i ≤ ∑ i, y i * ξ i := by
      nlinarith [hpair_nonneg]
    exact le_trans hpair_u_lower' haux
  dsimp [c₀]
  have hcard_pos : 0 < ((Fintype.card (Fin m) : ℝ) + 1) := by positivity
  calc
    c₀ * Metric.infDist y Cᶜ * ‖ξ‖
        = (d / 2) * (‖ξ‖ / ((Fintype.card (Fin m) : ℝ) + 1)) := by
            dsimp [c₀, d]
            field_simp [show ((Fintype.card (Fin m) : ℝ) + 1) ≠ 0 by linarith]
    _ ≤ ∑ i, y i * ξ i := hmain

private lemma infDist_compl_le_infDist_zero_add_norm
    {m : ℕ} {C : Set (Fin m → ℝ)} (y : Fin m → ℝ) :
    Metric.infDist y Cᶜ ≤ Metric.infDist (0 : Fin m → ℝ) Cᶜ + ‖y‖ := by
  simpa [dist_eq_norm] using
    (Metric.infDist_le_infDist_add_dist (s := Cᶜ) (x := y) (y := (0 : Fin m → ℝ)))

private lemma subsingleton_of_compl_empty
    {m : ℕ} {C : Set (Fin m → ℝ)} (hC_salient : IsSalientCone C)
    (hCempty : Cᶜ = (∅ : Set (Fin m → ℝ))) :
    Subsingleton (Fin m → ℝ) := by
  have hCuniv : C = Set.univ := by
    ext y
    by_cases hy : y ∈ C
    · simp [hy]
    · have : y ∈ Cᶜ := hy
      simpa [hCempty] using this
  refine ⟨fun y₁ y₂ => ?_⟩
  have hy₁ : y₁ = 0 := by
    apply hC_salient y₁
    · simpa [hCuniv]
    · simpa [hCuniv]
  have hy₂ : y₂ = 0 := by
    apply hC_salient y₂
    · simpa [hCuniv]
    · simpa [hCuniv]
  simpa [hy₁, hy₂]

private lemma radius_mul_im_norm_le_one {m : ℕ} (z : Fin m → ℂ) :
    multiDimPsiZRadius z * ‖fun i => (z i).im‖ ≤ 1 := by
  let t : ℝ := ‖fun i => (z i).im‖
  have ht : 0 ≤ t := norm_nonneg _
  calc
    multiDimPsiZRadius z * ‖fun i => (z i).im‖ = t / (1 + t) := by
      simp [multiDimPsiZRadius, t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ 1 := by
      have hden : 0 < 1 + t := by positivity
      rw [div_le_iff₀ hden]
      nlinarith

/-- Pointwise Vladimirov bound: for the dynamically-scaled family,
    `‖ξ‖^k · ‖D^n[ψ_{z,R(z)}](ξ)‖ ≤ B·(1+‖z‖)^N·(1+dist(Im z,∂C)⁻¹)^M` uniformly in ξ.

    This is the key quantitative estimate that converts the qualitative
    `psiZRaw_iteratedFDeriv_decay` into Vladimirov-type polynomial growth.

    **Proof ingredients** (all available in the codebase):
    1. `psiZRaw_iteratedFDeriv_decay` — pointwise bound D(z) for each fixed z
    2. `dualConeFlat_coercivity` — coercivity c(y) for y ∈ C
    3. `schwartz_seminorm_cutoff_exp_bound` — Leibniz + exponential bound
    4. `SCV.pow_mul_exp_neg_le_const` — polynomial vs exponential

    **Tracking D(z)** through the proof of `psiZRaw_iteratedFDeriv_decay`:
    - D = LeibConst · exp(A·R) · M_decay
    - With R = 1/(1+‖y‖): exp(A·R) = exp((c+m²‖y‖)/(1+‖y‖)) ≤ exp(c+m²)
    - LeibConst = Σ C(n,i)·Cχ_i·‖L‖^{n-i} where Cχ_i ~ (1+‖y‖)^i, ‖L‖ ~ ‖z‖
    - M_decay depends on c⁻¹ ~ (infDist(y,∂C))⁻¹

    **Missing ingredient**: a lemma `coercivity_lower_bound_by_infDist` that
    formalizes c(y) ≥ c₀·infDist(y,∂C) for convex cones. This is standard
    convex geometry but not yet in the codebase. -/
/-
Attempted proof route for `multiDimPsiZDynamic_pointwise_vladimirov`:

1. Fix the canonical cone cutoff `χ`.
2. For `z`, set
   `y := Im z`, `d := Metric.infDist y Cᶜ`, `R := multiDimPsiZRadius z`,
   `S := R⁻¹ • ContinuousLinearMap.id`,
   `Lbase ξ := I * ∑ i, z i * ξ_i`,
   `L' := R • Lbase`,
   `g η := χ(η) * exp(L' η)`.
3. Show `psiZRaw χ R z = g ∘ S`.
4. Use `dualConeFlat_coercivity_infDist` to get
   `cEff := R * c₀ * d > 0`.
5. For `χ η ≠ 0`, combine `cexp_bound_on_support` at the scaled point
   `zR := R • z` with
   `Metric.infDist η (DualConeFlat C) ≤ 1`
   to get
   `(L' η).re ≤ A₀ - cEff * ‖η‖`
   where `A₀ := c₀ * Metric.infDist 0 Cᶜ + c₀ + ((card Fin m : ℝ)^2)`.
6. Apply
   `schwartz_seminorm_cutoff_exp_bound_affine_uniform_explicit_uniform`
   to `g`.
7. Pull back along `S` using `iteratedFDeriv_comp_right`, then bound
   `‖S‖ ≤ R⁻¹` and `‖ξ‖^k = R^k * ‖S ξ‖^k`.
8. Convert the resulting factor
   `R^k * cEff⁻¹^k * R⁻n`
   into `(c₀ * d)⁻¹^k * R⁻n`, then bound
   `R⁻¹ ≤ 1 + ‖z‖`,
   `(1 + ‖L'‖)^n ≤ (card + 1)^n * (1 + ‖z‖)^n`,
   `((c₀ * d)⁻¹)^k ≤ c₀⁻¹^k * (1 + d⁻¹)^k`.

What remained formally blocked in Lean:
- rewriting `L' (S η)` to the unscaled exponent without brittle `simp/ring`,
- packaging the `psiZRaw χ R z = g ∘ S` identity in a way `iteratedFDeriv_comp_right`
  accepts cleanly,
- a few commutative-ring normalizations when rearranging the final constant,
- the degenerate branch `Cᶜ = ∅`, which is mathematically trivial but awkward.

So the theorem still looks true and the proof route is stable; the remaining
issue is proof engineering around the rescaling identities, not a missing
mathematical ingredient. -/

-- Scaled cutoff derivative bound: ‖D^i[χ ∘ S](ξ)‖ ≤ Cχ · R⁻ⁱ
private lemma norm_iteratedFDeriv_scaled_cutoff_le
    {m : ℕ} {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    (R : ℝ) (hR : 0 < R) (i : ℕ) :
    ∃ (Ci : ℝ), 0 < Ci ∧ ∀ (ξ : Fin m → ℝ),
      ‖iteratedFDeriv ℝ i (fun η => (χ.val (R⁻¹ • η) : ℂ)) ξ‖ ≤ Ci * R⁻¹ ^ i := by
  -- The function factors as ofRealCLM ∘ χ.val ∘ S where S = R⁻¹ • id
  let S : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := R⁻¹ • ContinuousLinearMap.id ℝ (Fin m → ℝ)
  have hS_norm : ‖S‖ ≤ R⁻¹ := by
    calc ‖S‖ ≤ ‖(R⁻¹ : ℝ)‖ * ‖ContinuousLinearMap.id ℝ (Fin m → ℝ)‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ R⁻¹ * 1 := by
          gcongr
          · exact le_of_eq (Real.norm_of_nonneg (inv_nonneg.mpr hR.le))
          · exact ContinuousLinearMap.norm_id_le
      _ = R⁻¹ := mul_one _
  -- Get uniform bound on χ.val derivatives
  obtain ⟨Cmax, hCmax⟩ := χ.deriv_bound i
  let Ci := |Cmax| + 1
  refine ⟨Ci, by positivity, fun ξ => ?_⟩
  -- D^i[ofRealCLM ∘ χ.val ∘ S](ξ) via chain rule
  have hχS_smooth : ContDiff ℝ ∞ (χ.val ∘ ⇑S) := χ.smooth.comp S.contDiff
  -- Step 1: ofRealCLM is a linear isometry, so doesn't change the norm of iteratedFDeriv
  have hfact : (fun η => (χ.val (R⁻¹ • η) : ℂ)) =
      (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (χ.val ∘ ⇑S) := by
    ext η; simp [S]
  rw [hfact]
  have h_li := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (contDiff_infty.mp hχS_smooth i).contDiffAt le_rfl (x := ξ)
  rw [h_li]
  -- Step 2: Chain rule for χ.val ∘ S
  have hcomp := S.iteratedFDeriv_comp_right χ.smooth ξ
    (show (i : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [hcomp]
  calc ‖(iteratedFDeriv ℝ i (χ.val) (S ξ)).compContinuousLinearMap fun _ => S‖
      ≤ ‖iteratedFDeriv ℝ i (χ.val) (S ξ)‖ * ∏ _ : Fin i, ‖S‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ Ci * R⁻¹ ^ i := by
        calc ‖iteratedFDeriv ℝ i (χ.val) (S ξ)‖ * ∏ _ : Fin i, ‖S‖
            ≤ Ci * ∏ _ : Fin i, R⁻¹ := by
              gcongr with j _
              calc ‖iteratedFDeriv ℝ i (χ.val) (S ξ)‖ ≤ Cmax := hCmax (S ξ)
                _ ≤ |Cmax| := le_abs_self _
                _ ≤ Ci := by linarith
          _ = Ci * R⁻¹ ^ i := by rw [Finset.prod_const, Finset.card_fin]

set_option maxHeartbeats 800000 in
private theorem multiDimPsiZDynamic_pointwise_vladimirov
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (k n : ℕ) :
    ∃ (B : ℝ) (N M : ℕ), B > 0 ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (ξ : Fin m → ℝ),
        ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n
            (⇑(multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz)) ξ‖ ≤
            B * (1 + ‖z‖) ^ N *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M := by
  -- ── Degenerate case: if Cᶜ = ∅ then Fin m → ℝ is subsingleton ──
  by_cases hCcompl : Cᶜ = (∅ : Set (Fin m → ℝ))
  · -- When C = univ, the cone is salient so m = 0 (subsingleton)
    have hsub := subsingleton_of_compl_empty hC_salient hCcompl
    have hCuniv : C = Set.univ := by
      ext y
      by_cases hy : y ∈ C
      · simp [hy]
      · have : y ∈ Cᶜ := hy
        simpa [hCcompl] using this
    have hFinEmpty : IsEmpty (Fin m) := by
      classical
      by_contra hne
      obtain ⟨i⟩ := not_isEmpty_iff.mp hne
      let f : Fin m → ℝ := 0
      let g : Fin m → ℝ := Function.update 0 i 1
      have hfg : f ≠ g := by
        intro h
        have hi' := congrArg (fun h' : Fin m → ℝ => h' i) h
        simp [f, g] at hi'
      exact hfg (hsub.elim _ _)
    let _ : IsEmpty (Fin m) := hFinEmpty
    have hz0 : (0 : Fin m → ℂ) ∈ SCV.TubeDomain C := by
      simp [SCV.TubeDomain, hCuniv]
    let ψ0 := multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient (0 : Fin m → ℂ) hz0
    let B0 : ℝ := ‖iteratedFDeriv ℝ n (⇑ψ0) (0 : Fin m → ℝ)‖ + 1
    refine ⟨B0, 0, 0, by positivity, ?_⟩
    intro z hz ξ
    have hz_eq : z = 0 := Subsingleton.elim _ _
    have hξ_eq : ξ = 0 := Subsingleton.elim _ _
    subst z
    have hhz : hz = hz0 := Subsingleton.elim _ _
    subst hz
    subst ξ
    change ‖(0 : Fin m → ℝ)‖ ^ k *
        ‖iteratedFDeriv ℝ n (⇑ψ0) (0 : Fin m → ℝ)‖ ≤ B0 * (1 + ‖(0 : Fin m → ℂ)‖) ^ 0 *
          (1 + (Metric.infDist (fun i => ((0 : Fin m → ℂ) i).im) Cᶜ)⁻¹) ^ 0
    rw [pow_zero, pow_zero, mul_one, mul_one]
    have hpow : ‖(0 : Fin m → ℝ)‖ ^ k ≤ 1 := by
      cases k with
      | zero =>
          simp
      | succ k =>
          simp
    calc
      ‖(0 : Fin m → ℝ)‖ ^ k * ‖iteratedFDeriv ℝ n (⇑ψ0) (0 : Fin m → ℝ)‖
          ≤ 1 * ‖iteratedFDeriv ℝ n (⇑ψ0) (0 : Fin m → ℝ)‖ := by
              gcongr
      _ ≤ B0 := by
              dsimp [B0]
              linarith [norm_nonneg (iteratedFDeriv ℝ n (⇑ψ0) (0 : Fin m → ℝ))]
  · -- ── Main case: Cᶜ ≠ ∅ ──
    let χ := (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
    obtain ⟨c₀, hc₀_pos, hc₀⟩ := dualConeFlat_coercivity_infDist hC_open hC_cone
    let K : ℝ := (Fintype.card (Fin m) : ℝ) ^ 2
    let A₀ : ℝ := c₀ * (Metric.infDist (0 : Fin m → ℝ) Cᶜ + 1) +
      K
    let K1 : ℝ := (Fintype.card (Fin m) : ℝ) + 1
    choose Cχ0 hCχ0 using χ.deriv_bound
    let Cχ : ℕ → ℝ := fun i => |Cχ0 i| + 1
    obtain ⟨Mexp, hMexp_pos, hMexp⟩ := pow_mul_exp_neg_bounded_explicit_le k
    let LeibConst : ℝ := ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * Cχ i * (n - i).factorial * K1 ^ n
    let B : ℝ := LeibConst * Real.exp A₀ * Mexp * c₀⁻¹ ^ k + 1
    refine ⟨B, 2 * n, k, by positivity, fun z hz ξ => ?_⟩
    let y : Fin m → ℝ := fun i => (z i).im
    have hy : y ∈ C := hz
    let d : ℝ := Metric.infDist y Cᶜ
    have hd_pos : 0 < d := by
      have hCcompl_ne : (Cᶜ : Set (Fin m → ℝ)).Nonempty := by
        rwa [Set.nonempty_iff_ne_empty]
      have hCcompl_closed : IsClosed (Cᶜ : Set (Fin m → ℝ)) :=
        hC_open.isClosed_compl
      exact (hCcompl_closed.notMem_iff_infDist_pos hCcompl_ne).mp (fun h => h hy)
    have hR := multiDimPsiZRadius_pos z
    -- Coercivity for this y: c₀ * d * ‖ξ‖ ≤ ⟨y, ξ⟩ for ξ ∈ DualConeFlat C
    have hc_y : ∀ ξ' ∈ DualConeFlat C, ∑ i, y i * ξ' i ≥ (c₀ * d) * ‖ξ'‖ := by
      intro ξ' hξ'; linarith [hc₀ y hy ξ' hξ']
    have hcd_pos : 0 < c₀ * d := mul_pos hc₀_pos hd_pos
    let R := multiDimPsiZRadius z
    let S : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := R⁻¹ • ContinuousLinearMap.id ℝ (Fin m → ℝ)
    let f : (Fin m → ℝ) → ℂ := fun η => (χ.val (S η) : ℂ)
    let L : (Fin m → ℝ) →L[ℝ] ℂ :=
      ∑ i : Fin m, ((I * z i) : ℂ) •
        (Complex.ofRealCLM.comp
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i))
    let g : (Fin m → ℝ) → ℂ := fun η => cexp (L η)
    have hfg : ∀ η, (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz) η =
        f η * g η := by
      intro η
      show psiZRaw χ (multiDimPsiZRadius z) z η = f η * g η
      simp only [psiZRaw, f, g, L, S, Pi.smul_apply, smul_eq_mul,
        ContinuousLinearMap.coe_sum', Finset.sum_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
        Function.comp, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply,
        ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', id]
      have h1 : (fun i => (multiDimPsiZRadius z)⁻¹ * η i) = (multiDimPsiZRadius z)⁻¹ • η :=
        funext fun i => by rw [Pi.smul_apply, smul_eq_mul]
      rw [h1, Finset.mul_sum]
      simp only [R]; ring
    have hf_smooth : ContDiff ℝ ∞ f :=
      Complex.ofRealCLM.contDiff.comp (χ.smooth.comp S.contDiff)
    have hg_smooth : ContDiff ℝ ∞ g :=
      Complex.contDiff_exp.comp L.contDiff
    -- Step 1: Rewrite using hfg
    have hrw : iteratedFDeriv ℝ n
        (⇑(multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz)) ξ =
        iteratedFDeriv ℝ n (fun η => f η * g η) ξ := by
      congr 1; ext η; exact hfg η
    rw [hrw]
    -- Step 2: Leibniz bound
    have hLeib := norm_iteratedFDeriv_mul_le hf_smooth hg_smooth ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    -- Step 3: Bound ‖D^i[f](ξ)‖
    have hCχ_pos : ∀ i, 0 < Cχ i := by
      intro i
      dsimp [Cχ]
      positivity
    have hCf : ∀ i, ∀ η, ‖iteratedFDeriv ℝ i f η‖ ≤ Cχ i * R⁻¹ ^ i := by
      intro i η
      let S0 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := R⁻¹ • ContinuousLinearMap.id ℝ (Fin m → ℝ)
      have hS0_norm : ‖S0‖ ≤ R⁻¹ := by
        calc ‖S0‖ ≤ ‖(R⁻¹ : ℝ)‖ * ‖ContinuousLinearMap.id ℝ (Fin m → ℝ)‖ :=
              ContinuousLinearMap.opNorm_smul_le _ _
          _ ≤ R⁻¹ * 1 := by
              gcongr
              · exact le_of_eq (Real.norm_of_nonneg (inv_nonneg.mpr hR.le))
              · exact ContinuousLinearMap.norm_id_le
          _ = R⁻¹ := mul_one _
      have hχS_smooth : ContDiff ℝ ∞ (χ.val ∘ ⇑S0) := χ.smooth.comp S0.contDiff
      have hfact : (fun η => (χ.val (R⁻¹ • η) : ℂ)) =
          (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (χ.val ∘ ⇑S0) := by
        ext η'
        simp [S0]
      have h_eq_f : f = (fun η => (χ.val (R⁻¹ • η) : ℂ)) := by
        ext η'
        simp [f, S]
      rw [h_eq_f, hfact]
      have h_li := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
        (contDiff_infty.mp hχS_smooth i).contDiffAt le_rfl (x := η)
      rw [h_li]
      have hcomp := S0.iteratedFDeriv_comp_right χ.smooth η
        (show (i : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
      rw [hcomp]
      calc
        ‖(iteratedFDeriv ℝ i χ.val (S0 η)).compContinuousLinearMap fun _ => S0‖
            ≤ ‖iteratedFDeriv ℝ i χ.val (S0 η)‖ * ∏ _ : Fin i, ‖S0‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ = ‖iteratedFDeriv ℝ i χ.val (S0 η)‖ * ‖S0‖ ^ i := by
              rw [Finset.prod_const, Finset.card_fin]
        _ ≤ |Cχ0 i| * ‖S0‖ ^ i := by
              gcongr
              calc ‖iteratedFDeriv ℝ i χ.val (S0 η)‖ ≤ Cχ0 i := hCχ0 i (S0 η)
                _ ≤ |Cχ0 i| := le_abs_self _
        _ ≤ Cχ i * R⁻¹ ^ i := by
              have habs : |Cχ0 i| ≤ Cχ i := by
                dsimp [Cχ]
                linarith
              have hpow : ‖S0‖ ^ i ≤ R⁻¹ ^ i := by
                exact pow_le_pow_left₀ (norm_nonneg _) hS0_norm i
              gcongr
    -- Step 4: Bound ‖D^j[g](ξ)‖ ≤ j! * ‖cexp(Lξ)‖ * ‖L‖^j
    have hg_bound : ∀ j, ‖iteratedFDeriv ℝ j g ξ‖ ≤
        j.factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ j := by
      intro j
      exact norm_iteratedFDeriv_cexp_comp_clm_le L ξ j
    have hL_apply : ∀ η : Fin m → ℝ, L η = I * ∑ i, z i * (η i : ℂ) := by
      intro η
      simp only [L, ContinuousLinearMap.coe_sum', Finset.sum_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      congr with i
      simp
      ring
    have hL_bound : ‖L‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖z‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro η
      calc
        ‖L η‖ = ‖∑ i : Fin m, z i * (η i : ℂ)‖ := by
          rw [hL_apply]
          simp
        _ ≤ ∑ i : Fin m, ‖z i * (η i : ℂ)‖ := norm_sum_le _ _
        _ = ∑ i : Fin m, ‖z i‖ * ‖η i‖ := by simp [norm_mul]
        _ ≤ ∑ _i : Fin m, ‖z‖ * ‖η‖ := by
          apply Finset.sum_le_sum
          intro i hi
          gcongr
          · exact norm_le_pi_norm z i
          · exact norm_le_pi_norm η i
        _ = (Fintype.card (Fin m) : ℝ) * (‖z‖ * ‖η‖) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ((Fintype.card (Fin m) : ℝ) * ‖z‖) * ‖η‖ := by ring
    have hy_norm_le : ‖y‖ ≤ ‖z‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
      intro i
      calc
        ‖y i‖ = ‖(z i).im‖ := rfl
        _ ≤ ‖z i‖ := by
          simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (z i)
        _ ≤ ‖z‖ := norm_le_pi_norm z i
    have hRinv : R⁻¹ ≤ 1 + ‖z‖ := by
      calc
        R⁻¹ = 1 + ‖y‖ := by
          dsimp [R, y, multiDimPsiZRadius]
          field_simp
        _ ≤ 1 + ‖z‖ := by
          gcongr
    have hK1_nonneg : 0 ≤ K1 := by
      dsimp [K1]
      positivity
    have hLdom : ‖L‖ ≤ K1 * (1 + ‖z‖) := by
      dsimp [K1]
      nlinarith [hL_bound, show (0 : ℝ) ≤ ‖z‖ by positivity]
    have hS_cone : ∀ (η : Fin m → ℝ), η ∈ DualConeFlat C →
        ∀ (t : ℝ), 0 < t → t • η ∈ DualConeFlat C := by
      intro η hη t ht
      rw [mem_dualConeFlat] at hη ⊢
      intro w hw
      have := hη w hw
      simp [Pi.smul_apply, smul_eq_mul]
      calc
        ∑ i, w i * (t * η i) = t * ∑ i, w i * η i := by
          rw [Finset.mul_sum]
          congr 1
          ext i
          ring
        _ ≥ 0 := mul_nonneg (le_of_lt ht) this
    have hsupp_sub : Function.support (fun η : Fin m → ℝ => χ.val (S η)) ⊆
        {η | Metric.infDist η (DualConeFlat C) ≤ R} := by
      intro η hη
      simp only [Function.mem_support] at hη
      by_contra hfar
      have hfar' : R < Metric.infDist η (DualConeFlat C) := lt_of_not_ge hfar
      have hscale :
          Metric.infDist (R⁻¹ • η) (DualConeFlat C) =
            R⁻¹ * Metric.infDist η (DualConeFlat C) :=
        infDist_smul_cone hS_cone (inv_pos.mpr hR) η
      have hmul : R⁻¹ * R < R⁻¹ * Metric.infDist η (DualConeFlat C) :=
        mul_lt_mul_of_pos_left hfar' (inv_pos.mpr hR)
      have hgt : 1 < Metric.infDist (R⁻¹ • η) (DualConeFlat C) := by
        have hgt' : 1 < R⁻¹ * Metric.infDist η (DualConeFlat C) := by
          have hmul' : R / R < R⁻¹ * Metric.infDist η (DualConeFlat C) := by
            simpa [div_eq_mul_inv, mul_comm] using hmul
          have hRR : R / R = 1 := div_self (ne_of_gt hR)
          calc
            1 = R / R := hRR.symm
            _ < R⁻¹ * Metric.infDist η (DualConeFlat C) := hmul'
        simpa [hscale] using hgt'
      exact hη (χ.support_bound (R⁻¹ • η) hgt)
    have hclosed_region :
        IsClosed {η : Fin m → ℝ | Metric.infDist η (DualConeFlat C) ≤ R} :=
      isClosed_le (Metric.continuous_infDist_pt (s := DualConeFlat C)) continuous_const
    have hclosure_sub :
        closure (Function.support (fun η : Fin m → ℝ => χ.val (S η))) ⊆
          {η : Fin m → ℝ | Metric.infDist η (DualConeFlat C) ≤ R} :=
      closure_minimal hsupp_sub hclosed_region
    by_cases hfar : Metric.infDist ξ (DualConeFlat C) > R
    · have hξ_not_closure :
          ξ ∉ closure (Function.support (fun η : Fin m → ℝ => χ.val (S η))) := by
        intro hξ
        exact not_le_of_gt hfar (hclosure_sub hξ)
      have hzeroEv :=
        (product_zero_outside_closure_support
          (fun η : Fin m → ℝ => χ.val (S η)) g ξ hξ_not_closure).iteratedFDeriv ℝ n
      have hzero : iteratedFDeriv ℝ n (fun η : Fin m → ℝ => f η * g η) ξ = 0 := by
        rw [hzeroEv.eq_of_nhds]
        ext η
        simp [f]
      calc
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun η : Fin m → ℝ => f η * g η) ξ‖ = 0 := by
          simp [hzero]
        _ ≤ B * (1 + ‖z‖) ^ (2 * n) *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ k := by positivity
    · have hdist : Metric.infDist ξ (DualConeFlat C) ≤ R := le_of_not_gt hfar
      have hsum_bound :
          ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ *
                ‖iteratedFDeriv ℝ (n - i) g ξ‖
            ≤ LeibConst * ‖g ξ‖ * (1 + ‖z‖) ^ (2 * n) := by
        calc
          ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ *
                ‖iteratedFDeriv ℝ (n - i) g ξ‖
              ≤ ∑ i ∈ Finset.range (n + 1),
                  (n.choose i : ℝ) * (Cχ i * R⁻¹ ^ i) *
                    ((n - i).factorial * ‖g ξ‖ * ‖L‖ ^ (n - i)) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  have hf_i := hCf i ξ
                  have hg_i := hg_bound (n - i)
                  calc
                    (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ *
                        ‖iteratedFDeriv ℝ (n - i) g ξ‖
                        ≤ (n.choose i : ℝ) * (Cχ i * R⁻¹ ^ i) *
                            ‖iteratedFDeriv ℝ (n - i) g ξ‖ := by
                              gcongr
                    _ ≤ (n.choose i : ℝ) * (Cχ i * R⁻¹ ^ i) *
                          ((n - i).factorial * ‖g ξ‖ * ‖L‖ ^ (n - i)) := by
                              gcongr
          _ ≤ ∑ i ∈ Finset.range (n + 1),
                ((n.choose i : ℝ) * Cχ i * (n - i).factorial * K1 ^ n) *
                  (‖g ξ‖ * (1 + ‖z‖) ^ (2 * n)) := by
                apply Finset.sum_le_sum
                intro i hi
                have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                have hbase1 : 1 ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg z]
                have hRi : R⁻¹ ^ i ≤ (1 + ‖z‖) ^ n := by
                  calc
                    R⁻¹ ^ i ≤ (1 + ‖z‖) ^ i := by
                      exact pow_le_pow_left₀ (by positivity) hRinv i
                    _ ≤ (1 + ‖z‖) ^ n := by
                      exact pow_le_pow_right₀ hbase1 hi_le
                have hbase2 : 1 ≤ K1 * (1 + ‖z‖) := by
                  dsimp [K1]
                  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
                  nlinarith
                have hLi : ‖L‖ ^ (n - i) ≤ K1 ^ n * (1 + ‖z‖) ^ n := by
                  calc
                    ‖L‖ ^ (n - i) ≤ (K1 * (1 + ‖z‖)) ^ (n - i) := by
                      exact pow_le_pow_left₀ (by positivity) hLdom (n - i)
                    _ ≤ (K1 * (1 + ‖z‖)) ^ n := by
                      exact pow_le_pow_right₀ hbase2 (Nat.sub_le n i)
                    _ = K1 ^ n * (1 + ‖z‖) ^ n := by rw [mul_pow]
                calc
                  (n.choose i : ℝ) * (Cχ i * R⁻¹ ^ i) *
                      ((n - i).factorial * ‖g ξ‖ * ‖L‖ ^ (n - i))
                    ≤ (n.choose i : ℝ) * (Cχ i * (1 + ‖z‖) ^ n) *
                        ((n - i).factorial * ‖g ξ‖ * ‖L‖ ^ (n - i)) := by
                          gcongr
                  _ ≤ (n.choose i : ℝ) * (Cχ i * (1 + ‖z‖) ^ n) *
                        ((n - i).factorial * ‖g ξ‖ * (K1 ^ n * (1 + ‖z‖) ^ n)) := by
                          gcongr
                  _ = ((n.choose i : ℝ) * Cχ i * (n - i).factorial * K1 ^ n) *
                        (‖g ξ‖ * (1 + ‖z‖) ^ (2 * n)) := by
                          ring_nf
          _ = LeibConst * ‖g ξ‖ * (1 + ‖z‖) ^ (2 * n) := by
                rw [← Finset.sum_mul]
                simp [LeibConst]
                ring
      set_option maxHeartbeats 400000 in
      have hExpBound : ‖g ξ‖ ≤ Real.exp A₀ * Real.exp (-((c₀ * d) * ‖ξ‖)) := by
        calc
          ‖g ξ‖ = ‖cexp (I * ∑ i, z i * (ξ i : ℂ))‖ := by
            rw [show g ξ = cexp (L ξ) by rfl, hL_apply]
          _ ≤ Real.exp ((((c₀ * d) + K * ‖y‖) * R)) *
                Real.exp (-((c₀ * d) * ‖ξ‖)) := by
              simpa [K, y, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
                using cexp_bound_on_support hC_open hC_cone hz hcd_pos hc_y hR ξ hdist
          _ ≤ Real.exp A₀ * Real.exp (-((c₀ * d) * ‖ξ‖)) := by
              have hRle : R ≤ 1 := by
                change (1 + ‖fun i => (z i).im‖)⁻¹ ≤ 1
                have hden : 0 < 1 + ‖fun i => (z i).im‖ := by positivity
                have hone : (1 : ℝ) ≤ 1 + ‖fun i => (z i).im‖ := by
                  exact le_add_of_nonneg_right (norm_nonneg _)
                exact (inv_le_one₀ hden).2 hone
              have hRy : R * ‖y‖ ≤ 1 := radius_mul_im_norm_le_one z
              have hdR : d * R ≤ Metric.infDist (0 : Fin m → ℝ) Cᶜ + 1 := by
                calc
                  d * R ≤ (Metric.infDist (0 : Fin m → ℝ) Cᶜ + ‖y‖) * R := by
                    have hd_le : d ≤ Metric.infDist (0 : Fin m → ℝ) Cᶜ + ‖y‖ :=
                      infDist_compl_le_infDist_zero_add_norm y
                    exact mul_le_mul_of_nonneg_right hd_le hR.le
                  _ = Metric.infDist (0 : Fin m → ℝ) Cᶜ * R + ‖y‖ * R := by ring
                  _ ≤ Metric.infDist (0 : Fin m → ℝ) Cᶜ * 1 + 1 := by
                    have h0 : 0 ≤ Metric.infDist (0 : Fin m → ℝ) Cᶜ := Metric.infDist_nonneg
                    have hleft :
                        Metric.infDist (0 : Fin m → ℝ) Cᶜ * R ≤
                          Metric.infDist (0 : Fin m → ℝ) Cᶜ * 1 :=
                      mul_le_mul_of_nonneg_left hRle h0
                    have hright : ‖y‖ * R ≤ 1 := by
                      simpa [mul_comm] using hRy
                    exact add_le_add hleft hright
                  _ = Metric.infDist (0 : Fin m → ℝ) Cᶜ + 1 := by ring
              have hterm1 : c₀ * d * R ≤ c₀ * (Metric.infDist (0 : Fin m → ℝ) Cᶜ + 1) := by
                have := mul_le_mul_of_nonneg_left hdR hc₀_pos.le
                simpa [mul_assoc] using this
              have hterm2 : K * ‖y‖ * R ≤ K := by
                calc
                  K * ‖y‖ * R = K * (R * ‖y‖) := by ring
                  _ ≤ K * 1 := by gcongr
                  _ = K := by ring
              have hA0bound : ((c₀ * d) + K * ‖y‖) * R ≤ A₀ := by
                calc
                  ((c₀ * d) + K * ‖y‖) * R
                      = c₀ * d * R + K * ‖y‖ * R := by ring
                  _ ≤ c₀ * (Metric.infDist (0 : Fin m → ℝ) Cᶜ + 1) + K := by
                      gcongr
                  _ = A₀ := by dsimp [A₀]
              have hExpA : Real.exp ((((c₀ * d) + K * ‖y‖) * R)) ≤ Real.exp A₀ :=
                Real.exp_le_exp.mpr hA0bound
              exact mul_le_mul_of_nonneg_right hExpA (Real.exp_pos _).le
      have hscaled :
          ‖ξ‖ ^ k * Real.exp (-((c₀ * d) * ‖ξ‖)) ≤ Mexp * (c₀ * d)⁻¹ ^ k := by
        simpa [mul_comm] using hMexp (c₀ * d) hcd_pos ‖ξ‖ (norm_nonneg _)
      set_option maxHeartbeats 400000 in
      have hdinv :
          (c₀ * d)⁻¹ ^ k ≤ c₀⁻¹ ^ k * (1 + d⁻¹) ^ k := by
        have hdpow : d⁻¹ ^ k ≤ (1 + d⁻¹) ^ k := by
          have : d⁻¹ ≤ 1 + d⁻¹ := by linarith
          exact pow_le_pow_left₀ (by positivity) this k
        have hcd_eq : (c₀ * d)⁻¹ ^ k = c₀⁻¹ ^ k * d⁻¹ ^ k := by
          rw [show (c₀ * d)⁻¹ = c₀⁻¹ * d⁻¹ by
                rw [mul_inv_rev, mul_comm], mul_pow]
        calc
          (c₀ * d)⁻¹ ^ k = c₀⁻¹ ^ k * d⁻¹ ^ k := hcd_eq
          _ ≤ c₀⁻¹ ^ k * (1 + d⁻¹) ^ k := by
            exact mul_le_mul_of_nonneg_left hdpow (by positivity)
      calc
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun η => f η * g η) ξ‖
            ≤ ‖ξ‖ ^ k *
                ∑ i ∈ Finset.range (n + 1),
                  (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ *
                    ‖iteratedFDeriv ℝ (n - i) g ξ‖ := by
              gcongr
              exact hLeib
        _ ≤ ‖ξ‖ ^ k * (LeibConst * ‖g ξ‖ * (1 + ‖z‖) ^ (2 * n)) := by
              gcongr
        _ = LeibConst * (1 + ‖z‖) ^ (2 * n) * (‖ξ‖ ^ k * ‖g ξ‖) := by ring
        _ ≤ LeibConst * (1 + ‖z‖) ^ (2 * n) *
              (‖ξ‖ ^ k * (Real.exp A₀ * Real.exp (-((c₀ * d) * ‖ξ‖)))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left hExpBound (by positivity)
        _ = LeibConst * Real.exp A₀ * (1 + ‖z‖) ^ (2 * n) *
              (‖ξ‖ ^ k * Real.exp (-((c₀ * d) * ‖ξ‖))) := by ring
        _ ≤ LeibConst * Real.exp A₀ * (1 + ‖z‖) ^ (2 * n) *
              (Mexp * (c₀ * d)⁻¹ ^ k) := by
              gcongr
        _ ≤ LeibConst * Real.exp A₀ * (1 + ‖z‖) ^ (2 * n) *
              (Mexp * (c₀⁻¹ ^ k * (1 + d⁻¹) ^ k)) := by
              gcongr
        _ = (LeibConst * Real.exp A₀ * Mexp * c₀⁻¹ ^ k) *
              (1 + ‖z‖) ^ (2 * n) * (1 + d⁻¹) ^ k := by ring
        _ ≤ B * (1 + ‖z‖) ^ (2 * n) *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ k := by
              have hcoeff : LeibConst * Real.exp A₀ * Mexp * c₀⁻¹ ^ k ≤ B := by
                have hnonneg : 0 ≤ LeibConst * Real.exp A₀ * Mexp * c₀⁻¹ ^ k := by positivity
                calc
                  LeibConst * Real.exp A₀ * Mexp * c₀⁻¹ ^ k
                      ≤ LeibConst * Real.exp A₀ * Mexp * c₀⁻¹ ^ k + 1 := by linarith
                  _ = B := by dsimp [B]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity)

/-! ### Seminorm bounds for the multi-D family -/

/-- **Quantitative polynomial seminorm bound for psiZRSchwartz with dynamic scaling.**

    For the dynamically scaled family psiZR with R = 1/(1+‖y‖), the Schwartz
    (k,n)-seminorm has polynomial growth in ‖z‖.

    **Proof sketch** (Vladimirov, §25, Lemma 25.1):
    The function is psiZRaw χ R z ξ = χ(ξ/R) · exp(iz·ξ) with R = 1/(1+‖Im z‖).

    Step 1: `psiZRaw_iteratedFDeriv_decay` gives ∃ D(z,R,k,n), ∀ ξ,
      ‖ξ‖^k · ‖D^n[psiZRaw](ξ)‖ ≤ D
    This D is then a valid bound for `seminorm_le_bound`.

    Step 2: Track D's dependence on z. From the proof of psiZRaw_iteratedFDeriv_decay:
    - D = LeibConst · exp(A·R) · M, where:
      · A = c(y) + m² · ‖Im z‖, c(y) = coercivity constant
      · LeibConst ~ Σ C(n,i) · Cχ_i(R) · ‖L‖^{n-i}
      · ‖L‖ ~ ‖z‖ (the linear exponent map)
      · Cχ_i(R) ~ R^{-i} = (1+‖Im z‖)^i (chain rule for χ(·/R))
      · M comes from poly-vs-exp bound (independent of z)

    Step 3: With R = 1/(1+‖Im z‖):
    - exp(A·R) = exp((c + m²‖y‖)/(1+‖y‖)) ≤ exp(c + m²) = constant
    - LeibConst ≤ C'·(1+‖z‖)^n·(1+‖Im z‖)^n
    - c(y) ≥ δ > 0 where δ ~ infDist(Im z, ∂C) by cone geometry
    - The coercivity constant c enters through M's dependence on c⁻¹

    Step 4: Altogether: seminorm ≤ D ≤ B·(1+‖z‖)^N·(1+dist(Im z,∂C)⁻¹)^M.

    The sorry below is in the quantitative tracking of constants (Step 2-4).
    The pointwise decay (Step 1) is fully proved in `psiZRaw_iteratedFDeriv_decay`. -/
theorem psiZRSchwartz_seminorm_vladimirovBound
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (k n : ℕ) :
    ∃ (B : ℝ) (N M : ℕ), B > 0 ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
        SchwartzMap.seminorm ℝ k n
          (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz) ≤
            B * (1 + ‖z‖) ^ N *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M := by
  -- Get the quantitative pointwise bound
  obtain ⟨B, N, M_exp, hB, hpw⟩ :=
    multiDimPsiZDynamic_pointwise_vladimirov hC_open hC_conv hC_cone hC_salient k n
  refine ⟨B, N, M_exp, hB, fun z hz => ?_⟩
  -- Apply seminorm_le_bound to convert pointwise bound to seminorm bound.
  -- seminorm_le_bound : (∀ x, ‖x‖^k * ‖D^n f x‖ ≤ M) → seminorm 𝕜 k n f ≤ M
  -- We need to provide M and the SchwartzMap explicitly.
  let f := multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz
  let M := B * (1 + ‖z‖) ^ N * (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M_exp
  show SchwartzMap.seminorm ℝ k n f ≤ M
  have hdist_nn : (0 : ℝ) ≤ 1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹ := by
    have : 0 ≤ Metric.infDist (fun i => (z i).im) Cᶜ := Metric.infDist_nonneg
    linarith [inv_nonneg.mpr this]
  have hMnn : 0 ≤ M := by
    apply mul_nonneg
    · apply mul_nonneg (le_of_lt hB)
      exact pow_nonneg (by linarith [norm_nonneg z]) _
    · exact pow_nonneg hdist_nn _
  exact SchwartzMap.seminorm_le_bound ℝ k n f hMnn (hpw z hz)

private def multiDimPsiExpCLM {m : ℕ} (z : Fin m → ℂ) :
    (Fin m → ℝ) →L[ℝ] ℂ :=
  ∑ i : Fin m, ((I * z i) : ℂ) •
    (Complex.ofRealCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i))

private lemma multiDimPsiExpCLM_apply {m : ℕ} (z : Fin m → ℂ) (ξ : Fin m → ℝ) :
    multiDimPsiExpCLM z ξ = I * ∑ i, z i * (ξ i : ℂ) := by
  simp only [multiDimPsiExpCLM, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr with i
  simp
  ring

private lemma multiDimPsiExpCLM_norm_le {m : ℕ} (z : Fin m → ℂ) :
    ‖multiDimPsiExpCLM z‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  calc
    ‖multiDimPsiExpCLM z ξ‖ = ‖∑ i : Fin m, z i * (ξ i : ℂ)‖ := by
      rw [multiDimPsiExpCLM_apply]
      simp
    _ ≤ ∑ i : Fin m, ‖z i * (ξ i : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i : Fin m, ‖z i‖ * ‖ξ i‖ := by
      simp [norm_mul]
    _ ≤ ∑ _i : Fin m, ‖z‖ * ‖ξ‖ := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact norm_le_pi_norm z i
      · exact norm_le_pi_norm ξ i
    _ = (Fintype.card (Fin m) : ℝ) * (‖z‖ * ‖ξ‖) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((Fintype.card (Fin m) : ℝ) * ‖z‖) * ‖ξ‖ := by ring

private lemma imag_norm_sub_le {m : ℕ} (z z₀ : Fin m → ℂ) :
    ‖(fun i => (z i).im) - fun i => (z₀ i).im‖ ≤ ‖z - z₀‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro i
  calc
    ‖((fun i => (z i).im) - fun i => (z₀ i).im) i‖ = ‖((z - z₀) i).im‖ := by
      simp [Pi.sub_apply]
    _ ≤ ‖(z - z₀) i‖ := by
      simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm ((z - z₀) i)
    _ ≤ ‖z - z₀‖ := norm_le_pi_norm (z - z₀) i

private lemma imag_norm_le {m : ℕ} (z : Fin m → ℂ) :
    ‖fun i => (z i).im‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro i
  calc
    ‖(fun i => (z i).im) i‖ = ‖(z i).im‖ := rfl
    _ ≤ ‖z i‖ := by
      simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (z i)
    _ ≤ ‖z‖ := norm_le_pi_norm z i

private lemma pairing_abs_le_card_sq {m : ℕ} (y ξ : Fin m → ℝ) :
    |∑ i, y i * ξ i| ≤ ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖y‖ * ‖ξ‖ := by
  have hy_sum :
      ∑ i, ‖y i‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖y‖ := by
    simpa [nsmul_eq_mul] using (Pi.sum_norm_apply_le_norm y)
  have hξ_sum :
      ∑ i, ‖ξ i‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖ξ‖ := by
    simpa [nsmul_eq_mul] using (Pi.sum_norm_apply_le_norm ξ)
  have hnorm :
      ‖∑ i, y i * ξ i‖ ≤ ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖y‖ * ‖ξ‖ := by
    calc
      ‖∑ i, y i * ξ i‖ ≤ ∑ i, ‖y i * ξ i‖ := norm_sum_le _ _
      _ = ∑ i, ‖y i‖ * ‖ξ i‖ := by simp [norm_mul]
      _ ≤ ∑ i, ∑ j, ‖y i‖ * ‖ξ j‖ := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun j : Fin m => ‖y i‖ * ‖ξ j‖)
            (fun j hj => mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (Finset.mem_univ i)
      _ = (∑ i, ‖y i‖) * ∑ j, ‖ξ j‖ := by rw [Finset.sum_mul_sum]
      _ ≤ ((Fintype.card (Fin m) : ℝ) * ‖y‖) * ((Fintype.card (Fin m) : ℝ) * ‖ξ‖) := by
          gcongr
      _ = ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖y‖ * ‖ξ‖ := by ring
  simpa [Real.norm_eq_abs] using hnorm

private lemma dualConeFlat_coercivity_perturb
    {m : ℕ} {C : Set (Fin m → ℝ)} {y₀ y : Fin m → ℝ} {c₀ : ℝ}
    (hc₀ : ∀ ξ ∈ DualConeFlat C, ∑ i, y₀ i * ξ i ≥ c₀ * ‖ξ‖)
    (hy : ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖y - y₀‖ ≤ c₀ / 2) :
    ∀ ξ ∈ DualConeFlat C, ∑ i, y i * ξ i ≥ (c₀ / 2) * ‖ξ‖ := by
  intro ξ hξ
  have herrabs : |∑ i, (y - y₀) i * ξ i| ≤
      ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖y - y₀‖ * ‖ξ‖ :=
    pairing_abs_le_card_sq (y - y₀) ξ
  have herr :
      -(((Fintype.card (Fin m) : ℝ) ^ 2) * ‖y - y₀‖ * ‖ξ‖) ≤
        ∑ i, (y - y₀) i * ξ i := by
    nlinarith [abs_le.mp herrabs |>.1]
  have herr' :
      ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖y - y₀‖ * ‖ξ‖ ≤ (c₀ / 2) * ‖ξ‖ := by
    exact mul_le_mul_of_nonneg_right hy (norm_nonneg ξ)
  calc
    ∑ i, y i * ξ i = ∑ i, ((y₀ i + (y - y₀) i) * ξ i) := by
      congr with i
      have hyi : y i = y₀ i + (y - y₀) i := by
        simp [Pi.sub_apply, sub_eq_add_neg, add_assoc]
      rw [hyi]
    _ = ∑ i, (y₀ i * ξ i + (y - y₀) i * ξ i) := by
      congr with i
      ring
    _ = ∑ i, y₀ i * ξ i + ∑ i, (y - y₀) i * ξ i := by
      rw [Finset.sum_add_distrib]
    _ ≥ c₀ * ‖ξ‖ - (((Fintype.card (Fin m) : ℝ) ^ 2) * ‖y - y₀‖ * ‖ξ‖) := by
      nlinarith [hc₀ ξ hξ, herr]
    _ ≥ (c₀ / 2) * ‖ξ‖ := by
      nlinarith [herr']

/-- **Local fixed-radius uniform seminorm bound for `multiDimPsiZ`.**

    For each base point `z₀ ∈ T(C)` and each Schwartz seminorm `(k,n)`, there is
    a tube neighborhood of `z₀` on which the radius-`1` family `multiDimPsiZ`
    is uniformly bounded in that seminorm.

    This is the local compactness/uniformity input needed for the quantitative
    difference and difference-quotient estimates below. -/
theorem multiDimPsiZ_local_uniform_seminorm_bound
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (k n : ℕ)
    (z₀ : Fin m → ℂ) (hz₀ : z₀ ∈ SCV.TubeDomain C) :
    ∃ (B δ₀ : ℝ), 0 < B ∧ 0 < δ₀ ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
        ‖z - z₀‖ < δ₀ →
          SchwartzMap.seminorm ℝ k n
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) ≤ B := by
  let χ : FixedConeCutoff (DualConeFlat C) :=
    (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  let y₀ : Fin m → ℝ := fun i => (z₀ i).im
  have hy₀ : y₀ ∈ C := hz₀
  have hC_star_ne : (DualConeFlat C).Nonempty := ⟨0, zero_mem_dualConeFlat C⟩
  have hC_star_closed : IsClosed (DualConeFlat C) := dualConeFlat_closed C
  obtain ⟨c₀, hc₀_pos, hc₀⟩ :=
    dualConeFlat_coercivity hC_open hC_cone hy₀ hC_star_ne hC_star_closed
  let K : ℝ := ((Fintype.card (Fin m) : ℝ) ^ 2)
  let δ₀ : ℝ := c₀ / (2 * (K + 1))
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    positivity
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hKδ₀ : K * δ₀ ≤ c₀ / 2 := by
    have haux : K * c₀ ≤ c₀ * (K + 1) := by
      nlinarith [hK_nonneg, hc₀_pos]
    calc
      K * δ₀ = (K * c₀) / (2 * (K + 1)) := by
        dsimp [δ₀]
        ring
      _ ≤ (c₀ * (K + 1)) / (2 * (K + 1)) := by
        exact div_le_div_of_nonneg_right haux (by positivity)
      _ = c₀ / 2 := by
        field_simp [show (K + 1) ≠ 0 by linarith]
  let A₀ : ℝ := c₀ / 2 + K * (‖y₀‖ + δ₀)
  let L₀ : ℝ := (Fintype.card (Fin m) : ℝ) * (‖z₀‖ + δ₀)
  obtain ⟨Bexp, hBexp_pos, hBexp⟩ :=
    schwartz_seminorm_cutoff_exp_bound_affine_uniform
      χ.val χ.smooth χ.deriv_bound A₀ (c₀ / 2) (by positivity) k n
  let B : ℝ := Bexp * (1 + L₀) ^ n
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨B, δ₀, hB_pos, hδ₀_pos, ?_⟩
  intro z hz hzdist
  let y : Fin m → ℝ := fun i => (z i).im
  have hy_close : K * ‖y - y₀‖ ≤ c₀ / 2 := by
    calc
      K * ‖y - y₀‖ ≤ K * ‖z - z₀‖ := by
        gcongr
        exact imag_norm_sub_le z z₀
      _ ≤ K * δ₀ := by
        nlinarith [hK_nonneg, le_of_lt hzdist]
      _ ≤ c₀ / 2 := hKδ₀
  have hc_z :
      ∀ ξ ∈ DualConeFlat C, ∑ i, y i * ξ i ≥ (c₀ / 2) * ‖ξ‖ :=
    dualConeFlat_coercivity_perturb hc₀ hy_close
  have hy_norm : ‖y‖ ≤ ‖y₀‖ + δ₀ := by
    calc
      ‖y‖ = ‖(y - y₀) + y₀‖ := by
        congr 1
        ext i
        simp [y, y₀]
      _ ≤ ‖y - y₀‖ + ‖y₀‖ := norm_add_le _ _
      _ ≤ ‖z - z₀‖ + ‖y₀‖ := by
        gcongr
        exact imag_norm_sub_le z z₀
      _ ≤ ‖y₀‖ + δ₀ := by
        linarith
  have hz_norm : ‖z‖ ≤ ‖z₀‖ + δ₀ := by
    calc
      ‖z‖ = ‖(z - z₀) + z₀‖ := by
        congr 1
        ext i
        simp
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + δ₀ := by
        linarith
  have hL₀ : ‖multiDimPsiExpCLM z‖ ≤ L₀ := by
    calc
      ‖multiDimPsiExpCLM z‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖z‖ :=
        multiDimPsiExpCLM_norm_le z
      _ ≤ (Fintype.card (Fin m) : ℝ) * (‖z₀‖ + δ₀) := by
        gcongr
      _ = L₀ := by
        rfl
  have hexp_decay :
      ∀ ξ : Fin m → ℝ, χ.val ξ ≠ 0 →
        (multiDimPsiExpCLM z ξ).re ≤ A₀ - (c₀ / 2) * ‖ξ‖ := by
    intro ξ hχξ
    have hdistχ : Metric.infDist ξ (DualConeFlat C) ≤ 1 := by
      by_contra h
      exact hχξ (χ.support_bound ξ (by linarith))
    have hExpBound :
        ‖cexp (multiDimPsiExpCLM z ξ)‖ ≤
          Real.exp A₀ * Real.exp (-((c₀ / 2) * ‖ξ‖)) := by
      calc
        ‖cexp (multiDimPsiExpCLM z ξ)‖
            = ‖cexp (I * ∑ i, z i * (ξ i : ℂ))‖ := by
                rw [multiDimPsiExpCLM_apply]
        _ ≤ Real.exp (((c₀ / 2) + K * ‖y‖) * 1) *
              Real.exp (-((c₀ / 2) * ‖ξ‖)) := by
                simpa [K, y] using
                  cexp_bound_on_support hC_open hC_cone hz (by positivity) hc_z zero_lt_one ξ hdistχ
        _ ≤ Real.exp A₀ * Real.exp (-((c₀ / 2) * ‖ξ‖)) := by
          gcongr
          dsimp [A₀]
          nlinarith
    have hnormexp : ‖cexp (multiDimPsiExpCLM z ξ)‖ = Real.exp ((multiDimPsiExpCLM z ξ).re) := by
      rw [Complex.norm_exp]
    have hExp' :
        Real.exp ((multiDimPsiExpCLM z ξ).re) ≤
          Real.exp (A₀ - (c₀ / 2) * ‖ξ‖) := by
      rw [← hnormexp]
      simpa [sub_eq_add_neg, Real.exp_add] using hExpBound
    exact Real.exp_le_exp.mp hExp'
  have hpoint :
      ∀ ξ : Fin m → ℝ,
        ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n
              (fun ξ => (χ.val ξ : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))) ξ‖ ≤ B := by
    intro ξ
    have hraw := hBexp (multiDimPsiExpCLM z) hexp_decay ξ
    have hfunexp :
        (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))) =
          (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ) * cexp (multiDimPsiExpCLM z ξ)) := by
      funext ξ
      rw [multiDimPsiExpCLM_apply]
    calc
      ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n
              (fun ξ => (χ.val ξ : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))) ξ‖
        = ‖ξ‖ ^ k *
            ‖iteratedFDeriv ℝ n
                (fun ξ => (χ.val ξ : ℂ) * cexp (multiDimPsiExpCLM z ξ)) ξ‖ := by
            rw [hfunexp]
      _ ≤ Bexp * (1 + ‖multiDimPsiExpCLM z‖) ^ n := hraw
      _ ≤ Bexp * (1 + L₀) ^ n := by
        have hbase : 1 + ‖multiDimPsiExpCLM z‖ ≤ 1 + L₀ := by
          linarith [hL₀]
        apply mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hbase n) (le_of_lt hBexp_pos)
      _ = B := by
        rfl
  have hpoint' :
      ∀ ξ : Fin m → ℝ,
        ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n
              (⇑(psiZRSchwartz hC_open hC_cone hC_salient χ 1 zero_lt_one z hz)) ξ‖ ≤ B := by
    intro ξ
    have hcoe :
        ⇑(psiZRSchwartz hC_open hC_cone hC_salient χ 1 zero_lt_one z hz) = psiZRaw χ 1 z := rfl
    have hrawfun :
        psiZRaw χ 1 z =
          (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))) := by
      funext ξ
      simp [psiZRaw]
    rw [hcoe]
    rw [hrawfun]
    exact hpoint ξ
  have hseminorm :
      SchwartzMap.seminorm ℝ k n
        (psiZRSchwartz hC_open hC_cone hC_salient χ 1 zero_lt_one z hz) ≤ B := by
    exact SchwartzMap.seminorm_le_bound ℝ k n
      (psiZRSchwartz hC_open hC_cone hC_salient χ 1 zero_lt_one z hz)
      (le_of_lt hB_pos) hpoint'
  simpa [multiDimPsiZ, multiDimPsiZR, χ] using hseminorm

/-- **Local uniform seminorm bound after multiplying by a coordinate monomial.**

    For fixed coordinate `j` and power `r`, the coordinate-weighted family
    `ξ ↦ (ξ_j)^r ψ_z(ξ)` is uniformly bounded in every Schwartz seminorm for
    `z` in a sufficiently small tube neighborhood of `z₀`.

    This is the local uniformity input needed for the Taylor remainder kernel in
    the difference-quotient estimate (`r = 2`) and for the first-order expansion
    used in the difference estimate (`r = 1`). -/
theorem multiDimPsiZ_local_uniform_coordPow_seminorm_bound
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (j : Fin m) (r k n : ℕ)
    (z₀ : Fin m → ℂ) (hz₀ : z₀ ∈ SCV.TubeDomain C) :
    ∃ (B δ₀ : ℝ), 0 < B ∧ 0 < δ₀ ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
        ‖z - z₀‖ < δ₀ →
          SchwartzMap.seminorm ℝ k n
            (SchwartzMap.smulLeftCLM ℂ
              (fun ξ : Fin m → ℝ => (((ξ j) ^ r : ℝ) : ℂ))
              (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)) ≤ B := by
  let L : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun ξ : Fin m → ℝ => (((ξ j) ^ r : ℝ) : ℂ))
  let q : Seminorm ℝ (SchwartzMap (Fin m → ℝ) ℂ) :=
    (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ (k, n)).comp
      (L.restrictScalars ℝ).toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun g : SchwartzMap (Fin m → ℝ) ℂ =>
      schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ (k, n) (L g))
    exact ((schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).continuous_seminorm (k, n)).comp
      L.continuous
  obtain ⟨s, C_L, hC_L_ne, hbound_L⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ) q hq_cont
  have hC_L_pos : 0 < (C_L : ℝ) := by
    rcases eq_or_lt_of_le C_L.coe_nonneg with h | h
    · exact absurd (NNReal.coe_eq_zero.mp h.symm) hC_L_ne
    · exact h
  have hsum :
      ∀ s : Finset (ℕ × ℕ),
        ∃ (B_sum δ_sum : ℝ), 0 < B_sum ∧ 0 < δ_sum ∧
          ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C), ‖z - z₀‖ < δ_sum →
            ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2
              (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) ≤ B_sum := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
        intro z hz hzdist
        simp
    | insert p s hp ih =>
        obtain ⟨B_s, δ_s, hB_s, hδ_s, hs_bound⟩ := ih
        obtain ⟨B_p, δ_p, hB_p, hδ_p, hp_bound⟩ :=
          multiDimPsiZ_local_uniform_seminorm_bound
            hC_open hC_conv hC_cone hC_salient p.1 p.2 z₀ hz₀
        refine ⟨B_p + B_s, min δ_s δ_p, add_pos hB_p hB_s, lt_min hδ_s hδ_p, ?_⟩
        intro z hz hzdist
        rw [Finset.sum_insert hp]
        exact add_le_add
          (hp_bound z hz (lt_of_lt_of_le hzdist (min_le_right _ _)))
          (hs_bound z hz (lt_of_lt_of_le hzdist (min_le_left _ _)))
  obtain ⟨B_sum, δ_sum, hB_sum, hδ_sum, hsum_bound⟩ := hsum s
  refine ⟨(C_L : ℝ) * B_sum, δ_sum, mul_pos hC_L_pos hB_sum, hδ_sum, ?_⟩
  intro z hz hzdist
  have hsum_apply :
      ∀ s : Finset (ℕ × ℕ),
        (∑ i ∈ s, schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ i)
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) =
          ∑ p ∈ s,
            (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p)
              (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | insert a s ha ih =>
        simp [ha, Seminorm.add_apply, ih]
  have hsup :
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) ≤
        ∑ p ∈ s,
          (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p)
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) := by
      calc
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)
        ≤ (∑ i ∈ s, schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ i)
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) :=
          Seminorm.le_def.mp
            (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) s)
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)
      _ = ∑ p ∈ s,
            (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p)
              (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) := hsum_apply s
  calc
    SchwartzMap.seminorm ℝ k n
        (SchwartzMap.smulLeftCLM ℂ
          (fun ξ : Fin m → ℝ => (((ξ j) ^ r : ℝ) : ℂ))
          (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz))
      = q (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) := by
          rfl
    _ ≤ (C_L • s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) :=
          hbound_L _
    _ = (C_L : ℝ) *
          (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) := by
          rfl
    _ ≤ (C_L : ℝ) * ∑ p ∈ s,
          (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p)
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) := by
          exact mul_le_mul_of_nonneg_left hsup C_L.coe_nonneg
    _ = (C_L : ℝ) * ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2
          (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) := by
          simp [schwartzSeminormFamily]
    _ ≤ (C_L : ℝ) * B_sum := by
          apply mul_le_mul_of_nonneg_left (hsum_bound z hz hzdist) C_L.coe_nonneg

private def multiDimPsiZCoordDeriv
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ : Fin m → ℝ => I * (ξ j : ℂ))
    (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)

private lemma multiDimPsiZCoordDeriv_apply
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m)
    (ξ : Fin m → ℝ) :
    multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j ξ =
      (I * (ξ j : ℂ)) * multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ := by
  have hcoord : (fun η : Fin m → ℝ => (η j : ℂ)).HasTemperateGrowth := by
    simpa using
      (Complex.ofRealCLM.comp
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) j)).hasTemperateGrowth
  have htemp : (fun η : Fin m → ℝ => I * (η j : ℂ)).HasTemperateGrowth := by
    exact (Function.HasTemperateGrowth.const I).mul hcoord
  simpa [multiDimPsiZCoordDeriv, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply_apply htemp
      (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) ξ)

private lemma multiDimPsiZ_update_apply_eq_mul_cexp
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) (h : ℂ)
    (hz' : Function.update z j (z j + h) ∈ SCV.TubeDomain C)
    (ξ : Fin m → ℝ) :
    multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
        (Function.update z j (z j + h)) hz' ξ =
      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ * cexp (I * h * (ξ j : ℂ)) := by
  let χ : FixedConeCutoff (DualConeFlat C) :=
    (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  change psiZRaw χ 1 (Function.update z j (z j + h)) ξ =
      psiZRaw χ 1 z ξ * cexp (I * h * (ξ j : ℂ))
  simp only [psiZRaw, mul_assoc]
  have hsum :
      (∑ i, Function.update z j (z j + h) i * (ξ i : ℂ)) =
        (∑ i, z i * (ξ i : ℂ)) + h * (ξ j : ℂ) := by
    calc
      ∑ i, Function.update z j (z j + h) i * (ξ i : ℂ)
          = ∑ i, ((z i) + if i = j then h else 0) * (ξ i : ℂ) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hij : i = j
              · subst hij
                simp [Function.update_self]
              · simp [Function.update_of_ne hij, hij]
      _ = ∑ i, (z i * (ξ i : ℂ) + (if i = j then h else 0) * (ξ i : ℂ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i, z i * (ξ i : ℂ)) + ∑ i, (if i = j then h else 0) * (ξ i : ℂ) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i, z i * (ξ i : ℂ)) + h * (ξ j : ℂ) := by
            simp
  rw [hsum, mul_add, Complex.exp_add]

private lemma multiDimPsiZ_update_sub_sub_coordDeriv_apply
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) (h : ℂ)
    (hz' : Function.update z j (z j + h) ∈ SCV.TubeDomain C)
    (ξ : Fin m → ℝ) :
    multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
        (Function.update z j (z j + h)) hz' ξ -
      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ -
      h * multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j ξ =
      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ *
          (cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)) := by
  rw [multiDimPsiZ_update_apply_eq_mul_cexp hC_open hC_conv hC_cone hC_salient z hz j h hz' ξ,
    multiDimPsiZCoordDeriv_apply hC_open hC_conv hC_cone hC_salient z hz j ξ]
  ring

private lemma hasDerivAt_psiZRaw_update_apply
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (χ : FixedConeCutoff (DualConeFlat C))
    (z : Fin m → ℂ) (j : Fin m) (h : ℂ) (ξ : Fin m → ℝ) (s : ℝ) :
    HasDerivAt
      (fun t : ℝ => psiZRaw χ 1 (Function.update z j (z j + (t : ℂ) * h)) ξ)
      (((I * h * (ξ j : ℂ)) : ℂ) *
        psiZRaw χ 1 (Function.update z j (z j + (s : ℂ) * h)) ξ)
      s := by
  have hcoord :
      HasDerivAt (fun t : ℝ => z j + (t : ℂ) * h) h s := by
    simpa [one_mul] using (Complex.ofRealCLM.hasDerivAt.mul_const h).const_add (z j)
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ i, Function.update z j (z j + (t : ℂ) * h) i * (ξ i : ℂ))
        (h * (ξ j : ℂ))
        s := by
    have hsum' :
        HasDerivAt
          (fun t : ℝ => ∑ i : Fin m,
            Function.update z j (z j + (t : ℂ) * h) i * (ξ i : ℂ))
          (∑ i : Fin m, if i = j then h * (ξ j : ℂ) else 0)
          s := by
      let hsum'' :=
        (HasDerivAt.sum (u := Finset.univ)
          (A := fun i : Fin m => fun t : ℝ =>
            Function.update z j (z j + (t : ℂ) * h) i * (ξ i : ℂ))
          (A' := fun i : Fin m => if i = j then h * (ξ j : ℂ) else 0)
          (x := s)
          (fun i _ => by
            by_cases hij : i = j
            · subst hij
              simpa [Function.update_self] using hcoord.mul_const ((ξ i : ℂ))
            · simpa [Function.update_of_ne hij, hij] using
                (hasDerivAt_const s (z i * (ξ i : ℂ)))))
      convert hsum'' using 1
      · ext t
        simp
    simpa using hsum'
  have hexp :
      HasDerivAt
        (fun t : ℝ =>
          cexp (I * ∑ i, Function.update z j (z j + (t : ℂ) * h) i * (ξ i : ℂ)))
        (cexp (I * ∑ i, Function.update z j (z j + (s : ℂ) * h) i * (ξ i : ℂ)) *
          (I * (h * (ξ j : ℂ))))
        s := by
    simpa [mul_assoc] using (hsum.const_mul I).cexp
  have hmul := hexp.const_mul ((χ.val ξ : ℂ))
  simpa [psiZRaw, mul_assoc, mul_left_comm, mul_comm] using hmul

private lemma hasDerivAt_psiZRaw_update_coordDeriv_apply
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (χ : FixedConeCutoff (DualConeFlat C))
    (z : Fin m → ℂ) (j : Fin m) (h : ℂ) (ξ : Fin m → ℝ) (s : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        ((I * h * (ξ j : ℂ)) : ℂ) *
          psiZRaw χ 1 (Function.update z j (z j + (t : ℂ) * h)) ξ)
      ((((I * h * (ξ j : ℂ)) : ℂ) ^ 2) *
        psiZRaw χ 1 (Function.update z j (z j + (s : ℂ) * h)) ξ)
      s := by
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_psiZRaw_update_apply χ z j h ξ s).const_mul ((I * h * (ξ j : ℂ)) : ℂ)

private lemma hasDerivAt_multiDimPsiZ_update_apply
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (j : Fin m) (h : ℂ) (ξ : Fin m → ℝ)
    (hzCurve : ∀ t : ℝ, Function.update z j (z j + (t : ℂ) * h) ∈ SCV.TubeDomain C)
    (s : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
          (Function.update z j (z j + (t : ℂ) * h))
          (hzCurve t) ξ)
      (((I * h * (ξ j : ℂ)) : ℂ) *
        multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
          (Function.update z j (z j + (s : ℂ) * h)) (hzCurve s) ξ)
      s := by
  let χ : FixedConeCutoff (DualConeFlat C) :=
    (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  simpa [multiDimPsiZ, multiDimPsiZR, χ] using
    hasDerivAt_psiZRaw_update_apply χ z j h ξ s

private lemma hasDerivAt_multiDimPsiZ_update_coordDeriv_apply
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (j : Fin m) (h : ℂ) (ξ : Fin m → ℝ)
    (hzCurve : ∀ t : ℝ, Function.update z j (z j + (t : ℂ) * h) ∈ SCV.TubeDomain C)
    (s : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        ((I * h * (ξ j : ℂ)) : ℂ) *
          multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
            (Function.update z j (z j + (t : ℂ) * h))
            (hzCurve t) ξ)
      ((((I * h * (ξ j : ℂ)) : ℂ) ^ 2) *
        multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
          (Function.update z j (z j + (s : ℂ) * h)) (hzCurve s) ξ)
      s := by
  let χ : FixedConeCutoff (DualConeFlat C) :=
    (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  simpa [multiDimPsiZ, multiDimPsiZR, χ] using
    hasDerivAt_psiZRaw_update_coordDeriv_apply χ z j h ξ s

private lemma multiDimPsiZ_update_sub_apply
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) (h : ℂ)
    (hz' : Function.update z j (z j + h) ∈ SCV.TubeDomain C)
    (ξ : Fin m → ℝ) :
    multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
        (Function.update z j (z j + h)) hz' ξ -
      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ =
      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ *
        (cexp (I * h * (ξ j : ℂ)) - 1) := by
  rw [multiDimPsiZ_update_apply_eq_mul_cexp hC_open hC_conv hC_cone hC_salient z hz j h hz' ξ]
  ring

private lemma norm_cexp_sub_one_le_mul_exp (h : ℂ) (x : ℝ) :
    ‖cexp (I * h * x) - 1‖ ≤ ‖h‖ * |x| * Real.exp (‖h‖ * |x|) := by
  have hmain := Complex.norm_exp_sub_sum_le_norm_mul_exp (I * h * x) 1
  have hnorm : ‖I * h * x‖ = ‖h‖ * |x| := by
    simp [mul_assoc, Real.norm_eq_abs]
  calc
    ‖cexp (I * h * x) - 1‖ ≤ ‖I * h * x‖ * Real.exp ‖I * h * x‖ := by
      simpa using hmain
    _ = ‖h‖ * |x| * Real.exp (‖h‖ * |x|) := by rw [hnorm]

private lemma norm_cexp_sub_one_sub_linear_div_le (h : ℂ) (x : ℝ) :
    ‖(cexp (I * h * x) - 1 - I * h * x) / h‖ ≤
      ‖h‖ * |x| ^ 2 * Real.exp (‖h‖ * |x|) := by
  by_cases hh : h = 0
  · subst hh
    simp
  · have hmain := Complex.norm_exp_sub_sum_le_norm_mul_exp (I * h * x) 2
    have hnorm : ‖I * h * x‖ = ‖h‖ * |x| := by
      simp [mul_assoc, Real.norm_eq_abs]
    have hh0 : ‖h‖ ≠ 0 := by simpa [norm_eq_zero] using hh
    have hsum :
        ∑ m ∈ Finset.range 2, (I * h * x) ^ m / (m.factorial : ℂ) = I * h * x + 1 := by
      simp [Finset.sum_range_succ, add_comm]
    have hmain' :
        ‖cexp (I * h * x) - 1 - I * h * x‖ ≤
          ‖I * h * x‖ ^ 2 * Real.exp ‖I * h * x‖ := by
      simpa [hsum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain
    calc
      ‖(cexp (I * h * x) - 1 - I * h * x) / h‖
          = ‖cexp (I * h * x) - 1 - I * h * x‖ / ‖h‖ := by rw [norm_div]
      _ ≤ (‖I * h * x‖ ^ 2 * Real.exp ‖I * h * x‖) / ‖h‖ := by
            gcongr
      _ = ‖h‖ * |x| ^ 2 * Real.exp (‖h‖ * |x|) := by
            rw [hnorm]
            field_simp [hh0]

private lemma norm_multiDimPsiZ_update_sub_le
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) (h : ℂ)
    (hz' : Function.update z j (z j + h) ∈ SCV.TubeDomain C)
    (ξ : Fin m → ℝ) :
    ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
        (Function.update z j (z j + h)) hz' ξ -
      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ‖ ≤
      ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ‖ *
        (‖h‖ * |ξ j| * Real.exp (‖h‖ * |ξ j|)) := by
  rw [multiDimPsiZ_update_sub_apply hC_open hC_conv hC_cone hC_salient z hz j h hz' ξ]
  calc
    ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ *
        (cexp (I * h * (ξ j : ℂ)) - 1)‖
        = ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ‖ *
            ‖cexp (I * h * (ξ j : ℂ)) - 1‖ := by rw [norm_mul]
    _ ≤ ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ‖ *
          (‖h‖ * |ξ j| * Real.exp (‖h‖ * |ξ j|)) := by
            gcongr
            exact norm_cexp_sub_one_le_mul_exp h (ξ j)

private lemma norm_multiDimPsiZ_differenceQuotient_remainder_le
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) (h : ℂ)
    (hh : h ≠ 0)
    (hz' : Function.update z j (z j + h) ∈ SCV.TubeDomain C)
    (ξ : Fin m → ℝ) :
    ‖h⁻¹ *
        (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
            (Function.update z j (z j + h)) hz' ξ -
          multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ) -
      multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j ξ‖ ≤
      ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ‖ *
        (‖h‖ * |ξ j| ^ 2 * Real.exp (‖h‖ * |ξ j|)) := by
  have hrew :=
    multiDimPsiZ_update_sub_sub_coordDeriv_apply
      hC_open hC_conv hC_cone hC_salient z hz j h hz' ξ
  have hlin :
      h⁻¹ *
          (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
              (Function.update z j (z j + h)) hz' ξ -
            multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ) -
        multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j ξ =
      h⁻¹ *
        (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
            (Function.update z j (z j + h)) hz' ξ -
          multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ -
          h * multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j ξ) := by
    field_simp [hh]
  calc
    ‖h⁻¹ *
        (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
            (Function.update z j (z j + h)) hz' ξ -
          multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ) -
      multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j ξ‖
        = ‖h⁻¹ *
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ *
              (cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)))‖ := by
            rw [hlin, hrew]
    _ = ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ *
          ((cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)) / h)‖ := by
            field_simp [hh]
    _ = ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ‖ *
          ‖(cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)) / h‖ := by
            rw [norm_mul]
    _ ≤ ‖multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ‖ *
          (‖h‖ * |ξ j| ^ 2 * Real.exp (‖h‖ * |ξ j|)) := by
            gcongr
            exact norm_cexp_sub_one_sub_linear_div_le h (ξ j)

private lemma norm_iteratedFDeriv_cexp_sub_one_bound
    {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hL_one : ‖L‖ ≤ 1) (hL_c : ‖L‖ ≤ c)
    (i : ℕ) (ξ : Fin m → ℝ) :
    ‖iteratedFDeriv ℝ i (fun x => cexp (L x) - 1) ξ‖ ≤
      ‖L‖ * (i.factorial : ℝ) * (1 + ‖ξ‖) ^ 2 * Real.exp (c * ‖ξ‖) := by
  rcases i with _ | i
  · have hmain := Complex.norm_exp_sub_sum_le_norm_mul_exp (L ξ) 1
    calc
      ‖iteratedFDeriv ℝ 0 (fun x => cexp (L x) - 1) ξ‖
          = ‖cexp (L ξ) - 1‖ := by simp
      _ ≤ ‖L ξ‖ * Real.exp ‖L ξ‖ := by simpa using hmain
      _ ≤ (‖L‖ * ‖ξ‖) * Real.exp (c * ‖ξ‖) := by
            gcongr
            · exact ContinuousLinearMap.le_opNorm L ξ
            · exact le_trans (ContinuousLinearMap.le_opNorm L ξ) (by gcongr)
      _ ≤ ‖L‖ * (1 + ‖ξ‖) ^ 2 * Real.exp (c * ‖ξ‖) := by
            have hpow : ‖ξ‖ ≤ (1 + ‖ξ‖) ^ 2 := by
              nlinarith [norm_nonneg ξ]
            gcongr
      _ = ‖L‖ * ((Nat.factorial 0 : ℕ) : ℝ) * (1 + ‖ξ‖) ^ 2 * Real.exp (c * ‖ξ‖) := by
            simp
  · have hsub :
        iteratedFDeriv ℝ (i + 1) (fun x => cexp (L x) - 1) ξ =
          iteratedFDeriv ℝ (i + 1) (fun x => cexp (L x)) ξ := by
      have hsub' := iteratedFDeriv_sub_apply
        (f := fun x => cexp (L x))
        (g := fun _ => (1 : ℂ))
        ((Complex.contDiff_exp.comp L.contDiff).contDiffAt)
        (contDiff_const.contDiffAt)
        (x := ξ) (i := i + 1)
      calc
        iteratedFDeriv ℝ (i + 1) (fun x => cexp (L x) - 1) ξ
            = iteratedFDeriv ℝ (i + 1) ((fun x => cexp (L x)) - fun _ => (1 : ℂ)) ξ := by
                rfl
        _ = iteratedFDeriv ℝ (i + 1) (fun x => cexp (L x)) ξ -
              iteratedFDeriv ℝ (i + 1) (fun _ => (1 : ℂ)) ξ := hsub'
        _ = iteratedFDeriv ℝ (i + 1) (fun x => cexp (L x)) ξ := by
              simp [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega : i + 1 ≠ 0) (1 : ℂ)]
    rw [hsub]
    calc
      ‖iteratedFDeriv ℝ (i + 1) (fun x => cexp (L x)) ξ‖
          ≤ ((i + 1).factorial : ℝ) * ‖cexp (L ξ)‖ * ‖L‖ ^ (i + 1) :=
            norm_iteratedFDeriv_cexp_comp_clm_le L ξ (i + 1)
      _ = ((i + 1).factorial : ℝ) * Real.exp ((L ξ).re) * ‖L‖ ^ (i + 1) := by
            rw [Complex.norm_exp]
      _ ≤ ((i + 1).factorial : ℝ) * Real.exp (c * ‖ξ‖) * ‖L‖ ^ (i + 1) := by
            gcongr
            exact le_trans (Complex.re_le_norm _) (le_trans (ContinuousLinearMap.le_opNorm L ξ) (by gcongr))
      _ = ((i + 1).factorial : ℝ) * Real.exp (c * ‖ξ‖) * (‖L‖ ^ i * ‖L‖) := by
            rw [pow_succ]
      _ ≤ ((i + 1).factorial : ℝ) * Real.exp (c * ‖ξ‖) * (1 * ‖L‖) := by
            have hpow : ‖L‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hL_one
            gcongr
      _ = ‖L‖ * ((i + 1).factorial : ℝ) * Real.exp (c * ‖ξ‖) := by ring
      _ ≤ ‖L‖ * ((i + 1).factorial : ℝ) * (1 + ‖ξ‖) ^ 2 * Real.exp (c * ‖ξ‖) := by
            have hpow : (1 : ℝ) ≤ (1 + ‖ξ‖) ^ 2 := by
              nlinarith [norm_nonneg ξ]
            have hnonneg :
                0 ≤ ‖L‖ * ((i + 1).factorial : ℝ) * Real.exp (c * ‖ξ‖) := by
              positivity
            nlinarith

private def expTaylorLinearRemainderQuotPW (h : ℂ) : ℝ → ℂ :=
  fun ξ => (Complex.exp (I * h * ξ) - 1 - I * h * ξ) / h

private theorem iteratedDeriv_expTaylorLinearRemainderQuotPW_zero
    (h : ℂ) (ξ : ℝ) :
    iteratedDeriv 0 (expTaylorLinearRemainderQuotPW h) ξ =
      (Complex.exp (I * h * ξ) - 1 - I * h * ξ) / h := by
  simp [expTaylorLinearRemainderQuotPW]

private theorem iteratedDeriv_expTaylorLinearRemainderQuotPW_one
    (h : ℂ) (ξ : ℝ) :
    iteratedDeriv 1 (expTaylorLinearRemainderQuotPW h) ξ =
      I * (Complex.exp (I * h * ξ) - 1) := by
  let c : ℂ := I * h
  rw [iteratedDeriv_succ]
  simp [iteratedDeriv_zero]
  unfold expTaylorLinearRemainderQuotPW
  have hlin : HasDerivAt (fun ξ : ℝ => c * ξ) c ξ := by
    refine (?_ : HasDerivAt (fun y : ℂ => c * y) c (ξ : ℂ)).comp_ofReal
    simpa using (hasDerivAt_const_mul c : HasDerivAt (fun y : ℂ => c * y) c (ξ : ℂ))
  have hExp : HasDerivAt (fun ξ : ℝ => Complex.exp (c * ξ))
      (c * Complex.exp (c * ξ)) ξ := by
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using
      (Complex.hasDerivAt_exp (c * (ξ : ℂ))).comp ξ hlin
  have hfull : HasDerivAt (fun ξ : ℝ => (Complex.exp (c * ξ) - 1 - c * ξ) / h)
      ((c * Complex.exp (c * ξ) - c) / h) ξ := by
    exact ((hExp.sub_const 1).sub hlin).div_const h
  rw [hfull.deriv]
  by_cases hh : h = 0
  · subst hh
    simp [c]
  · field_simp [hh]
    simp [c, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]

private theorem iteratedDeriv_expTaylorLinearRemainderQuotPW_succ_succ
    (m : ℕ) (h : ℂ) (ξ : ℝ) :
    iteratedDeriv (m + 2) (expTaylorLinearRemainderQuotPW h) ξ =
      ((I * h) ^ (m + 2) / h) * Complex.exp (I * h * ξ) := by
  let c : ℂ := I * h
  have hderiv1 :
      deriv (expTaylorLinearRemainderQuotPW h) =
        fun ξ : ℝ => I * (Complex.exp (c * ξ) - 1) := by
    funext x
    simpa [c] using iteratedDeriv_expTaylorLinearRemainderQuotPW_one h x
  have hderiv2 :
      deriv (fun ξ : ℝ => I * (Complex.exp (c * ξ) - 1)) =
        fun ξ : ℝ => (I * c) * Complex.exp (c * ξ) := by
    funext x
    have hlin : HasDerivAt (fun ξ : ℝ => c * ξ) c x := by
      refine (?_ : HasDerivAt (fun y : ℂ => c * y) c (x : ℂ)).comp_ofReal
      simpa using (hasDerivAt_const_mul c : HasDerivAt (fun y : ℂ => c * y) c (x : ℂ))
    have : HasDerivAt (fun ξ : ℝ => Complex.exp (c * ξ) - 1)
        (c * Complex.exp (c * x)) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((Complex.hasDerivAt_exp (c * (x : ℂ))).comp x hlin).sub_const 1
    rw [(this.const_mul I).deriv]
    simp [mul_assoc]
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  rw [hderiv1, hderiv2]
  calc
    iteratedDeriv m (fun ξ : ℝ => (I * c) * Complex.exp (c * ξ)) ξ
        = (I * c) * iteratedDeriv m (fun ξ : ℝ => Complex.exp (c * ξ)) ξ := by
            have := iteratedDeriv_const_mul_field (𝕜 := ℝ) (n := m) (I * c)
              (fun ξ : ℝ => Complex.exp (c * ξ)) (x := ξ)
            exact this
    _ = (I * c) * (c ^ m * Complex.exp (c * ξ)) := by
          rw [SCV.iteratedDeriv_cexp_const_mul_real]
    _ = ((I * h) ^ (m + 2) / h) * Complex.exp (I * h * ξ) := by
          by_cases hh : h = 0
          · subst hh
            simp [c]
          · have hscalar : (I * c) * c ^ m = ((I * h) ^ (m + 2)) / h := by
                field_simp [c, hh]
                ring
            calc
              (I * c) * (c ^ m * Complex.exp (c * ξ))
                  = ((I * c) * c ^ m) * Complex.exp (c * ξ) := by ring
              _ = (((I * h) ^ (m + 2)) / h) * Complex.exp (c * ξ) := by rw [hscalar]
              _ = (((I * h) ^ (m + 2)) / h) * Complex.exp (I * h * ξ) := by simp [c]

private theorem expTaylorLinearRemainderQuotPW_contDiff (h : ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (expTaylorLinearRemainderQuotPW h) := by
  let c : ℂ := I * h
  have hexp : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun ξ : ℝ => Complex.exp ((ξ : ℂ) * c)) := by
    simpa using
      (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const))
  have hlin : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun ξ : ℝ => (ξ : ℂ) * c) := by
    simpa using (Complex.ofRealCLM.contDiff.mul contDiff_const)
  unfold expTaylorLinearRemainderQuotPW
  simpa [c, div_eq_mul_inv, sub_eq_add_neg, add_assoc, mul_assoc, mul_left_comm, mul_comm] using
    (contDiff_const.mul ((hexp.sub contDiff_const).sub hlin))

private theorem norm_iteratedDeriv_expTaylorLinearRemainderQuotPW_le
    (i : ℕ) (h : ℂ) (hh1 : ‖h‖ ≤ 1) (ξ : ℝ) :
    ‖iteratedDeriv i (expTaylorLinearRemainderQuotPW h) ξ‖ ≤
      ‖h‖ * (i.factorial : ℝ) * (1 + |ξ|) ^ 2 * Real.exp (‖h‖ * |ξ|) := by
  obtain rfl | rfl | m := i
  · rw [iteratedDeriv_expTaylorLinearRemainderQuotPW_zero]
    by_cases hh : h = 0
    · subst hh
      simp
    · have hmain := Complex.norm_exp_sub_sum_le_norm_mul_exp (I * h * ξ) 2
      have hnorm : ‖I * h * ξ‖ = ‖h‖ * |ξ| := by
        simp [mul_assoc, Real.norm_eq_abs]
      have hh0 : ‖h‖ ≠ 0 := by simpa [norm_eq_zero] using hh
      have hsum :
          ∑ m ∈ Finset.range 2, (I * h * ξ) ^ m / (m.factorial : ℂ) = I * h * ξ + 1 := by
        simp [Finset.sum_range_succ, add_comm]
      have hmain' :
          ‖Complex.exp (I * h * ξ) - 1 - I * h * ξ‖ ≤
            ‖I * h * ξ‖ ^ 2 * Real.exp ‖I * h * ξ‖ := by
        simpa [hsum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain
      calc
        ‖(Complex.exp (I * h * ξ) - 1 - I * h * ξ) / h‖
            = ‖Complex.exp (I * h * ξ) - 1 - I * h * ξ‖ / ‖h‖ := by rw [norm_div]
        _ ≤ (‖I * h * ξ‖ ^ 2 * Real.exp ‖I * h * ξ‖) / ‖h‖ := by gcongr
        _ = ‖h‖ * |ξ| ^ 2 * Real.exp (‖h‖ * |ξ|) := by
              rw [hnorm]
              field_simp [hh0]
        _ ≤ ‖h‖ * (1 + |ξ|) ^ 2 * Real.exp (‖h‖ * |ξ|) := by
              have habs : |ξ| ^ 2 ≤ (1 + |ξ|) ^ 2 := by nlinarith [abs_nonneg ξ]
              gcongr
        _ = ‖h‖ * ((Nat.factorial 0 : ℕ) : ℝ) * (1 + |ξ|) ^ 2 * Real.exp (‖h‖ * |ξ|) := by
              simp
  · calc
      ‖iteratedDeriv 1 (expTaylorLinearRemainderQuotPW h) ξ‖
          = ‖I * (Complex.exp (I * h * ξ) - 1)‖ := by
              rw [iteratedDeriv_expTaylorLinearRemainderQuotPW_one]
      _ = ‖Complex.exp (I * h * ξ) - 1‖ := by simp
      _ ≤ ‖I * h * ξ‖ * Real.exp ‖I * h * ξ‖ := by
            simpa using (Complex.norm_exp_sub_sum_le_norm_mul_exp (I * h * ξ) 1)
      _ = ‖h‖ * |ξ| * Real.exp (‖h‖ * |ξ|) := by
            simp [mul_assoc, Real.norm_eq_abs]
      _ ≤ ‖h‖ * (1 + |ξ|) ^ 2 * Real.exp (‖h‖ * |ξ|) := by
            have habs : |ξ| ≤ (1 + |ξ|) ^ 2 := by nlinarith [abs_nonneg ξ]
            gcongr
      _ = ‖h‖ * ((Nat.factorial 1 : ℕ) : ℝ) * (1 + |ξ|) ^ 2 * Real.exp (‖h‖ * |ξ|) := by
            simp
  · calc
      ‖iteratedDeriv (m + 2) (expTaylorLinearRemainderQuotPW h) ξ‖
          = ‖((I * h) ^ (m + 2) / h) * Complex.exp (I * h * ξ)‖ := by
              rw [iteratedDeriv_expTaylorLinearRemainderQuotPW_succ_succ]
      _ ≤ ‖h‖ * Real.exp (‖h‖ * |ξ|) := by
            by_cases hh : h = 0
            · subst hh
              simp
            · have hh0 : ‖h‖ ≠ 0 := by simpa [norm_eq_zero] using hh
              have hcoeff : ‖((I * h) ^ (m + 2) / h)‖ ≤ ‖h‖ := by
                have hpow_le : ‖h‖ ^ (m + 1) ≤ ‖h‖ := by
                  cases m with
                  | zero => simp
                  | succ m =>
                      calc
                        ‖h‖ ^ (Nat.succ (Nat.succ m)) = ‖h‖ ^ (Nat.succ m) * ‖h‖ := by
                          rw [pow_succ]
                        _ ≤ 1 * ‖h‖ := by
                          gcongr
                          exact pow_le_one₀ (norm_nonneg _) hh1
                        _ = ‖h‖ := by ring
                calc
                  ‖((I * h) ^ (m + 2) / h)‖ = ‖I * h‖ ^ (m + 2) / ‖h‖ := by
                    rw [norm_div, norm_pow]
                  _ = ‖h‖ ^ (m + 2) / ‖h‖ := by simp [norm_mul]
                  _ = ‖h‖ ^ (m + 1) := by
                    field_simp [hh0]
                    ring
                  _ ≤ ‖h‖ := hpow_le
              calc
                ‖((I * h) ^ (m + 2) / h) * Complex.exp (I * h * ξ)‖
                    = ‖((I * h) ^ (m + 2) / h)‖ * Real.exp (Complex.re (I * h * ξ)) := by
                        rw [norm_mul, Complex.norm_exp]
                _ ≤ ‖((I * h) ^ (m + 2) / h)‖ * Real.exp ‖I * h * ξ‖ := by
                      apply mul_le_mul_of_nonneg_left
                      · exact Real.exp_le_exp.mpr (Complex.re_le_norm _)
                      · exact norm_nonneg _
                _ ≤ ‖h‖ * Real.exp ‖I * h * ξ‖ := by
                      apply mul_le_mul_of_nonneg_right hcoeff
                      positivity
                _ = ‖h‖ * Real.exp (‖h‖ * |ξ|) := by
                      simp [mul_assoc, Real.norm_eq_abs]
      _ ≤ ‖h‖ * ((m + 2).factorial : ℝ) * (1 + |ξ|) ^ 2 * Real.exp (‖h‖ * |ξ|) := by
            have hfac : (1 : ℝ) ≤ ((m + 2).factorial : ℝ) := by
              exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (m + 2))
            have hpow : (1 : ℝ) ≤ (1 + |ξ|) ^ 2 := by nlinarith [abs_nonneg ξ]
            have hexp_nonneg : 0 ≤ Real.exp (‖h‖ * |ξ|) := by positivity
            calc
              ‖h‖ * Real.exp (‖h‖ * |ξ|)
                  ≤ (‖h‖ * ((m + 2).factorial : ℝ)) * Real.exp (‖h‖ * |ξ|) := by
                      apply mul_le_mul_of_nonneg_right _ hexp_nonneg
                      calc
                        ‖h‖ = ‖h‖ * 1 := by ring
                        _ ≤ ‖h‖ * ((m + 2).factorial : ℝ) := by
                              gcongr
              _ ≤ (‖h‖ * ((m + 2).factorial : ℝ) * (1 + |ξ|) ^ 2) * Real.exp (‖h‖ * |ξ|) := by
                      apply mul_le_mul_of_nonneg_right _ hexp_nonneg
                      calc
                        ‖h‖ * ((m + 2).factorial : ℝ) =
                            (‖h‖ * ((m + 2).factorial : ℝ)) * 1 := by ring
                        _ ≤ (‖h‖ * ((m + 2).factorial : ℝ)) * (1 + |ξ|) ^ 2 := by
                              gcongr
              _ = ‖h‖ * ((m + 2).factorial : ℝ) * (1 + |ξ|) ^ 2 * Real.exp (‖h‖ * |ξ|) := by
                      ring

private lemma norm_iteratedFDeriv_differenceQuotient_remainder_bound
    {m : ℕ} (h : ℂ) (j : Fin m) {c : ℝ}
    (hh1 : ‖h‖ ≤ 1) (hhc : ‖h‖ ≤ c)
    (i : ℕ) (ξ : Fin m → ℝ) :
    ‖iteratedFDeriv ℝ i
        (fun x : Fin m → ℝ =>
          (cexp (I * h * (x j : ℂ)) - 1 - I * h * (x j : ℂ)) / h) ξ‖ ≤
      ‖h‖ * (i.factorial : ℝ) * (1 + ‖ξ‖) ^ 2 * Real.exp (c * ‖ξ‖) := by
  let p : (Fin m → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) j
  let r : ℝ → ℂ := expTaylorLinearRemainderQuotPW h
  have hr_smooth : ContDiff ℝ ∞ r := expTaylorLinearRemainderQuotPW_contDiff h
  have hcomp : (fun x : Fin m → ℝ => (cexp (I * h * (x j : ℂ)) - 1 - I * h * (x j : ℂ)) / h) = r ∘ p := by
    funext x
    simp [r, p, expTaylorLinearRemainderQuotPW]
  rw [hcomp, p.iteratedFDeriv_comp_right hr_smooth ξ (by exact_mod_cast le_top)]
  have hp : ‖p‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro x
    rw [one_mul]
    simp only [p, ContinuousLinearMap.proj_apply, Pi.norm_def]
    exact_mod_cast Finset.le_sup (f := fun k => ‖x k‖₊) (Finset.mem_univ j)
  calc
    ‖(iteratedFDeriv ℝ i r (p ξ)).compContinuousLinearMap fun _ => p‖
        ≤ ‖iteratedFDeriv ℝ i r (p ξ)‖ * ∏ _ : Fin i, ‖p‖ := by
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ i r (ξ j)‖ * ‖p‖ ^ i := by
          simp [p, Finset.prod_const]
    _ ≤ ‖iteratedFDeriv ℝ i r (ξ j)‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hp
    _ = ‖iteratedFDeriv ℝ i r (ξ j)‖ := by simp
    _ = ‖iteratedDeriv i r (ξ j)‖ := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ ≤ ‖h‖ * (i.factorial : ℝ) * (1 + |ξ j|) ^ 2 * Real.exp (‖h‖ * |ξ j|) := by
          exact norm_iteratedDeriv_expTaylorLinearRemainderQuotPW_le i h hh1 (ξ j)
    _ ≤ ‖h‖ * (i.factorial : ℝ) * (1 + ‖ξ‖) ^ 2 * Real.exp (c * ‖ξ‖) := by
          have hcoord : |ξ j| ≤ ‖ξ‖ := by
            calc
              |ξ j| = ‖p ξ‖ := by simp [p]
              _ ≤ ‖p‖ * ‖ξ‖ := ContinuousLinearMap.le_opNorm p ξ
              _ ≤ 1 * ‖ξ‖ := by gcongr
              _ = ‖ξ‖ := by ring
          have hc' : 0 ≤ c := le_trans (norm_nonneg h) hhc
          gcongr

/-- **Lipschitz-type seminorm bound for multiDimPsiZ difference.**

    For z near z₀ in the tube, the Schwartz (k,n)-seminorm of ψ_z - ψ_{z₀}
    is bounded by D * ‖z - z₀‖, with D depending on z₀, k, n, the cone.

    **Proof sketch** (Hörmander, "Analysis of Linear PDOs I", §7.4):
    The difference at ξ is:
      (ψ_z - ψ_{z₀})(ξ) = χ(ξ)(exp(iz·ξ) - exp(iz₀·ξ))

    By mean value theorem applied to t ↦ exp(i(z₀ + t(z-z₀))·ξ):
      |exp(iz·ξ) - exp(iz₀·ξ)| ≤ ‖z - z₀‖ · ‖ξ‖ · sup_t |exp(i(z₀+t(z-z₀))·ξ)|

    For z near z₀ (within δ₀ = δ_tube/2), the path stays in the tube, so
    the exponential has the same decay: exp(-c·‖ξ‖ + A·R) for some uniform c.

    The ‖ξ‖ factor from MVT is absorbed by the exponential decay (losing one
    power of k in the polynomial weight), giving:
      ‖ξ‖^k · |D^n[(ψ_z - ψ_{z₀})](ξ)| ≤ D' · ‖z - z₀‖

    Then seminorm_le_bound gives the result.

    See Hörmander, "Analysis of Linear PDOs I", §7.4. -/
theorem multiDimPsiZ_seminorm_difference_bound
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (k n : ℕ)
    (z₀ : Fin m → ℂ) (hz₀ : z₀ ∈ SCV.TubeDomain C) :
    ∃ (D : ℝ) (δ₀ : ℝ), D > 0 ∧ δ₀ > 0 ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
        ‖z - z₀‖ < δ₀ →
          SchwartzMap.seminorm ℝ k n
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz -
             multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z₀ hz₀) ≤ D * ‖z - z₀‖ := by
  let χ : FixedConeCutoff (DualConeFlat C) :=
    (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  let y₀ : Fin m → ℝ := fun i => (z₀ i).im
  have hy₀ : y₀ ∈ C := hz₀
  have hC_star_ne : (DualConeFlat C).Nonempty := ⟨0, zero_mem_dualConeFlat C⟩
  have hC_star_closed : IsClosed (DualConeFlat C) := dualConeFlat_closed C
  obtain ⟨c₀, hc₀_pos, hc₀⟩ :=
    dualConeFlat_coercivity hC_open hC_cone hy₀ hC_star_ne hC_star_closed
  let K : ℝ := (Fintype.card (Fin m) : ℝ)
  let K2 : ℝ := ((Fintype.card (Fin m) : ℝ) ^ 2)
  let δ₀ : ℝ := min (1 / (K + 1)) (c₀ / (2 * (K + 1)))
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    refine lt_min ?_ ?_ <;> positivity
  let A₀ : ℝ := c₀ + K2 * ‖y₀‖
  let L₀ : (Fin m → ℝ) →L[ℝ] ℂ := multiDimPsiExpCLM z₀
  obtain ⟨Bexp, hBexp_pos, hBexp⟩ :=
    schwartz_seminorm_cutoff_exp_mul_G_bound_affine_uniform
      χ.val χ.smooth χ.deriv_bound A₀ c₀ hc₀_pos k n
  let L₀bd : ℝ := K * ‖z₀‖
  let D : ℝ := Bexp * (K + 1) * (1 + L₀bd) ^ n
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, δ₀, hD_pos, hδ₀_pos, ?_⟩
  intro z hz hzdist
  let Ldiff : (Fin m → ℝ) →L[ℝ] ℂ := multiDimPsiExpCLM (z - z₀)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hLdiff_one : ‖Ldiff‖ ≤ 1 := by
    calc
      ‖Ldiff‖ ≤ K * ‖z - z₀‖ := multiDimPsiExpCLM_norm_le (z - z₀)
      _ ≤ K * δ₀ := by
            gcongr
      _ ≤ K * (1 / (K + 1)) := by
            gcongr
            exact min_le_left _ _
      _ = K / (K + 1) := by
            field_simp
      _ ≤ 1 := by
            have hpos : 0 < K + 1 := by positivity
            exact (div_le_one hpos).2 (by linarith)
  have hLdiff_c : ‖Ldiff‖ ≤ c₀ / 2 := by
    calc
      ‖Ldiff‖ ≤ K * ‖z - z₀‖ := multiDimPsiExpCLM_norm_le (z - z₀)
      _ ≤ K * δ₀ := by
            gcongr
      _ ≤ K * (c₀ / (2 * (K + 1))) := by
            gcongr
            exact min_le_right _ _
      _ = (K * c₀) / (2 * (K + 1)) := by
            ring
      _ ≤ (c₀ * (K + 1)) / (2 * (K + 1)) := by
            apply div_le_div_of_nonneg_right
            · nlinarith [hK_nonneg, hc₀_pos]
            · positivity
      _ = c₀ / 2 := by
            field_simp [show (K + 1) ≠ 0 by linarith]
  have hexp_decay :
      ∀ ξ : Fin m → ℝ, χ.val ξ ≠ 0 → (L₀ ξ).re ≤ A₀ - c₀ * ‖ξ‖ := by
    intro ξ hχξ
    have hdistχ : Metric.infDist ξ (DualConeFlat C) ≤ 1 := by
      by_contra h
      exact hχξ (χ.support_bound ξ (by linarith))
    have hExpBound :
        ‖cexp (L₀ ξ)‖ ≤ Real.exp A₀ * Real.exp (-(c₀ * ‖ξ‖)) := by
      calc
        ‖cexp (L₀ ξ)‖ = ‖cexp (I * ∑ i, z₀ i * (ξ i : ℂ))‖ := by
          rw [multiDimPsiExpCLM_apply]
        _ ≤ Real.exp (((c₀ + K2 * ‖y₀‖) * 1)) * Real.exp (-(c₀ * ‖ξ‖)) := by
          simpa [K2, y₀] using
            cexp_bound_on_support hC_open hC_cone hz₀ hc₀_pos hc₀ zero_lt_one ξ hdistχ
        _ = Real.exp A₀ * Real.exp (-(c₀ * ‖ξ‖)) := by
          simp [A₀]
    have hnormexp : ‖cexp (L₀ ξ)‖ = Real.exp ((L₀ ξ).re) := by
      rw [Complex.norm_exp]
    have hExp' : Real.exp ((L₀ ξ).re) ≤ Real.exp (A₀ - c₀ * ‖ξ‖) := by
      rw [← hnormexp]
      simpa [sub_eq_add_neg, Real.exp_add] using hExpBound
    exact Real.exp_le_exp.mp hExp'
  have hG_bound :
      ∀ i ≤ n, ∀ ξ : Fin m → ℝ,
        ‖iteratedFDeriv ℝ i (fun x => cexp (Ldiff x) - 1) ξ‖ ≤
          ‖Ldiff‖ * (i.factorial : ℝ) * (1 + ‖ξ‖) ^ 2 * Real.exp ((c₀ / 2) * ‖ξ‖) := by
    intro i hi ξ
    exact norm_iteratedFDeriv_cexp_sub_one_bound Ldiff (by positivity) hLdiff_one hLdiff_c i ξ
  have hL₀ : ‖L₀‖ ≤ L₀bd := by
    simpa [L₀, L₀bd, K] using multiDimPsiExpCLM_norm_le z₀
  have hpoint :
      ∀ ξ : Fin m → ℝ,
        ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n
              (⇑(multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz -
                  multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z₀ hz₀)) ξ‖ ≤
            D * ‖z - z₀‖ := by
    intro ξ
    have hraw :=
      hBexp L₀ hexp_decay
        (fun x => cexp (Ldiff x) - 1)
        ((Complex.contDiff_exp.comp Ldiff.contDiff).sub contDiff_const)
        ‖Ldiff‖ (norm_nonneg _) hG_bound ξ
    have hfun :
        ⇑(multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz -
            multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z₀ hz₀) =
          (fun ξ : Fin m → ℝ =>
            (χ.val ξ : ℂ) * (cexp (L₀ ξ) * (cexp (Ldiff ξ) - 1))) := by
      funext ξ
      change psiZRaw χ 1 z ξ - psiZRaw χ 1 z₀ ξ =
        (χ.val ξ : ℂ) * (cexp (L₀ ξ) * (cexp (Ldiff ξ) - 1))
      simp [psiZRaw, L₀, Ldiff]
      rw [multiDimPsiExpCLM_apply z₀ ξ, multiDimPsiExpCLM_apply (z - z₀) ξ]
      have hsum :
          ∑ i, z i * (ξ i : ℂ) =
            ∑ i, z₀ i * (ξ i : ℂ) + ∑ i, (z - z₀) i * (ξ i : ℂ) := by
        rw [← Finset.sum_add_distrib]
        congr with i
        simp [Pi.sub_apply]
        ring_nf
      have hadd :
          I * ∑ i, z i * (ξ i : ℂ) =
            I * ∑ i, z₀ i * (ξ i : ℂ) + I * ∑ i, (z - z₀) i * (ξ i : ℂ) := by
        rw [hsum]
        ring
      rw [hadd, Complex.exp_add]
      ring
    calc
      ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n
              (⇑(multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz -
                  multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z₀ hz₀)) ξ‖
          = ‖ξ‖ ^ k *
              ‖iteratedFDeriv ℝ n
                  (fun ξ : Fin m → ℝ =>
                    (χ.val ξ : ℂ) * (cexp (L₀ ξ) * (cexp (Ldiff ξ) - 1))) ξ‖ := by
                rw [hfun]
      _ ≤ ‖Ldiff‖ * Bexp * (1 + ‖L₀‖) ^ n := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
      _ ≤ ‖Ldiff‖ * Bexp * (1 + L₀bd) ^ n := by
            have hbase : 1 + ‖L₀‖ ≤ 1 + L₀bd := by linarith
            gcongr
      _ ≤ (K * ‖z - z₀‖) * Bexp * (1 + L₀bd) ^ n := by
            gcongr
            exact multiDimPsiExpCLM_norm_le (z - z₀)
      _ ≤ D * ‖z - z₀‖ := by
            dsimp [D]
            have hz_nonneg : 0 ≤ ‖z - z₀‖ := norm_nonneg _
            nlinarith [hK_nonneg]
  exact SchwartzMap.seminorm_le_bound ℝ k n
    (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz -
      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z₀ hz₀)
    (by positivity) hpoint

/-- **Difference quotient of ψ_z converges in Schwartz seminorms.**

    For fixed z in the tube and direction e_j, there exists a derivative
    Schwartz function ψ'_j such that for all (k,n):

      seminorm k n ((ψ_{z+he_j} - ψ_z)/h - ψ'_j) ≤ D * |h|

    The derivative Schwartz function is ψ'_j(ξ) = χ(ξ) * (iξ_j) * exp(iz·ξ).

    **Proof sketch** (Vladimirov, "Methods of Generalized Functions", §25):
    The derivative Schwartz function is constructed as:
      ψ'_j(ξ) = χ(ξ) · (iξ_j) · exp(iz·ξ)

    This is Schwartz by the same argument as psiZRSchwartz (the extra iξ_j
    polynomial factor is absorbed by exponential decay).

    The remainder at ξ is:
      r_h(ξ) = χ(ξ) · exp(iz·ξ) · (exp(ihξ_j) - 1 - ihξ_j) / h

    By Taylor's theorem: |exp(ihξ_j) - 1 - ihξ_j| ≤ |h|²|ξ_j|²/2,
    so |r_h(ξ)| ≤ |h| · |ξ_j|² · |exp(iz·ξ)| / 2.

    The ξ_j² factor is absorbed by the exponential decay exp(-c‖ξ‖),
    giving ‖ξ‖^k · |D^n[r_h](ξ)| ≤ D' · |h|.

    Then seminorm_le_bound gives: seminorm k n (r_h) ≤ D · |h|.

    **Structure of the proof**:
    1. Construct ψ'_j as a SchwartzMap (smooth, rapid decay by decay of χ·exp)
    2. Choose δ₀ from update_mem_tubeDomain_of_small (tube is open)
    3. For each (k,n), bound the remainder using Taylor + exponential decay -/
theorem multiDimPsiZ_differenceQuotient_seminorm_bound
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) :
    ∃ (ψ'_j : SchwartzMap (Fin m → ℝ) ℂ),
      ∀ (k n : ℕ), ∃ (D : ℝ) (δ₀ : ℝ), D > 0 ∧ δ₀ > 0 ∧
        ∀ (h : ℂ), h ≠ 0 → ‖h‖ < δ₀ →
          (Function.update z j (z j + h) ∈ SCV.TubeDomain C) ∧
          SchwartzMap.seminorm ℝ k n
            ((h⁻¹ • (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
                (Function.update z j (z j + h))
              - multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz))
              - ψ'_j) ≤ D * ‖h‖ := by
  refine ⟨multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j, ?_⟩
  intro k n
  obtain ⟨δ_tube, hδ_tube, hδ_mem⟩ := update_mem_tubeDomain_of_small C hC_open z hz j
  let χ : FixedConeCutoff (DualConeFlat C) :=
    (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  let y : Fin m → ℝ := fun i => (z i).im
  have hy : y ∈ C := hz
  have hC_star_ne : (DualConeFlat C).Nonempty := ⟨0, zero_mem_dualConeFlat C⟩
  have hC_star_closed : IsClosed (DualConeFlat C) := dualConeFlat_closed C
  obtain ⟨c₀, hc₀_pos, hc₀⟩ :=
    dualConeFlat_coercivity hC_open hC_cone hy hC_star_ne hC_star_closed
  let K : ℝ := (Fintype.card (Fin m) : ℝ)
  let K2 : ℝ := ((Fintype.card (Fin m) : ℝ) ^ 2)
  let δ₀ : ℝ := min δ_tube (min 1 (c₀ / 2))
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    refine lt_min hδ_tube ?_
    refine lt_min zero_lt_one ?_
    positivity
  let A₀ : ℝ := c₀ + K2 * ‖y‖
  let L₀ : (Fin m → ℝ) →L[ℝ] ℂ := multiDimPsiExpCLM z
  obtain ⟨Bexp, hBexp_pos, hBexp⟩ :=
    schwartz_seminorm_cutoff_exp_mul_G_bound_affine_uniform
      χ.val χ.smooth χ.deriv_bound A₀ c₀ hc₀_pos k n
  let L₀bd : ℝ := K * ‖z‖
  let D : ℝ := Bexp * (1 + L₀bd) ^ n
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, δ₀, hD_pos, hδ₀_pos, ?_⟩
  intro h hh hh_dist
  have hh_tube : ‖h‖ < δ_tube := lt_of_lt_of_le hh_dist (min_le_left _ _)
  have hh_small : ‖h‖ < min 1 (c₀ / 2) := lt_of_lt_of_le hh_dist (min_le_right _ _)
  have hh1 : ‖h‖ ≤ 1 := hh_small.le.trans (min_le_left _ _)
  have hhc : ‖h‖ ≤ c₀ / 2 := hh_small.le.trans (min_le_right _ _)
  have hz' : Function.update z j (z j + h) ∈ SCV.TubeDomain C := hδ_mem h hh_tube
  refine ⟨hz', ?_⟩
  have hexp_decay :
      ∀ ξ : Fin m → ℝ, χ.val ξ ≠ 0 → (L₀ ξ).re ≤ A₀ - c₀ * ‖ξ‖ := by
    intro ξ hχξ
    have hdistχ : Metric.infDist ξ (DualConeFlat C) ≤ 1 := by
      by_contra hcontr
      exact hχξ (χ.support_bound ξ (by linarith))
    have hExpBound :
        ‖cexp (L₀ ξ)‖ ≤ Real.exp A₀ * Real.exp (-(c₀ * ‖ξ‖)) := by
      calc
        ‖cexp (L₀ ξ)‖ = ‖cexp (I * ∑ i, z i * (ξ i : ℂ))‖ := by
          rw [multiDimPsiExpCLM_apply]
        _ ≤ Real.exp (((c₀ + K2 * ‖y‖) * 1)) * Real.exp (-(c₀ * ‖ξ‖)) := by
            simpa [K2, y] using
              cexp_bound_on_support hC_open hC_cone hz hc₀_pos hc₀ zero_lt_one ξ hdistχ
        _ = Real.exp A₀ * Real.exp (-(c₀ * ‖ξ‖)) := by
            simp [A₀]
    have hnormexp : ‖cexp (L₀ ξ)‖ = Real.exp ((L₀ ξ).re) := by
      rw [Complex.norm_exp]
    have hExp' : Real.exp ((L₀ ξ).re) ≤ Real.exp (A₀ - c₀ * ‖ξ‖) := by
      rw [← hnormexp]
      simpa [sub_eq_add_neg, Real.exp_add] using hExpBound
    exact Real.exp_le_exp.mp hExp'
  have hG_smooth :
      ContDiff ℝ ∞ (fun x : Fin m → ℝ =>
        (cexp (I * h * (x j : ℂ)) - 1 - I * h * (x j : ℂ)) / h) := by
    let p : (Fin m → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) j
    simpa [p, expTaylorLinearRemainderQuotPW] using
      (expTaylorLinearRemainderQuotPW_contDiff h).comp p.contDiff
  have hG_bound :
      ∀ i ≤ n, ∀ ξ : Fin m → ℝ,
        ‖iteratedFDeriv ℝ i
            (fun x : Fin m → ℝ =>
              (cexp (I * h * (x j : ℂ)) - 1 - I * h * (x j : ℂ)) / h) ξ‖ ≤
          ‖h‖ * (i.factorial : ℝ) * (1 + ‖ξ‖) ^ 2 * Real.exp ((c₀ / 2) * ‖ξ‖) := by
    intro i hi ξ
    exact norm_iteratedFDeriv_differenceQuotient_remainder_bound h j hh1 hhc i ξ
  have hL₀ : ‖L₀‖ ≤ L₀bd := by
    simpa [L₀, L₀bd, K] using multiDimPsiExpCLM_norm_le z
  have hpoint :
      ∀ ξ : Fin m → ℝ,
        ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n
              (⇑((h⁻¹ •
                    (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
                      (Function.update z j (z j + h)) -
                      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)) -
                  multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j)) ξ‖ ≤
            D * ‖h‖ := by
    intro ξ
    have hraw :=
      hBexp L₀ hexp_decay
        (fun x : Fin m → ℝ =>
          (cexp (I * h * (x j : ℂ)) - 1 - I * h * (x j : ℂ)) / h)
        hG_smooth ‖h‖ (norm_nonneg _) hG_bound ξ
    have hfun :
        ⇑((h⁻¹ •
              (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
                (Function.update z j (z j + h)) -
                multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)) -
            multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j) =
          (fun ξ : Fin m → ℝ =>
            (χ.val ξ : ℂ) *
              (cexp (L₀ ξ) *
                ((cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)) / h))) := by
      funext ξ
      rw [multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient
        (Function.update z j (z j + h)) hz']
      simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, Pi.smul_apply]
      calc
        h⁻¹ *
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
                (Function.update z j (z j + h)) hz' ξ -
              multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ) -
          multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j ξ
            =
          h⁻¹ *
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
                (Function.update z j (z j + h)) hz' ξ -
              multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ -
              h * multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j ξ) := by
                field_simp [hh]
        _ = h⁻¹ *
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ *
              (cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ))) := by
                rw [multiDimPsiZ_update_sub_sub_coordDeriv_apply
                  hC_open hC_conv hC_cone hC_salient z hz j h hz' ξ]
        _ = multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz ξ *
            ((cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)) / h) := by
                field_simp [hh]
        _ = (χ.val ξ : ℂ) *
            (cexp (L₀ ξ) * ((cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)) / h)) := by
                change psiZRaw χ 1 z ξ * ((cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)) / h) =
                  _
                simp [psiZRaw, L₀, multiDimPsiExpCLM_apply]
                ring
    calc
      ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n
              (⇑((h⁻¹ •
                    (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
                      (Function.update z j (z j + h)) -
                      multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)) -
                  multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j)) ξ‖
          = ‖ξ‖ ^ k *
              ‖iteratedFDeriv ℝ n
                  (fun ξ : Fin m → ℝ =>
                    (χ.val ξ : ℂ) *
                      (cexp (L₀ ξ) *
                        ((cexp (I * h * (ξ j : ℂ)) - 1 - I * h * (ξ j : ℂ)) / h))) ξ‖ := by
                rw [hfun]
      _ ≤ ‖h‖ * Bexp * (1 + ‖L₀‖) ^ n := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
      _ ≤ ‖h‖ * Bexp * (1 + L₀bd) ^ n := by
            have hbase : 1 + ‖L₀‖ ≤ 1 + L₀bd := by linarith
            gcongr
      _ ≤ D * ‖h‖ := by
            dsimp [D]
            ring_nf
            nlinarith [norm_nonneg h]
  exact SchwartzMap.seminorm_le_bound ℝ k n
    ((h⁻¹ •
        (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
          (Function.update z j (z j + h)) -
          multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)) -
      multiDimPsiZCoordDeriv hC_open hC_conv hC_cone hC_salient z hz j)
    (by positivity) hpoint

/-- The dynamically scaled family has Vladimirov-type seminorm growth. -/
theorem multiDimPsiZDynamic_seminorm_bound {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (k n : ℕ) :
    ∃ (B : ℝ) (N M : ℕ), B > 0 ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
        SchwartzMap.seminorm ℝ k n (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz) ≤
          B * (1 + ‖z‖) ^ N *
            (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M := by
  obtain ⟨B₀, N₀, M₀, hB₀, hbound⟩ :=
    psiZRSchwartz_seminorm_vladimirovBound hC_open hC_conv hC_cone hC_salient k n
  exact ⟨B₀, N₀, M₀, hB₀, hbound⟩

/-- Finset-sup version of `multiDimPsiZDynamic_seminorm_bound`. -/
theorem multiDimPsiZDynamic_finset_sup_bound {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (s : Finset (ℕ × ℕ)) :
    ∃ (B : ℝ) (N M : ℕ), B > 0 ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
        (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ))
          (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz) ≤
          B * (1 + ‖z‖) ^ N *
            (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M := by
  induction s using Finset.induction with
  | empty =>
    exact ⟨1, 0, 0, one_pos, fun z hz => by simp [Finset.sup_empty]⟩
  | @insert a s ha ih =>
    obtain ⟨B₁, N₁, M₁, hB₁, h₁⟩ := ih
    obtain ⟨B₂, N₂, M₂, hB₂, h₂⟩ :=
      multiDimPsiZDynamic_seminorm_bound C hC_open hC_conv hC_cone hC_salient a.1 a.2
    refine ⟨max B₁ B₂, max N₁ N₂, max M₁ M₂, lt_max_of_lt_left hB₁, fun z hz => ?_⟩
    rw [Finset.sup_insert]
    apply sup_le
    · calc (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ a)
              (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz)
          = SchwartzMap.seminorm ℂ a.1 a.2
              (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz) := by
            simp [schwartzSeminormFamily]
        _ ≤ B₂ * (1 + ‖z‖) ^ N₂ *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M₂ := by
            simp only [SchwartzMap.seminorm_apply] at h₂ ⊢
            exact h₂ z hz
        _ ≤ max B₁ B₂ * (1 + ‖z‖) ^ (max N₁ N₂) *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ (max M₁ M₂) := by
            have hx1 : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg _)
            have hy1 : 1 ≤ 1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹ :=
              le_add_of_nonneg_right (inv_nonneg.mpr Metric.infDist_nonneg)
            have hxN : (1 + ‖z‖) ^ N₂ ≤
                (1 + ‖z‖) ^ (max N₁ N₂) :=
              pow_le_pow_right₀ hx1 (le_max_right _ _)
            have hyM : (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M₂ ≤
                (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ (max M₁ M₂) :=
              pow_le_pow_right₀ hy1 (le_max_right _ _)
            have hB : B₂ ≤ max B₁ B₂ := le_max_right _ _
            exact mul_le_mul
              (mul_le_mul hB hxN (pow_nonneg (le_trans zero_le_one hx1) _)
                (le_trans (le_of_lt hB₂) hB))
              hyM (pow_nonneg (le_trans zero_le_one hy1) _)
              (mul_nonneg (le_trans (le_of_lt hB₂) hB)
                (pow_nonneg (le_trans zero_le_one hx1) _))
    · calc (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ))
              (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz)
          ≤ B₁ * (1 + ‖z‖) ^ N₁ *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M₁ := h₁ z hz
        _ ≤ max B₁ B₂ * (1 + ‖z‖) ^ (max N₁ N₂) *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ (max M₁ M₂) := by
            have hx1 : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg _)
            have hy1 : 1 ≤ 1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹ :=
              le_add_of_nonneg_right (inv_nonneg.mpr Metric.infDist_nonneg)
            have hxN : (1 + ‖z‖) ^ N₁ ≤
                (1 + ‖z‖) ^ (max N₁ N₂) :=
              pow_le_pow_right₀ hx1 (le_max_left _ _)
            have hyM : (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M₁ ≤
                (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ (max M₁ M₂) :=
              pow_le_pow_right₀ hy1 (le_max_left _ _)
            have hB : B₁ ≤ max B₁ B₂ := le_max_left _ _
            exact mul_le_mul
              (mul_le_mul hB hxN (pow_nonneg (le_trans zero_le_one hx1) _)
                (le_trans (le_of_lt hB₁) hB))
              hyM (pow_nonneg (le_trans zero_le_one hy1) _)
              (mul_nonneg (le_trans (le_of_lt hB₁) hB)
                (pow_nonneg (le_trans zero_le_one hx1) _))

/-- z ↦ ψ_z is continuous into Schwartz space: for each seminorm (k,n),
    `z ↦ seminorm k n (ψ_{z'} - ψ_z) → 0` as `z' → z` in the tube.

    This is used to prove continuity of F(z) = T(ψ_z) on the tube. -/
theorem multiDimPsiZ_seminorm_continuous {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (k n : ℕ)
    (z₀ : Fin m → ℂ) (hz₀ : z₀ ∈ SCV.TubeDomain C) :
    ∀ ε > 0, ∃ δ > 0, ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
      ‖z - z₀‖ < δ →
        SchwartzMap.seminorm ℝ k n
          (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz -
           multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z₀ hz₀) < ε := by
  obtain ⟨D, δ₀, hD, hδ₀, hLip⟩ :=
    multiDimPsiZ_seminorm_difference_bound hC_open hC_conv hC_cone hC_salient k n z₀ hz₀
  intro ε hε
  refine ⟨min δ₀ (ε / (D + 1)), lt_min hδ₀ (div_pos hε (by linarith)), fun z hz hzd => ?_⟩
  have hzd_δ₀ : ‖z - z₀‖ < δ₀ := lt_of_lt_of_le hzd (min_le_left _ _)
  have hzd_eps : ‖z - z₀‖ < ε / (D + 1) := lt_of_lt_of_le hzd (min_le_right _ _)
  calc SchwartzMap.seminorm ℝ k n _ ≤ D * ‖z - z₀‖ := hLip z hz hzd_δ₀
    _ < D * (ε / (D + 1)) := mul_lt_mul_of_pos_left hzd_eps hD
    _ ≤ ε := by
        have h1 : 0 < D + 1 := by linarith
        calc D * (ε / (D + 1)) = D / (D + 1) * ε := by ring
          _ ≤ 1 * ε := by gcongr; exact (div_le_one h1).mpr (by linarith)
          _ = ε := one_mul ε

/-- The difference quotient of ψ_z converges in Schwartz seminorms.
    For fixed z in the tube and direction e_j:

    ‖(ψ_{z+he_j} - ψ_z)/h - ∂_{z_j} ψ_z‖_{k,n} → 0 as h → 0

    Proved via the axiom `multiDimPsiZ_differenceQuotient_seminorm_bound`. -/
theorem multiDimPsiZ_differenceQuotient_converges {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C)
    (j : Fin m) :
    ∃ (ψ'_j : SchwartzMap (Fin m → ℝ) ℂ),
      ∀ (k n : ℕ),
        Filter.Tendsto
          (fun h : ℂ => SchwartzMap.seminorm ℝ k n
            ((h⁻¹ • (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
                (Function.update z j (z j + h))
              - multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz))
              - ψ'_j))
          (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  obtain ⟨ψ'_j, hψ'_j⟩ :=
    multiDimPsiZ_differenceQuotient_seminorm_bound hC_open hC_conv hC_cone hC_salient z hz j
  refine ⟨ψ'_j, fun k n => ?_⟩
  obtain ⟨D, δ₀, hD, hδ₀, hbound⟩ := hψ'_j k n
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min δ₀ (ε / (D + 1)), lt_min hδ₀ (div_pos hε (by linarith)), fun h hh_mem hh_dist => ?_⟩
  have hh_norm : ‖h‖ < min δ₀ (ε / (D + 1)) := by
    rwa [show dist h 0 = ‖h‖ from by simp [dist_eq_norm]] at hh_dist
  have hh_ne : h ≠ 0 := by
    intro h0; simp [h0] at hh_mem
  obtain ⟨_, hsn⟩ := hbound h hh_ne (lt_of_lt_of_le hh_norm (min_le_left _ _))
  simp only [Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (by positivity)]
  calc SchwartzMap.seminorm ℝ k n _ ≤ D * ‖h‖ := hsn
    _ < D * (ε / (D + 1)) :=
        mul_lt_mul_of_pos_left (lt_of_lt_of_le hh_norm (min_le_right _ _)) hD
    _ ≤ ε := by
        have h1 : 0 < D + 1 := by linarith
        calc D * (ε / (D + 1)) = D / (D + 1) * ε := by ring
          _ ≤ 1 * ε := by gcongr; exact (div_le_one h1).mpr (by linarith)
          _ = ε := one_mul ε

/-- For Fourier-supported functionals, the value of `T(ψ_{z,R})` is independent
    of the cutoff radius. This is the key bridge between fixed-radius
    holomorphicity and dynamic-radius growth estimates. -/
theorem multiDimPsiZR_eval_eq_of_support {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT_support : HasFourierSupportInDualCone C T)
    (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    T (multiDimPsiZR C hC_open hC_conv hC_cone hC_salient R₁ hR₁ z hz) =
      T (multiDimPsiZR C hC_open hC_conv hC_cone hC_salient R₂ hR₂ z hz) := by
  -- T(ψ_{R₁}) - T(ψ_{R₂}) = T(ψ_{R₁} - ψ_{R₂}) by linearity
  -- The difference ψ_{R₁} - ψ_{R₂} is supported outside DualConeFlat C
  -- (both cutoffs = 1 on C* by one_on_neighborhood), so T kills it
  -- by HasFourierSupportInDualCone.
  -- T(ψ_{R₁} - ψ_{R₂}) = 0 since the difference is supported outside DualConeFlat C
  suffices h : T (multiDimPsiZR C hC_open hC_conv hC_cone hC_salient R₁ hR₁ z hz -
      multiDimPsiZR C hC_open hC_conv hC_cone hC_salient R₂ hR₂ z hz) = 0 by
    rwa [map_sub, sub_eq_zero] at h
  apply hT_support
  intro ξ hξ_supp hξ_dual
  -- ξ is in the support, meaning the difference is nonzero at ξ
  -- But ξ ∈ DualConeFlat C, and both ψ agree there
  exfalso
  apply hξ_supp
  simp only [SchwartzMap.sub_apply, sub_eq_zero]
  -- The two multiDimPsiZR values agree at ξ ∈ DualConeFlat C
  change (psiZRSchwartz hC_open hC_cone hC_salient _ R₁ hR₁ z hz) ξ =
    (psiZRSchwartz hC_open hC_cone hC_salient _ R₂ hR₂ z hz) ξ
  exact psiZRaw_eq_on_dualCone _ hR₁ hR₂ z ξ hξ_dual

private theorem finset_sum_schwartzSeminorm_apply
    (s : Finset (ℕ × ℕ)) (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    (∑ p ∈ s, schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ p) φ =
      ∑ p ∈ s, (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ p) φ := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      simp [ha, Seminorm.add_apply, ih]

private theorem schwartz_clm_bound_by_finset_sup_aux
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0), C ≠ 0 ∧
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ),
        ‖T f‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) f := by
  let q : Seminorm ℂ (SchwartzMap (Fin m → ℝ) ℂ) :=
    (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq_cont : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC_ne, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (Fin m → ℝ) ℂ) q hq_cont
  refine ⟨s, C, hC_ne, fun f => ?_⟩
  calc ‖T f‖ = q f := rfl
    _ ≤ (C • s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) f := hbound f
    _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) f := by
        rfl

/-! ### The Fourier-Laplace extension -/

/-- The Fourier-Laplace extension: F(z) = T(ψ_z) for z in the tube T(C),
    extended by 0 outside the tube. This avoids threading membership proofs
    through differentiability arguments.

    This is the multi-dimensional generalization of `fourierLaplaceExt`. -/
def fourierLaplaceExtMultiDim
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (z : Fin m → ℂ) : ℂ :=
  if hz : z ∈ SCV.TubeDomain C then
    T (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)
  else 0

theorem fourierLaplaceExtMultiDim_eq
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T z =
      T (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) := by
  simp [fourierLaplaceExtMultiDim, hz]

theorem fourierLaplaceExtMultiDim_eq_ext
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (z : Fin m → ℂ) :
    fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T z =
      T (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z) := by
  by_cases hz : z ∈ SCV.TubeDomain C
  · simp [fourierLaplaceExtMultiDim, multiDimPsiZExt, hz]
  · simp [fourierLaplaceExtMultiDim, multiDimPsiZExt, hz]

/-! ### Holomorphicity via Osgood -/

/-- F(z) = T(ψ_z) is separately holomorphic in each variable z_j.

    Proof: The difference quotient (F(z+he_j) - F(z))/h = T((ψ_{z+he_j} - ψ_z)/h)
    converges to T(ψ'_j) by continuity of T and the seminorm convergence
    from `multiDimPsiZ_differenceQuotient_converges`. -/
theorem fourierLaplaceExtMultiDim_separatelyHolomorphic
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (_hT_support : HasFourierSupportInDualCone C T)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) :
    DifferentiableAt ℂ
      (fun w => fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
        (Function.update z j w))
      (z j) := by
  let dq : ℂ → SchwartzMap (Fin m → ℝ) ℂ := fun h =>
    h⁻¹ •
      (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient (Function.update z j (z j + h)) -
        multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)
  obtain ⟨ψ'_j, hψ'_j⟩ :=
    multiDimPsiZ_differenceQuotient_converges C hC_open hC_conv hC_cone hC_salient z hz j
  obtain ⟨s, C_T, hC_T_ne, hT_bound⟩ := schwartz_clm_bound_by_finset_sup_aux T
  have hC_T_pos : 0 < (C_T : ℝ) := by
    rcases eq_or_lt_of_le C_T.coe_nonneg with h | h
    · exact absurd (NNReal.coe_eq_zero.mp h.symm) hC_T_ne
    · exact h
  have hsum_tendsto :
      ∀ s' : Finset (ℕ × ℕ),
        Filter.Tendsto
          (fun h : ℂ => ∑ p ∈ s', SchwartzMap.seminorm ℝ p.1 p.2 (dq h - ψ'_j))
          (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    intro s'
    induction s' using Finset.induction_on with
    | empty =>
        simp
    | insert a s' ha ih =>
        simpa [Finset.sum_insert, ha] using (hψ'_j a.1 a.2).add ih
  have hT_zero :
      Filter.Tendsto (fun h : ℂ => T (dq h - ψ'_j))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hε' : 0 < ε / (C_T : ℝ) := div_pos hε hC_T_pos
    have hsmall := Metric.tendsto_nhds.1 (hsum_tendsto s) (ε / (C_T : ℝ)) hε'
    filter_upwards [hsmall] with h hh
    have hsum_nonneg :
        0 ≤ ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (dq h - ψ'_j) := by
      refine Finset.sum_nonneg ?_
      intro p hp
      positivity
    have hh' :
        ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (dq h - ψ'_j) < ε / (C_T : ℝ) := by
      simpa [Real.dist_eq, abs_of_nonneg hsum_nonneg] using hh
    have hsup :
        (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) (dq h - ψ'_j) ≤
          ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (dq h - ψ'_j) := by
      calc
        (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) (dq h - ψ'_j)
            ≤ (∑ p ∈ s, schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ p) (dq h - ψ'_j) :=
              Seminorm.le_def.mp
                (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) s)
                _
        _ = ∑ p ∈ s, (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ p) (dq h - ψ'_j) := by
              simpa using finset_sum_schwartzSeminorm_apply s (dq h - ψ'_j)
        _ = ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (dq h - ψ'_j) := by
              simp [schwartzSeminormFamily, SchwartzMap.seminorm_apply]
    have hnorm :
        ‖T (dq h - ψ'_j)‖ < ε := by
      calc
        ‖T (dq h - ψ'_j)‖
            ≤ (C_T : ℝ) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) (dq h - ψ'_j) :=
              hT_bound _
        _ ≤ (C_T : ℝ) * ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (dq h - ψ'_j) := by
              exact mul_le_mul_of_nonneg_left hsup C_T.coe_nonneg
        _ < (C_T : ℝ) * (ε / (C_T : ℝ)) := by
              exact mul_lt_mul_of_pos_left hh' hC_T_pos
        _ = ε := by
              field_simp [hC_T_pos.ne']
    simpa [dist_eq_norm] using hnorm
  have hT_tendsto :
      Filter.Tendsto (fun h : ℂ => T (dq h))
        (nhdsWithin 0 {0}ᶜ) (nhds (T ψ'_j)) := by
    have hconst :
        Filter.Tendsto (fun _ : ℂ => T ψ'_j)
          (nhdsWithin 0 {0}ᶜ) (nhds (T ψ'_j)) :=
      tendsto_const_nhds
    have haux :
        Filter.Tendsto (fun h : ℂ => T (dq h - ψ'_j) + T ψ'_j)
          (nhdsWithin 0 {0}ᶜ) (nhds (T ψ'_j)) := by
      simpa using hT_zero.add hconst
    have hEq : (fun h : ℂ => T (dq h - ψ'_j) + T ψ'_j) = fun h : ℂ => T (dq h) := by
      funext h
      simp [sub_eq_add_neg, add_comm]
    exact hEq ▸ haux
  have hderiv :
      HasDerivAt
        (fun w => fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
          (Function.update z j w))
        (T ψ'_j) (z j) := by
    have hzext :
        multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z =
          multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz :=
      multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient z hz
    have hslope_eq :
        (fun t : ℂ =>
          t⁻¹ •
            ((fun w => fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
                (Function.update z j w)) (z j + t) -
              (fun w => fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
                (Function.update z j w)) (z j))) =
          fun t : ℂ => T (dq t) := by
      funext t
      simp [dq, fourierLaplaceExtMultiDim_eq_ext, hzext, map_sub, map_smul]
    refine (hasDerivAt_iff_tendsto_slope_zero).2 ?_
    exact hslope_eq ▸ hT_tendsto
  exact hderiv.differentiableAt

/-- F(z) = T(ψ_z) is continuous on the tube.

    Proof: T is continuous on Schwartz space, and z ↦ ψ_z is continuous
    into Schwartz space (by the seminorm bounds). -/
theorem fourierLaplaceExtMultiDim_continuousOn
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (_hT_support : HasFourierSupportInDualCone C T) :
    ContinuousOn
      (fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T)
      (SCV.TubeDomain C) := by
  rw [continuousOn_iff_continuous_restrict]
  let ψ : SCV.TubeDomain C → SchwartzMap (Fin m → ℝ) ℂ :=
    fun z => multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z.1 z.2
  have hψ_cont : Continuous ψ := by
    rw [continuous_iff_continuousAt]
    intro z
    rw [ContinuousAt]
    exact ((schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds ψ (ψ z)).2 <| by
      intro p ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ :=
        multiDimPsiZ_seminorm_continuous C hC_open hC_conv hC_cone hC_salient p.1 p.2 z.1 z.2 ε hε
      filter_upwards [Metric.ball_mem_nhds z hδ_pos] with w hw
      exact hδ w.1 w.2 (by
        have : dist (w : Fin m → ℂ) (z : Fin m → ℂ) = ‖(w : Fin m → ℂ) - (z : Fin m → ℂ)‖ :=
          dist_eq_norm _ _
        have hwd : dist (w : Fin m → ℂ) (z : Fin m → ℂ) < δ := hw
        linarith)
  have hcont : Continuous fun z : SCV.TubeDomain C => T (ψ z) :=
    T.continuous.comp hψ_cont
  convert hcont using 1
  ext z
  simpa [ψ] using fourierLaplaceExtMultiDim_eq C hC_open hC_conv hC_cone hC_salient T z.1 z.2

/-- **Main holomorphicity theorem**: F(z) = T(ψ_z) is holomorphic on the tube T(C).

    Proof: Combine separate holomorphicity + continuity via `osgood_lemma`. -/
theorem fourierLaplaceExtMultiDim_holomorphic
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT_support : HasFourierSupportInDualCone C T) :
    DifferentiableOn ℂ
      (fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T)
      (SCV.TubeDomain C) := by
  apply osgood_lemma (SCV.tubeDomain_isOpen hC_open)
  · exact fourierLaplaceExtMultiDim_continuousOn C hC_open hC_conv hC_cone hC_salient T hT_support
  · intro z hz j
    exact fourierLaplaceExtMultiDim_separatelyHolomorphic
      C hC_open hC_conv hC_cone hC_salient T hT_support z hz j

/-- Under the Fourier-support hypothesis, the radius-1 evaluation agrees with
    the dynamically scaled evaluation. -/
theorem fourierLaplaceExtMultiDim_eq_dynamic
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT_support : HasFourierSupportInDualCone C T)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T z =
      T (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz) := by
  rw [fourierLaplaceExtMultiDim_eq C hC_open hC_conv hC_cone hC_salient T z hz]
  simpa [multiDimPsiZ, multiDimPsiZDynamic] using
    multiDimPsiZR_eval_eq_of_support C hC_open hC_conv hC_cone hC_salient T hT_support
      1 (multiDimPsiZRadius z) zero_lt_one (multiDimPsiZRadius_pos z) z hz

/-! ### Continuous functionals are seminorm-bounded -/

/-- Version with finset sup: a continuous linear functional on Schwartz space
    is bounded by a finite sup of Schwartz seminorms. This follows directly
    from `Seminorm.bound_of_continuous` applied to `schwartz_withSeminorms`. -/
theorem schwartz_clm_bound_by_finset_sup
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0), C ≠ 0 ∧
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ),
        ‖T f‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) f := by
  exact schwartz_clm_bound_by_finset_sup_aux T

/-! ### Growth bound -/

/-- F(z) = T(ψ_z) satisfies the global Vladimirov growth bound.

    Proof: |F(z)| = |T(ψ_z)| ≤ ‖T‖ · ‖ψ_z‖_{k,n} for some seminorm.
    By the dynamic-radius seminorm bound:
    ‖ψ_z‖_{k,n} ≤ B · (1+‖z‖)^N · (1 + dist(Im z, ∂C)⁻¹)^M -/
theorem fourierLaplaceExtMultiDim_vladimirov_growth
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT_support : HasFourierSupportInDualCone C T) :
    ∃ (C_bd : ℝ) (N M : ℕ), C_bd > 0 ∧
      ∀ (z : Fin m → ℂ), z ∈ SCV.TubeDomain C →
        ‖fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T z‖ ≤
          C_bd * (1 + ‖z‖) ^ N *
            (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M := by
  -- Step 1: T is bounded by a finset sup of seminorms (PROVED, no sorry)
  obtain ⟨s, C_T, hC_T_ne, hT_bound⟩ := schwartz_clm_bound_by_finset_sup T
  have hC_T_pos : (0 : ℝ) < C_T := by
    rcases eq_or_lt_of_le C_T.coe_nonneg with h | h
    · exact absurd (NNReal.coe_eq_zero.mp h.symm) hC_T_ne
    · exact h
  -- Step 2: The finset sup of seminorms of ψ_z has Vladimirov-type growth
  obtain ⟨B, N, M, hB_pos, hψ_bound⟩ :=
    multiDimPsiZDynamic_finset_sup_bound C hC_open hC_conv hC_cone hC_salient s
  -- Step 3: Combine
  refine ⟨C_T * B, N, M, mul_pos hC_T_pos hB_pos, fun z hz => ?_⟩
  rw [fourierLaplaceExtMultiDim_eq_dynamic C hC_open hC_conv hC_cone hC_salient T hT_support z hz]
  calc ‖T (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz)‖
    _ ≤ C_T * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ))
          (multiDimPsiZDynamic C hC_open hC_conv hC_cone hC_salient z hz) := hT_bound _
    _ ≤ C_T * (B * (1 + ‖z‖) ^ N *
          (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M) := by
        apply mul_le_mul_of_nonneg_left (hψ_bound z hz) (by exact_mod_cast C_T.coe_nonneg)
    _ = C_T * B * (1 + ‖z‖) ^ N *
          (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M := by
        ring

/-! ### Fourier conventions and boundary values

**Fourier conventions**: The tube kernel uses `exp(ix·ξ)` (physics convention),
while Mathlib's `fourierTransformCLM` uses `exp(-2πi⟨x,ξ⟩)`. Both are provided:
- `inverseFourierFlatCLM`: Mathlib convention (forward FT transported to Fin m → ℝ)
- `physicsFourierFlatCLM`: physics convention, `f ↦ (ξ ↦ ∫ exp(ix·ξ) f(x) dx)`

The boundary value theorem uses the physics convention. -/

/-- The Mathlib-convention Fourier transform on `Fin m → ℝ`, defined by transporting
    through `EuclideanSpace ℝ (Fin m)` (which has `InnerProductSpace`)
    and applying Mathlib's `fourierTransformCLM`.

    This is a localized bridge: only the Fourier layer touches EuclideanSpace,
    while all cone/seminorm/decay estimates stay in the flat `Fin m → ℝ` type.

    Concretely: f ↦ (equiv ∘ FT ∘ equiv⁻¹)(f) where equiv is the
    `EuclideanSpace.equiv` continuous linear equivalence. -/
noncomputable def inverseFourierFlatCLM {m : ℕ} :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
  -- Localized Fourier bridge: transport to EuclideanSpace, apply FT, transport back.
  -- compCLMOfContinuousLinearEquiv g : 𝓢(E,F) →L 𝓢(D,F) via f ↦ f ∘ g
  -- So g : D ≃L[ℝ] E gives 𝓢(E) → 𝓢(D), i.e., "pullback by g"
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  -- toEuc: 𝓢(Fin m → ℝ) → 𝓢(EuclideanSpace) needs g : Euc ≃L (Fin m → ℝ) = e
  let toEuc : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  -- fromEuc: 𝓢(EuclideanSpace) → 𝓢(Fin m → ℝ) needs g : (Fin m → ℝ) ≃L Euc = e.symm
  let fromEuc : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let ft : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.fourierTransformCLM ℂ
  fromEuc.comp (ft.comp toEuc)

-- Physics-convention FT: f ↦ (ξ ↦ ∫ exp(ix·ξ) f(x) dx)
-- Related to Mathlib's by: FT_phys(f)(ξ) = FT_Mathlib(f)(-ξ/(2π))
noncomputable def physicsFourierFlatCLM {m : ℕ} :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
  let a : ℝˣ := Units.mk0 (-(1 / (2 * Real.pi) : ℝ)) <| by
    apply neg_ne_zero.mpr
    exact one_div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  let scaleNeg : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearEquiv.smulLeft a
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg).comp inverseFourierFlatCLM

@[simp] theorem physicsFourierFlatCLM_apply {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (ξ : Fin m → ℝ) :
    physicsFourierFlatCLM f ξ =
      inverseFourierFlatCLM f ((-(1 / (2 * Real.pi) : ℝ)) • ξ) := by
  simp [physicsFourierFlatCLM]

-- Pointwise integral formula for the flat Fourier transform.
private theorem fourierTransformFlat_eval
    (f : SchwartzMap (Fin m → ℝ) ℂ) (ξ : Fin m → ℝ) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (EuclideanSpace.equiv (Fin m) ℝ).symm
      ((SchwartzMap.fourierTransformCLM ℂ)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (EuclideanSpace.equiv (Fin m) ℝ) f))) ξ =
    ∫ x : Fin m → ℝ,
      exp (-2 * ↑Real.pi * I * (∑ i, (x i : ℂ) * (ξ i : ℂ))) * f x := by
  simp only [SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [Real.fourierChar_apply, Circle.smul_def, mul_neg, neg_mul, smul_eq_mul]
  have hcomp := ((PiLp.volume_preserving_toLp (ι := Fin m)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding
      (fun x : EuclideanSpace ℝ (Fin m) =>
        cexp (↑(-2 * Real.pi * inner ℝ x ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ)) * I) *
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin m) ℝ)) f) x)).symm
  calc
    ∫ v : EuclideanSpace ℝ (Fin m),
        cexp (↑(-(2 * Real.pi * inner ℝ v ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ))) * I) *
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin m) ℝ)) f) v
      = ∫ y : WithLp 2 (Fin m → ℝ),
          cexp (↑(-(2 * Real.pi * inner ℝ y ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ))) * I) * f y.ofLp := by
            simp [PiLp.coe_continuousLinearEquiv]
    _ = ∫ x : Fin m → ℝ,
          cexp (↑(-(2 * Real.pi * inner ℝ (WithLp.toLp 2 x) ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ))) * I) *
            f ((EuclideanSpace.equiv (Fin m) ℝ) (WithLp.toLp 2 x)) := by
            simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hcomp
    _ = ∫ x : Fin m → ℝ, cexp (-(2 * ↑Real.pi * I * (∑ i, (x i : ℂ) * (ξ i : ℂ)))) * f x := by
          apply integral_congr_ae
          filter_upwards with x
          have hx : ((EuclideanSpace.equiv (Fin m) ℝ) (WithLp.toLp 2 x)) = x := by
            ext i; simp [EuclideanSpace.equiv]
          rw [hx]
          have hinner : inner ℝ (WithLp.toLp 2 x) ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ) =
              ∑ i, x i * ξ i := by
            rw [PiLp.inner_apply]
            change ∑ i, ξ i * x i = ∑ i, x i * ξ i
            simp_rw [mul_comm]
          rw [hinner]
          congr 1
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private noncomputable def dualConeCutoff {m : ℕ} (C : Set (Fin m → ℝ)) :
    FixedConeCutoff (DualConeFlat C) :=
  (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some

private def etaPairingCLM {m : ℕ} (η : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ i, (η i) •
    (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i)

@[simp] private lemma etaPairingCLM_apply {m : ℕ} (η ξ : Fin m → ℝ) :
    etaPairingCLM η ξ = ∑ i, η i * ξ i := by
  simp [etaPairingCLM]

private lemma dualConeCutoff_hasTemperateGrowthComplex
    {m : ℕ} {C : Set (Fin m → ℝ)} :
    (fun ξ : Fin m → ℝ => ((dualConeCutoff C).val ξ : ℂ)).HasTemperateGrowth := by
  refine ⟨?_, fun n => ?_⟩
  · simpa [dualConeCutoff] using
      (Complex.ofRealCLM.contDiff.comp (dualConeCutoff C).smooth)
  · obtain ⟨Cn, hCn⟩ := (dualConeCutoff C).deriv_bound n
    refine ⟨0, Cn, fun ξ => ?_⟩
    have h_eq :
        ‖iteratedFDeriv ℝ n (fun x : Fin m → ℝ => ((dualConeCutoff C).val x : ℂ)) ξ‖ =
          ‖iteratedFDeriv ℝ n (dualConeCutoff C).val ξ‖ := by
      rw [show (fun x : Fin m → ℝ => ((dualConeCutoff C).val x : ℂ)) =
          (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (dualConeCutoff C).val from rfl]
      exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left
        ((contDiff_infty.mp (dualConeCutoff C).smooth n).contDiffAt) le_rfl
    rw [h_eq]
    calc
      ‖iteratedFDeriv ℝ n (dualConeCutoff C).val ξ‖ ≤ Cn := hCn ξ
      _ = Cn * (1 + ‖ξ‖) ^ (0 : ℕ) := by ring

/-- A fixed cone cutoff is identically `1` on the dual cone itself. -/
private lemma fixedConeCutoff_eq_one_on_dualCone
    {m : ℕ} {C : Set (Fin m → ℝ)}
    (χ : FixedConeCutoff (DualConeFlat C)) {ξ : Fin m → ℝ}
    (hξ : ξ ∈ DualConeFlat C) :
    χ.val ξ = 1 := by
  obtain ⟨ε, hε, hone⟩ := χ.one_on_neighborhood
  exact hone ξ (by simpa [Metric.infDist_zero_of_mem hξ] using hε)

/-- The point `x + iεη` lies in the tube domain `T(C)` when `ε > 0` and `η ∈ C`.

    Proof: `Im(x + iεη)_j = ε * η_j`, so `Im(z) = ε • η ∈ C` by the cone property. -/
private lemma realPlusIEpsEta_mem_tubeDomain
    (C : Set (Fin m → ℝ)) (hC_cone : IsCone C)
    (x : Fin m → ℝ) (η : Fin m → ℝ) (hη : η ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) ∈ SCV.TubeDomain C := by
  show (fun i => ((x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I).im) ∈ C
  have hIm : (fun i => ((x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I).im) = ε • η := by
    ext i
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
  rw [hIm]
  exact hC_cone η hη ε hε

/-- Pointwise identification of the Fubini-exchanged Schwartz kernel with the
regularized physics Fourier transform. This is the remaining kernel-computation
step in the boundary-value theorem. -/
theorem physicsFourierFlatCLM_integral
    {m : ℕ} (f : SchwartzMap (Fin m → ℝ) ℂ) (ξ : Fin m → ℝ) :
    (∫ x : Fin m → ℝ, Complex.exp (I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * f x) =
      physicsFourierFlatCLM f ξ := by
  rw [physicsFourierFlatCLM_apply]
  have harg :
      (∫ x : Fin m → ℝ,
        (Complex.exp
            (I * ((Real.pi : ℂ) * (2 * ∑ i,
              (ξ i : ℂ) * ((x i : ℂ) * (((Real.pi : ℂ)⁻¹ * (2 : ℂ)⁻¹)))))))
            * f x) =
      ∫ x : Fin m → ℝ, Complex.exp (I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * f x := by
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    have hs :
        (Real.pi : ℂ) * (2 * ∑ i,
            (ξ i : ℂ) * ((x i : ℂ) * (((Real.pi : ℂ)⁻¹ * (2 : ℂ)⁻¹))) ) =
          ∑ i, (x i : ℂ) * (ξ i : ℂ) := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      field_simp [Real.pi_ne_zero]
    rw [hs]
  calc
    ∫ x : Fin m → ℝ, Complex.exp (I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * f x
        = ∫ x : Fin m → ℝ,
            Complex.exp
              (I * ((Real.pi : ℂ) * (2 * ∑ i,
                (ξ i : ℂ) * ((x i : ℂ) * (((Real.pi : ℂ)⁻¹ * (2 : ℂ)⁻¹))))))
              * f x := by
              symm
              exact harg
    _ = inverseFourierFlatCLM f ((-(1 / (2 * Real.pi) : ℝ)) • ξ) := by
          symm
          simpa [inverseFourierFlatCLM, smul_eq_mul, Pi.smul_apply,
            mul_assoc, mul_left_comm, mul_comm] using
            (fourierTransformFlat_eval f ((-(1 / (2 * Real.pi) : ℝ)) • ξ))

/-- Pointwise identification of the Fubini-exchanged Schwartz kernel with the
regularized physics Fourier transform. This is the remaining kernel-computation
step in the boundary-value theorem. -/
private theorem regularizedKernel_pointwise
    {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (η : Fin m → ℝ) (hη : η ∈ C)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    ∀ (ε : ℝ), 0 < ε → ∀ ξ : Fin m → ℝ,
      (∫ x : Fin m → ℝ,
        multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
          (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) ξ * f x) =
        Complex.exp (-(ε : ℂ) * (etaPairingCLM η ξ : ℂ)) *
          (((dualConeCutoff C).val ξ : ℂ) * physicsFourierFlatCLM f ξ) := by
  intro ε hε ξ
  have hz : ∀ x : Fin m → ℝ,
      (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) ∈ SCV.TubeDomain C := by
    intro x
    exact realPlusIEpsEta_mem_tubeDomain C hC_cone x η hη ε hε
  let χ : FixedConeCutoff (DualConeFlat C) := dualConeCutoff C
  have hexp_split : ∀ x : Fin m → ℝ,
      Complex.exp
          (I * ∑ i, ((x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * (ξ i : ℂ)) =
        Complex.exp (-(ε : ℂ) * (etaPairingCLM η ξ : ℂ)) *
          Complex.exp (I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) := by
    intro x
    have hsum :
        I * ∑ i, ((x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * (ξ i : ℂ) =
          (-(ε : ℂ) * (etaPairingCLM η ξ : ℂ)) +
            I * ∑ i, (x i : ℂ) * (ξ i : ℂ) := by
      rw [etaPairingCLM_apply]
      simp_rw [add_mul, mul_assoc]
      rw [Finset.sum_add_distrib, mul_add]
      have hcross :
          I * ∑ x_1, I * (ε : ℂ) * (η x_1 : ℂ) * (ξ x_1 : ℂ) =
            -(ε : ℂ) * ↑(∑ x, η x * ξ x) := by
        calc
          I * ∑ x_1, I * (ε : ℂ) * (η x_1 : ℂ) * (ξ x_1 : ℂ) =
              ∑ x_1, I * (I * (ε : ℂ) * (η x_1 : ℂ) * (ξ x_1 : ℂ)) := by
                rw [Finset.mul_sum]
          _ = ∑ x_1, -((ε : ℂ) * ((η x_1 : ℂ) * (ξ x_1 : ℂ))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hterm :
                    I * (I * ((ε : ℂ) * (η i : ℂ) * (ξ i : ℂ))) =
                      -((ε : ℂ) * ((η i : ℂ) * (ξ i : ℂ))) := by
                  rw [show I * (I * ((ε : ℂ) * (η i : ℂ) * (ξ i : ℂ))) =
                      (I * I) * ((ε : ℂ) * (η i : ℂ) * (ξ i : ℂ)) by ring]
                  simp [Complex.I_sq]
                  ring
                have hterm' :
                    I * (I * (ε : ℂ) * (η i : ℂ) * (ξ i : ℂ)) =
                      -((ε : ℂ) * ((η i : ℂ) * (ξ i : ℂ))) := by
                  calc
                  I * (I * (ε : ℂ) * (η i : ℂ) * (ξ i : ℂ))
                      = I * (I * ((ε : ℂ) * (η i : ℂ) * (ξ i : ℂ))) := by ring
                  _ = -((ε : ℂ) * ((η i : ℂ) * (ξ i : ℂ))) := hterm
                simpa [mul_assoc] using hterm'
          _ = -(∑ x_1, (ε : ℂ) * ((η x_1 : ℂ) * (ξ x_1 : ℂ))) := by
                rw [Finset.sum_neg_distrib]
          _ = -((ε : ℂ) * ∑ x_1, (η x_1 : ℂ) * (ξ x_1 : ℂ)) := by
                rw [← Finset.mul_sum]
          _ = -(ε : ℂ) * ↑(∑ x, η x * ξ x) := by
                have hsumCast :
                    (∑ x_1, (η x_1 : ℂ) * (ξ x_1 : ℂ)) = ↑(∑ x, η x * ξ x) := by
                  exact_mod_cast rfl
                rw [hsumCast]
                ring
      have hcross' :
          I * ∑ x, (ε : ℂ) * ((η x : ℂ) * (I * (ξ x : ℂ))) =
            -(ε : ℂ) * ↑(∑ x, η x * ξ x) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
      rw [add_comm, hcross']
    rw [hsum, Complex.exp_add]
  calc
    (∫ x : Fin m → ℝ,
      multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
        (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) ξ * f x)
        =
      ∫ x : Fin m → ℝ,
        multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
          (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) (hz x) ξ * f x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient
            (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) (hz x)]
    _ =
      ∫ x : Fin m → ℝ,
        (((χ.val ξ : ℂ) *
          Complex.exp (-(ε : ℂ) * (etaPairingCLM η ξ : ℂ))) *
            (Complex.exp (I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * f x)) := by
          apply integral_congr_ae
          filter_upwards with x
          change (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
              (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) (hz x) ξ) * f x = _
          rw [show multiDimPsiZ C hC_open hC_conv hC_cone hC_salient
              (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) (hz x) ξ =
                psiZRaw χ 1 (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) ξ by
                rfl]
          rw [show psiZRaw χ 1 (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) ξ =
              (χ.val ξ : ℂ) *
                Complex.exp (I * ∑ i, ((x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * (ξ i : ℂ)) by
                simp [psiZRaw]]
          rw [hexp_split x]
          ring
    _ = (((χ.val ξ : ℂ) * Complex.exp (-(ε : ℂ) * (etaPairingCLM η ξ : ℂ))) *
          ∫ x : Fin m → ℝ, Complex.exp (I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * f x) := by
          simpa [mul_assoc] using
            (MeasureTheory.integral_const_mul
              (((χ.val ξ : ℂ) * Complex.exp (-(ε : ℂ) * (etaPairingCLM η ξ : ℂ)))
              ) (fun x : Fin m → ℝ =>
                Complex.exp (I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * f x))
    _ = Complex.exp (-(ε : ℂ) * (etaPairingCLM η ξ : ℂ)) *
          (((dualConeCutoff C).val ξ : ℂ) * physicsFourierFlatCLM f ξ) := by
          rw [physicsFourierFlatCLM_integral]
          ring

/-- **Boundary value convergence for the Fourier-Laplace extension.**

    For T with Fourier support in C* and F(z) = fourierLaplaceExtMultiDim T z,
    the distributional boundary value ∫ F(x+iεη)f(x)dx → T(FT⁻¹(f)) as ε→0⁺.

    **Proof structure** (Route A):
    1. For ε > 0, the point x + iεη lies in tube T(C) by cone scaling.
    2. F(x+iεη) = T(ψ_{x+iεη}) by definition of `fourierLaplaceExtMultiDim`.
    3. Exchange T and ∫: ∫ T(ψ_{x+iεη}) f(x) dx = T(∫ ψ_{x+iεη} f(x) dx)
       by continuity of T (Bochner integral exchange for CLM on Schwartz space).
    4. Define Φ_ε(ξ) = ∫ ψ_{x+iεη}(ξ) f(x) dx.
       Pointwise: Φ_ε(ξ) = χ(ξ) exp(-εη·ξ) ∫ exp(ix·ξ) f(x) dx
                          = χ(ξ) exp(-εη·ξ) FT(f)(ξ).
    5. As ε→0⁺, Φ_ε → χ · FT(f) in Schwartz topology
       (uniform in ξ with all derivatives, from dominated convergence
       using `multiDimPsiZ_seminorm_difference_bound`).
    6. Since T has Fourier support in C* and χ = 1 on C*:
       T(χ · FT(f)) = T(FT(f)) = T(FT⁻¹(f)) by the Fourier support property.
    7. By continuity of T: T(Φ_ε) → T(FT⁻¹(f)).

    **Current status**: The 1 remaining sorry is the BV convergence proof.
    The Fubini/exchange step is now isolated through
    `schwartz_clm_fubini_exchange`; the remaining formal work is the
    regularized-kernel damping limit. -/

-- **Axiom: Scalar DCT for parameter-dependent integrals.**
-- g_ε(x) → L(x) pointwise with polynomial dominator, f Schwartz,
-- so ∫ g_ε(x) f(x) dx → ∫ L(x) f(x) dx by dominated convergence.
-- This is pure real analysis (Lebesgue DCT). Provable from Mathlib's
-- MeasureTheory.tendsto_integral_of_dominated_convergence once
-- the measurability/integrability bookkeeping is done.
-- Ref: Vladimirov §25; Reed-Simon I §IX.3.
-- Scalar DCT for Schwartz pairings via tendsto_integral_filter_of_dominated_convergence.
theorem scalar_dct_schwartz_pairing {m : ℕ}
    (g : ℝ → (Fin m → ℝ) → ℂ)
    (L : (Fin m → ℝ) → ℂ)
    (hg_meas : ∀ ε, AEStronglyMeasurable (g ε) MeasureTheory.volume)
    (hconv : ∀ (x : Fin m → ℝ),
      Filter.Tendsto (fun ε => g ε x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (L x)))
    (hdom : ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (x : Fin m → ℝ),
        ‖g ε x‖ ≤ C * (1 + ‖x‖) ^ N)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    Filter.Tendsto
      (fun ε => ∫ x : Fin m → ℝ, g ε x * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x : Fin m → ℝ, L x * f x)) := by
  obtain ⟨C_bd, N, hC_pos, hbound⟩ := hdom
  -- Apply Mathlib's filter DCT
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => C_bd * (1 + ‖x‖) ^ N * ‖f x‖)
  · -- AEStronglyMeasurable for the family
    filter_upwards with ε
    exact (hg_meas ε).mul f.continuous.aestronglyMeasurable
  · -- Domination: ‖g ε x * f x‖ ≤ bound x for ε near 0
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds one_pos),
      self_mem_nhdsWithin] with ε hε1 hε_pos
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hbound ε (Set.mem_Ioi.mp hε_pos) (le_of_lt (Set.mem_Iio.mp hε1)) x)
      (norm_nonneg _)
  · -- Integrability of bound
    -- C * (1+‖x‖)^N * ‖f x‖ is integrable: poly × Schwartz
    have h_norm_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => ‖f x‖) := by
      simpa only [pow_zero, one_mul] using
        (f.integrable_pow_mul MeasureTheory.MeasureSpace.volume 0)
    have h_pow_int : MeasureTheory.Integrable
        (fun x : Fin m → ℝ => ‖x‖ ^ N * ‖f x‖) :=
      f.integrable_pow_mul MeasureTheory.MeasureSpace.volume N
    have h_sum : MeasureTheory.Integrable
        (fun x : Fin m → ℝ => (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖)) :=
      (h_norm_int.add h_pow_int).const_mul _
    have h_bound :
        ∀ x : Fin m → ℝ,
          ‖(1 + ‖x‖) ^ N * ‖f x‖‖ ≤
            (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by
      intro x
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) N) (norm_nonneg _))]
      have h1 : (1 + ‖x‖) ^ N ≤ (2 : ℝ) ^ N * (1 + ‖x‖ ^ N) := by
        calc
          (1 + ‖x‖) ^ N ≤ (2 * max 1 ‖x‖) ^ N := by
            apply pow_le_pow_left₀ (by positivity)
            calc
              1 + ‖x‖ ≤ max 1 ‖x‖ + max 1 ‖x‖ :=
                add_le_add (le_max_left 1 ‖x‖) (le_max_right 1 ‖x‖)
              _ = 2 * max 1 ‖x‖ := by ring
          _ = 2 ^ N * (max 1 ‖x‖) ^ N := by rw [mul_pow]
          _ ≤ 2 ^ N * (1 + ‖x‖ ^ N) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              by_cases h : (1 : ℝ) ≤ ‖x‖
              · simp [max_eq_right h]
              · push_neg at h
                simp [max_eq_left h.le]
      calc
        (1 + ‖x‖) ^ N * ‖f x‖ ≤ (2 : ℝ) ^ N * (1 + ‖x‖ ^ N) * ‖f x‖ := by
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by ring
    have h_poly_int : MeasureTheory.Integrable
        (fun x : Fin m → ℝ => (1 + ‖x‖) ^ N * ‖f x‖) := by
      exact h_sum.mono'
        ((((continuous_const.add continuous_norm).pow N).mul f.continuous.norm).aestronglyMeasurable)
        (Filter.Eventually.of_forall h_bound)
    exact (h_poly_int.const_mul C_bd).congr <| ae_of_all _ fun x => by
      ring
  · -- Pointwise convergence
    filter_upwards with x
    exact (hconv x).mul_const (f x)
-- **Axiom: Fourier-Laplace boundary value recovery.**
--
-- The distributional boundary value of the Fourier-Laplace extension F(z) = T(ψ_z)
-- recovers T composed with the physics-convention Fourier transform:
--   ∫ F(x+i��η) f(x) dx → T(FT_phys(f))  as ε→0⁺
--
-- This is the boundary-value half of the Fourier-Laplace representation theorem.
-- It combines:
-- (a) The Vladimirov growth bound on F (proved in this file)
-- (b) The Cauchy regularization for distributional BV existence
-- (c) The identification of the BV limit via the Fourier support of T
--
-- Reference: Vladimirov, "Methods of Generalized Functions", Thm 25.5;
--   Streater-Wightman, Thm 2-9.
theorem fourierLaplace_boundaryValue_recovery {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (hC_ne : C.Nonempty)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT_support : HasFourierSupportInDualCone C T)
    (η : Fin m → ℝ) (hη : η ∈ C)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : Fin m → ℝ,
        fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
          (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) *
        f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (T (physicsFourierFlatCLM f))) := by
  -- ══════════════════════════════════════════════════════════════════════
  -- Proof outline (Vladimirov, Thm 25.5):
  --
  -- Step A. For each ε > 0, define g_ε : x ↦ multiDimPsiZExt C ... (x + iεη).
  --   Since x + iεη ∈ tube T(C), we have F(x+iεη) = T(g_ε(x)).
  --   Apply schwartz_clm_fubini_exchange to get Φ_ε with
  --     T(Φ_ε) = ∫ T(g_ε(x)) f(x) dx = ∫ F(x+iεη) f(x) dx.
  --
  -- Step B. Show T(Φ_ε) → T(physicsFourierFlatCLM f) as ε→0⁺.
  --   Pointwise: Φ_ε(ξ) = χ(ξ) exp(-εη·ξ) FT_phys(f)(ξ) → χ(ξ) FT_phys(f)(ξ).
  --   Since T has Fourier support in C* and χ = 1 on C*,
  --   T(χ · FT_phys(f)) = T(FT_phys(f)).
  --
  -- Step C. Combine A + B via scalar_dct_schwartz_pairing.
  -- ══════════════════════════════════════════════════════════════════════
  -- Step A: Rewrite the integrand using T(ψ_{x+iεη}).
  -- For each ε > 0, x + iεη lies in the tube by cone scaling.
  -- F(x+iεη) = T(multiDimPsiZExt C ... (x+iεη)) by fourierLaplaceExtMultiDim_eq_ext.
  --
  -- Apply scalar_dct_schwartz_pairing with:
  --   g ε x := F(x+iεη) = T(multiDimPsiZExt C ... (x+iεη))
  --   L x   := T(physicsFourierFlatCLM f ← evaluated at x) ... [limit of g ε x]
  --
  -- However, the pointwise limit of F(x+iεη) as ε→0+ does NOT exist in general
  -- (distributional BV, not pointwise). So we cannot use scalar_dct_schwartz_pairing
  -- directly on the F(x+iεη) integrand.
  --
  -- Instead, the correct route uses the Fubini exchange at each ε to rewrite
  -- the integral as T(Φ_ε), then takes the limit in Schwartz space.
  --
  -- For each ε > 0, define the Schwartz-valued family:
  --   g_ε : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ
  --   g_ε(x) := multiDimPsiZExt C ... (fun i => (x i : ℂ) + ε * (η i : ℂ) * I)
  --
  -- Step A: Apply schwartz_clm_fubini_exchange for each ε > 0.
  -- This gives Φ_ε : SchwartzMap with T(Φ_ε) = ∫ T(g_ε(x)) f(x) dx
  --                                           = ∫ F(x+iεη) f(x) dx.
  --
  -- The hypotheses of schwartz_clm_fubini_exchange are:
  --   hg_cont: x ↦ g_ε(x) is continuous into Schwartz space
  --     (from multiDimPsiZ_seminorm_continuous + affine embedding into tube)
  --   hg_bound: seminorm k n (g_ε(x)) ≤ C * (1 + ‖x‖)^N
  --     (from multiDimPsiZDynamic_seminorm_bound, since Im(x+iεη) = εη ∈ C
  --      gives bounded infDist term, and ‖x+iεη‖ ≤ ‖x‖ + ε‖η‖)
  --
  -- Step B: T(Φ_ε) → T(physicsFourierFlatCLM f) as ε → 0⁺.
  --   Φ_ε → physicsFourierFlatCLM f in Schwartz topology, then T.continuous
  --   gives the limit. The Schwartz convergence follows from the damping factor
  --   exp(-εη·ξ) → 1 with all derivatives controlled by Schwartz decay of FT(f).
  --
  -- ── Implementation ──
  -- We suffice to show: for each ε > 0 near 0, the integral equals T(Φ_ε)
  -- for some Schwartz Φ_ε, and T(Φ_ε) → T(physicsFourierFlatCLM f).
  --
  -- The Fubini exchange (Step A) and the Schwartz-topology limit (Step B) are
  -- both nontrivial. We factor them as separate sorries with clear labels.
  -- ──────────────────────────────────────────────────────────────────────
  -- Auxiliary: for each ε > 0, define the Schwartz-valued family g_ε
  let g : ℝ → (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ := fun ε x =>
    multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
      (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I)
  -- Key rewriting: F(x+iεη) = T(g ε x) for ε > 0
  have hF_eq : ∀ (ε : ℝ), 0 < ε → ∀ (x : Fin m → ℝ),
      fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
        (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) = T (g ε x) := by
    intro ε _hε x
    exact fourierLaplaceExtMultiDim_eq_ext C hC_open hC_conv hC_cone hC_salient T
      (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I)
  -- Step A: For each ε > 0, apply schwartz_clm_fubini_exchange to get Φ_ε
  -- with ∫ T(g_ε(x)) f(x) dx = T(Φ_ε).
  --
  -- hg_cont: The map x ↦ g ε x = multiDimPsiZExt(x+iεη) is continuous
  -- into Schwartz space. This follows from:
  --   (1) The affine map x ↦ x+iεη is continuous ℝᵐ → ℂᵐ
  --   (2) For ε > 0, x+iεη ∈ tube, so multiDimPsiZExt = multiDimPsiZ
  --   (3) z ↦ multiDimPsiZ(z) is continuous on the tube in Schwartz topology
  --       (multiDimPsiZ_seminorm_continuous)
  --
  -- hg_bound: seminorm k n (g ε x) ≤ C * (1+‖x‖)^N from
  -- multiDimPsiZDynamic_seminorm_bound, noting Im(x+iεη) = εη has fixed
  -- distance from ∂C (since εη ∈ C with η fixed), so the infDist factor
  -- is bounded by a constant depending on ε, η.
  have hFubini : ∀ (ε : ℝ), 0 < ε →
      ∃ (Φ_ε : SchwartzMap (Fin m → ℝ) ℂ),
        (∀ ξ, Φ_ε ξ = ∫ x, g ε x ξ * f x) ∧
        (T Φ_ε = ∫ x, T (g ε x) * f x) := by
    intro ε hε
    apply schwartz_clm_fubini_exchange T (g ε) f
    · -- hg_cont: continuity of x ↦ multiDimPsiZExt(x + iεη) in Schwartz topology
      -- Proof: compose the continuous affine embedding x ↦ x+iεη (landing in tube)
      -- with the Schwartz-continuous map z ↦ multiDimPsiZ(z) on the tube.
      -- Factor as g_ε = ψ ∘ ι where:
      --   ι : ℝᵐ → TubeDomain(C), x ↦ ⟨x+iεη, ...⟩  (continuous affine)
      --   ψ : TubeDomain(C) → 𝓢(ℝᵐ,ℂ), z ↦ multiDimPsiZ(z)  (continuous)
      let ψ : SCV.TubeDomain C → SchwartzMap (Fin m → ℝ) ℂ :=
        fun z => multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z.1 z.2
      -- ψ is continuous (same proof as in fourierLaplaceExtMultiDim_continuousOn)
      have hψ_cont : Continuous ψ := by
        rw [continuous_iff_continuousAt]
        intro z
        rw [ContinuousAt]
        exact ((schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds ψ (ψ z)).2 <| by
          intro p ε' hε'
          obtain ⟨δ, hδ_pos, hδ⟩ :=
            multiDimPsiZ_seminorm_continuous C hC_open hC_conv hC_cone hC_salient
              p.1 p.2 z.1 z.2 ε' hε'
          filter_upwards [Metric.ball_mem_nhds z hδ_pos] with w hw
          exact hδ w.1 w.2 (by
            have : dist (w : Fin m → ℂ) (z : Fin m → ℂ) =
              ‖(w : Fin m → ℂ) - (z : Fin m → ℂ)‖ := dist_eq_norm _ _
            have hwd : dist (w : Fin m → ℂ) (z : Fin m → ℂ) < δ := hw
            linarith)
      -- ι : ℝᵐ → TubeDomain(C) is the affine embedding x ↦ ⟨x + iεη, ...⟩
      let ι : (Fin m → ℝ) → SCV.TubeDomain C := fun x =>
        ⟨fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I,
         realPlusIEpsEta_mem_tubeDomain C hC_cone x η hη ε hε⟩
      -- ι is continuous (continuous affine map into ℂᵐ, landing in the open tube)
      have hι_cont : Continuous ι := by
        apply Continuous.subtype_mk
        apply continuous_pi; intro i
        exact (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const
      -- g ε = ψ ∘ ι (since x+iεη ∈ tube, multiDimPsiZExt = multiDimPsiZ)
      have hg_eq : g ε = ψ ∘ ι := by
        funext x
        show multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
            (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) =
          multiDimPsiZ C hC_open hC_conv hC_cone hC_salient (ι x).1 (ι x).2
        exact multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient
          (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I)
          (realPlusIEpsEta_mem_tubeDomain C hC_cone x η hη ε hε)
      rw [hg_eq]
      exact hψ_cont.comp hι_cont
    · -- hg_bound: polynomial seminorm growth of g_ε(x) in x
      -- For fixed ε > 0, η ∈ C, z = x + iεη has Im(z) = εη (constant).
      -- Coercivity of εη gives c₀ > 0, and the bound from
      -- schwartz_seminorm_cutoff_exp_bound_affine_uniform yields
      -- seminorm k n (g ε x) ≤ Bexp * (1 + ‖L_z‖)^n ≤ C_ε * (1+‖x‖)^n.
      intro k n
      -- Setup: canonical cutoff and coercivity for εη ∈ C
      let χ : FixedConeCutoff (DualConeFlat C) :=
        (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
      let y₀ : Fin m → ℝ := ε • η
      have hy₀ : y₀ ∈ C := hC_cone η hη ε hε
      have hC_star_ne : (DualConeFlat C).Nonempty := ⟨0, zero_mem_dualConeFlat C⟩
      have hC_star_closed : IsClosed (DualConeFlat C) := dualConeFlat_closed C
      obtain ⟨c₀, hc₀_pos, hc₀⟩ :=
        dualConeFlat_coercivity hC_open hC_cone hy₀ hC_star_ne hC_star_closed
      let K : ℝ := ((Fintype.card (Fin m) : ℝ) ^ 2)
      let A₀ : ℝ := c₀ + K * ε * ‖η‖
      obtain ⟨Bexp, hBexp_pos, hBexp⟩ :=
        schwartz_seminorm_cutoff_exp_bound_affine_uniform
          χ.val χ.smooth χ.deriv_bound A₀ c₀ hc₀_pos k n
      -- Constant absorbing the fixed ε‖η‖ contribution
      let mR : ℝ := (Fintype.card (Fin m) : ℝ)
      let C_poly : ℝ := 1 + mR * ε * ‖η‖ + mR
      have hmR_nn : (0 : ℝ) ≤ mR := Nat.cast_nonneg (Fintype.card (Fin m))
      have hC_poly_pos : 0 < C_poly := by
        dsimp [C_poly]
        linarith [mul_nonneg (mul_nonneg hmR_nn hε.le) (norm_nonneg η)]
      refine ⟨Bexp * C_poly ^ n, n, mul_pos hBexp_pos (pow_pos hC_poly_pos n), ?_⟩
      intro x
      -- z = x + iεη lies in the tube
      let z : Fin m → ℂ := fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I
      have hz : z ∈ SCV.TubeDomain C :=
        realPlusIEpsEta_mem_tubeDomain C hC_cone x η hη ε hε
      -- g ε x = multiDimPsiZ at z
      have hg_eq_psiZ :
          g ε x = multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz := by
        show multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z =
          multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz
        exact multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient z hz
      rw [hg_eq_psiZ]
      -- Im(z) = εη = y₀, so coercivity of y₀ applies directly
      have hy_eq : (fun i => (z i).im) = y₀ := by
        ext i
        simp [z, y₀, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
      have hc_z : ∀ ξ ∈ DualConeFlat C, ∑ i, (fun i => (z i).im) i * ξ i ≥ c₀ * ‖ξ‖ := by
        rw [hy_eq]; exact hc₀
      -- Exponential decay condition for multiDimPsiExpCLM z
      have hexp_decay : ∀ ξ : Fin m → ℝ, χ.val ξ ≠ 0 →
          (multiDimPsiExpCLM z ξ).re ≤ A₀ - c₀ * ‖ξ‖ := by
        intro ξ hχξ
        have hdistχ : Metric.infDist ξ (DualConeFlat C) ≤ 1 := by
          by_contra h
          exact hχξ (χ.support_bound ξ (by linarith))
        have hExpBound :
            ‖cexp (multiDimPsiExpCLM z ξ)‖ ≤
              Real.exp A₀ * Real.exp (-(c₀ * ‖ξ‖)) := by
          calc
            ‖cexp (multiDimPsiExpCLM z ξ)‖
                = ‖cexp (I * ∑ i, z i * (ξ i : ℂ))‖ := by
                    rw [multiDimPsiExpCLM_apply]
            _ ≤ Real.exp (((c₀ + K * ‖fun i => (z i).im‖)) * 1) *
                  Real.exp (-(c₀ * ‖ξ‖)) := by
                    exact cexp_bound_on_support hC_open hC_cone hz hc₀_pos hc_z
                      zero_lt_one ξ hdistχ
            _ ≤ Real.exp A₀ * Real.exp (-(c₀ * ‖ξ‖)) := by
              gcongr
              rw [mul_one]
              show c₀ + K * ‖fun i => (z i).im‖ ≤ A₀
              rw [hy_eq]; dsimp [y₀, A₀]
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]; ring_nf; exact le_refl _
        have hnormexp :
            ‖cexp (multiDimPsiExpCLM z ξ)‖ =
              Real.exp ((multiDimPsiExpCLM z ξ).re) := Complex.norm_exp _
        have hExp' :
            Real.exp ((multiDimPsiExpCLM z ξ).re) ≤ Real.exp (A₀ - c₀ * ‖ξ‖) := by
          rw [← hnormexp]
          simpa [sub_eq_add_neg, Real.exp_add] using hExpBound
        exact Real.exp_le_exp.mp hExp'
      -- Pointwise bound from schwartz_seminorm_cutoff_exp_bound_affine_uniform
      have hpoint : ∀ ξ : Fin m → ℝ,
          ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n
              (fun ξ => (χ.val ξ : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))) ξ‖ ≤
            Bexp * (1 + ‖multiDimPsiExpCLM z‖) ^ n := by
        intro ξ
        have hraw := hBexp (multiDimPsiExpCLM z) hexp_decay ξ
        have hfunexp :
            (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))) =
              (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ) * cexp (multiDimPsiExpCLM z ξ)) := by
          funext ξ; rw [multiDimPsiExpCLM_apply]
        rw [hfunexp]; exact hraw
      -- Convert pointwise bound to SchwartzMap.seminorm bound
      have hcoe :
          ⇑(multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) = psiZRaw χ 1 z := rfl
      have hrawfun :
          psiZRaw χ 1 z =
            (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))) := by
        funext ξ; simp [psiZRaw]
      have hpoint' : ∀ ξ : Fin m → ℝ,
          ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n
              (⇑(multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)) ξ‖ ≤
            Bexp * (1 + ‖multiDimPsiExpCLM z‖) ^ n := by
        intro ξ; rw [hcoe, hrawfun]; exact hpoint ξ
      have hMnn : (0 : ℝ) ≤ Bexp * (1 + ‖multiDimPsiExpCLM z‖) ^ n := by
        apply mul_nonneg hBexp_pos.le
        exact pow_nonneg (by linarith [norm_nonneg (multiDimPsiExpCLM z)]) _
      have hseminorm :
          SchwartzMap.seminorm ℝ k n
            (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz) ≤
            Bexp * (1 + ‖multiDimPsiExpCLM z‖) ^ n :=
        SchwartzMap.seminorm_le_bound ℝ k n _ hMnn hpoint'
      -- Bound ‖multiDimPsiExpCLM z‖ ≤ mR * (‖x‖ + ε * ‖η‖)
      -- Componentwise: ‖z_i‖ = ‖x_i + iεη_i‖ ≤ |x_i| + ε|η_i| ≤ ‖x‖ + ε‖η‖
      have hz_norm : ‖z‖ ≤ ‖x‖ + ε * ‖η‖ := by
        have hnn : (0 : ℝ) ≤ ‖x‖ + ε * ‖η‖ := by positivity
        apply (pi_norm_le_iff_of_nonneg hnn).2
        intro i
        calc ‖z i‖ = ‖(x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I‖ := rfl
          _ ≤ ‖(x i : ℂ)‖ + ‖(ε : ℂ) * (η i : ℂ) * I‖ := norm_add_le _ _
          _ = |x i| + ε * |η i| := by
              congr 1
              · exact Complex.norm_real (x i)
              · rw [show (ε : ℂ) * (η i : ℂ) * I = ((ε * η i : ℝ) : ℂ) * I from by push_cast; ring]
                rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
                  Real.norm_eq_abs, abs_mul, abs_of_pos hε]
          _ ≤ ‖x‖ + ε * ‖η‖ := by
              gcongr
              · exact norm_le_pi_norm x i
              · exact norm_le_pi_norm η i
      have hL_bound : ‖multiDimPsiExpCLM z‖ ≤ mR * (‖x‖ + ε * ‖η‖) := by
        calc ‖multiDimPsiExpCLM z‖ ≤ mR * ‖z‖ := multiDimPsiExpCLM_norm_le z
          _ ≤ mR * (‖x‖ + ε * ‖η‖) := by
            apply mul_le_mul_of_nonneg_left hz_norm (Nat.cast_nonneg' _)
      -- Polynomial absorption: (1 + ‖L_z‖)^n ≤ C_poly^n * (1+‖x‖)^n
      -- Key: 1 + a + b ≤ (1+a+b_coeff)*(1+t) when a,b_coeff constant, b = b_coeff*t.
      have hpoly_absorb :
          (1 + ‖multiDimPsiExpCLM z‖) ^ n ≤ C_poly ^ n * (1 + ‖x‖) ^ n := by
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by linarith [norm_nonneg (multiDimPsiExpCLM z)])
        have hmR_nn : (0 : ℝ) ≤ mR := Nat.cast_nonneg' _
        -- 1 + mR*ε*‖η‖ + mR*‖x‖ ≤ C_poly*(1+‖x‖) since
        --   1 + mR*ε*‖η‖ ≤ C_poly and mR*‖x‖ ≤ C_poly*‖x‖
        calc 1 + ‖multiDimPsiExpCLM z‖
            ≤ 1 + mR * (‖x‖ + ε * ‖η‖) := by linarith [hL_bound]
          _ = 1 + mR * ε * ‖η‖ + mR * ‖x‖ := by ring
          _ ≤ C_poly * 1 + C_poly * ‖x‖ := by
              apply add_le_add
              · -- 1 + mR*ε*‖η‖ ≤ C_poly * 1
                simp only [mul_one]; dsimp [C_poly]; linarith
              · -- mR * ‖x‖ ≤ C_poly * ‖x‖
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                show mR ≤ 1 + mR * ε * ‖η‖ + mR
                have : 0 ≤ mR * ε * ‖η‖ := by positivity
                linarith
          _ = C_poly * (1 + ‖x‖) := by ring
      calc SchwartzMap.seminorm ℝ k n
              (multiDimPsiZ C hC_open hC_conv hC_cone hC_salient z hz)
          ≤ Bexp * (1 + ‖multiDimPsiExpCLM z‖) ^ n := hseminorm
        _ ≤ Bexp * (C_poly ^ n * (1 + ‖x‖) ^ n) := by
            gcongr
        _ = (Bexp * C_poly ^ n) * (1 + ‖x‖) ^ n := by ring
  -- Step B: Extract Φ_ε and show the limit T(Φ_ε) → T(physicsFourierFlatCLM f).
  --
  -- For ε > 0 sufficiently small, hFubini gives Φ_ε with
  --   T(Φ_ε) = ∫ T(g ε x) f(x) dx = ∫ F(x+iεη) f(x) dx.
  -- So the original sequence equals T(Φ_ε) eventually.
  -- Then: Φ_ε → physicsFourierFlatCLM f in Schwartz topology as ε→0⁺,
  -- and T.continuous gives T(Φ_ε) → T(physicsFourierFlatCLM f).
  --
  -- The Schwartz convergence Φ_ε → physicsFourierFlatCLM f is the damping limit:
  --   Φ_ε(ξ) = χ(ξ) exp(-εη·ξ) FT_phys(f)(ξ) → χ(ξ) FT_phys(f)(ξ)
  -- with χ = 1 on DualConeFlat C, so T(χ · FT_phys(f)) = T(FT_phys(f))
  -- by HasFourierSupportInDualCone.
  --
  -- Rewrite the integral using the Fubini exchange.
  -- First: the original integral equals T(Φ_ε) for each ε > 0.
  suffices h : Filter.Tendsto
      (fun ε : ℝ => ∫ x : Fin m → ℝ, T (g ε x) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (T (physicsFourierFlatCLM f))) by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_pos : 0 < ε := Set.mem_Ioi.mp hε
    congr 1; ext x
    exact congr_arg (· * f x) (hF_eq ε hε_pos x).symm
  -- Now: ∫ T(g ε x) f(x) dx = T(Φ_ε) by Fubini, and T(Φ_ε) → T(physicsFourierFlatCLM f).
  -- Use the Fubini exchange to rewrite the integral, then take the limit.
  --
  -- For each ε > 0, choose Φ_ε via hFubini.
  -- Use Classical.choose to extract a definite Schwartz function for each ε > 0.
  -- The limit T(Φ_ε) → T(physicsFourierFlatCLM f) follows from:
  --   (1) Φ_ε → physicsFourierFlatCLM f in Schwartz topology (damping limit)
  --   (2) T is continuous: T(Φ_ε) → T(physicsFourierFlatCLM f)
  --
  -- Step B1: Schwartz-topology limit Φ_ε → physicsFourierFlatCLM f.
  --
  -- Pointwise: Φ_ε(ξ) = χ(ξ) exp(-εη·ξ) FT_phys(f)(ξ), so
  --   Φ_ε(ξ) - (physicsFourierFlatCLM f)(ξ) = χ(ξ)(exp(-εη·ξ) - 1)FT_phys(f)(ξ)
  --     + (χ(ξ) - 1)(physicsFourierFlatCLM f)(ξ)
  -- The second term is constant in ε and killed by T (Fourier support in C*
  -- via fixedConeCutoff_eq_one_on_dualCone), and the first → 0
  -- in Schwartz topology by dominated convergence (exp(-εη·ξ) → 1 uniformly
  -- on compacts, with Schwartz decay dominator from FT_phys(f)).
  --
  -- Step B2: T.continuous passes the limit: T(Φ_ε) → T(physicsFourierFlatCLM f).
  --
  -- These two steps together with the Fubini rewriting close the proof.
  -- The Schwartz damping limit (B1) is the core analytical content.
  -- We isolate it as a single sorry with a precise mathematical statement.
  --
  -- Choose Φ_ε for each ε > 0 and rewrite the integral.
  -- Extract a definite choice function Φ_ε for ε > 0 via Classical.choose.
  let Φ : ℝ → SchwartzMap (Fin m → ℝ) ℂ := fun ε =>
    if hε : 0 < ε then (hFubini ε hε).choose else 0
  have hΦ_pointwise : ∀ (ε : ℝ) (hε : 0 < ε) (ξ : Fin m → ℝ),
      Φ ε ξ = ∫ x, g ε x ξ * f x := by
    intro ε hε ξ
    simp only [Φ, dif_pos hε]
    exact (hFubini ε hε).choose_spec.1 ξ
  have hΦ_eq : ∀ (ε : ℝ) (hε : 0 < ε),
      T (Φ ε) = ∫ x, T (g ε x) * f x := by
    intro ε hε
    simp only [Φ, dif_pos hε]
    exact (hFubini ε hε).choose_spec.2
  -- Rewrite: ∫ T(g ε x) f(x) dx = T(Φ_ε) for ε > 0.
  -- Suffice: T(Φ_ε) → T(physicsFourierFlatCLM f).
  suffices hTΦ_lim : Filter.Tendsto (fun ε => T (Φ ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (T (physicsFourierFlatCLM f))) by
    apply hTΦ_lim.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hΦ_eq ε (Set.mem_Ioi.mp hε)
  let χ : FixedConeCutoff (DualConeFlat C) := dualConeCutoff C
  have hχ_temp : (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ)).HasTemperateGrowth := by
    simpa [χ, dualConeCutoff] using
      (dualConeCutoff_hasTemperateGrowthComplex (C := C))
  let hχf : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ))
      (physicsFourierFlatCLM f)
  let Lη : (Fin m → ℝ) →L[ℝ] ℝ := etaPairingCLM η
  have hsupp_Lη : ∃ M : ℝ, ∀ ξ, ξ ∈ Function.support (⇑hχf) → -M ≤ Lη ξ := by
    -- The cutoff χ vanishes outside the 1-neighborhood of DualConeFlat C.
    -- On that set, η ∈ C gives ⟨η, ξ⟩ ≥ -‖η‖ (since dist(ξ, C*) ≤ 1 and
    -- ⟨η, ξ'⟩ ≥ 0 for ξ' ∈ C*).
    refine ⟨2 * ‖Lη‖, fun ξ hξ_supp => ?_⟩
    -- Step 1: hχf ξ ≠ 0, so χ.val ξ ≠ 0
    have hχξ_ne : (χ.val ξ : ℂ) ≠ 0 := by
      intro hχξ_zero
      apply Function.mem_support.mp hξ_supp
      show hχf ξ = 0
      dsimp [hχf]
      rw [SchwartzMap.smulLeftCLM_apply_apply hχ_temp, hχξ_zero, zero_smul]
    -- Step 2: χ.val ξ ≠ 0 implies infDist ξ (DualConeFlat C) ≤ 1
    have hdist : Metric.infDist ξ (DualConeFlat C) ≤ 1 := by
      by_contra h
      push_neg at h
      have := χ.support_bound ξ (by linarith)
      exact hχξ_ne (by simp [this])
    -- Step 3: Find ξ' ∈ DualConeFlat C with dist ξ ξ' < 2
    have hne : (DualConeFlat C).Nonempty := ⟨0, zero_mem_dualConeFlat C⟩
    have hlt : Metric.infDist ξ (DualConeFlat C) < 2 := by linarith
    obtain ⟨ξ', hξ'_mem, hξ'_dist⟩ := (Metric.infDist_lt_iff hne).mp hlt
    -- Step 4: Lη ξ = Lη ξ' + Lη (ξ - ξ') ≥ 0 - 2‖Lη‖
    have hLη_ξ' : 0 ≤ Lη ξ' := by
      simp only [Lη, etaPairingCLM_apply]
      exact (mem_dualConeFlat.mp hξ'_mem) η hη
    have hLη_diff : -Lη (ξ - ξ') ≤ ‖Lη‖ * ‖ξ - ξ'‖ := by
      have := Lη.le_opNorm (ξ - ξ')
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (Lη (ξ - ξ')), neg_abs_le (Lη (ξ - ξ'))]
    have hLη_linear : Lη ξ = Lη ξ' + Lη (ξ - ξ') := by
      rw [map_sub]; ring
    have hdist_norm : ‖ξ - ξ'‖ < 2 := by
      rwa [dist_eq_norm] at hξ'_dist
    have hLη_bound : ‖Lη‖ * ‖ξ - ξ'‖ ≤ 2 * ‖Lη‖ := by
      have : ‖ξ - ξ'‖ ≤ 2 := le_of_lt hdist_norm
      calc ‖Lη‖ * ‖ξ - ξ'‖ ≤ ‖Lη‖ * 2 := by gcongr
        _ = 2 * ‖Lη‖ := by ring
    linarith
  obtain ⟨hε, hhε_apply, hhε_tendsto⟩ := schwartz_exp_damping_tendsto hχf Lη hsupp_Lη
  have hΦ_eq_hε : ∀ (ε : ℝ) (hε_pos : 0 < ε), Φ ε = hε ε := by
    intro ε hε_pos
    ext ξ
    rw [hΦ_pointwise ε hε_pos ξ]
    rw [regularizedKernel_pointwise C hC_open hC_conv hC_cone hC_salient η hη f ε hε_pos ξ]
    rw [hhε_apply ε hε_pos ξ]
    have hhχf :
        hχf ξ = (((dualConeCutoff C).val ξ : ℂ) * physicsFourierFlatCLM f ξ) := by
      dsimp [hχf, χ]
      rw [SchwartzMap.smulLeftCLM_apply_apply
        (dualConeCutoff_hasTemperateGrowthComplex (C := C))]
      simp [smul_eq_mul]
    simp only [Lη, etaPairingCLM_apply]
    rw [hhχf]
  have hThχf_eq : T hχf = T (physicsFourierFlatCLM f) := by
    apply hasFourierSupportIn_eqOn hT_support
    intro ξ hξ
    rw [show hχf =
        SchwartzMap.smulLeftCLM ℂ (fun ξ : Fin m → ℝ => (χ.val ξ : ℂ))
          (physicsFourierFlatCLM f) from rfl]
    rw [SchwartzMap.smulLeftCLM_apply_apply hχ_temp]
    simp [smul_eq_mul, fixedConeCutoff_eq_one_on_dualCone χ hξ]
  have hT_hε_tendsto : Filter.Tendsto (fun ε : ℝ => T (hε ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (T hχf)) := by
    exact T.continuous.continuousAt.tendsto.comp hhε_tendsto
  have hTΦ_lim_to_cutoff : Filter.Tendsto (fun ε : ℝ => T (Φ ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (T hχf)) := by
    refine hT_hε_tendsto.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε_mem
    rw [hΦ_eq_hε ε (Set.mem_Ioi.mp hε_mem)]
  simpa [hThχf_eq] using hTΦ_lim_to_cutoff

theorem fourierLaplaceExtMultiDim_boundaryValue
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (hC_ne : C.Nonempty)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT_support : HasFourierSupportInDualCone C T) :
    ∀ (η : Fin m → ℝ), η ∈ C →
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin m → ℝ,
            fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
              (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) *
            f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T (physicsFourierFlatCLM f))) := by
  intro η hη f
  -- The boundary value is distributional, not pointwise.
  -- F(x+iεη) may blow up as ε→0+ (the ε⁻ᴹ factor from Vladimirov growth).
  -- The convergence ∫ F(x+iεη) f(x) dx → W(f) holds for each test function f
  -- but NOT pointwise in x.
  --
  -- Apply the Fourier-Laplace BV recovery axiom below.
  exact fourierLaplace_boundaryValue_recovery C hC_open hC_conv hC_cone hC_salient hC_ne
    T hT_support η hη f

end
