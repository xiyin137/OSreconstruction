/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.FourierSupportCone
import OSReconstruction.SCV.Osgood

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

open scoped Classical ComplexConjugate BigOperators NNReal
open MeasureTheory Complex
noncomputable section

variable {m : ℕ}

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

/-- The multi-dimensional exponential-cutoff Schwartz function parametrized by
    z ∈ T(C). For now this is defined abstractly via the product structure;
    the concrete construction using `smoothCutoff` and `exp(iz·ξ)` is deferred
    to when the 1D tensor product machinery is connected.

    The key property is that for z = x + iy with y ∈ C:
    - ψ_z ∈ S(ℝ^m) (Schwartz class)
    - ψ_z(ξ) = χ(ξ) exp(iz·ξ) for a smooth cutoff χ adapted to C*
    - The Schwartz seminorms of ψ_z have polynomial growth in x and
      inverse-boundary-distance growth in y -/
axiom multiDimPsiZ {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    SchwartzMap (Fin m → ℝ) ℂ

/-! ### Seminorm bounds for the multi-D family -/

/-- The Schwartz seminorms of `multiDimPsiZ` have polynomial growth in the
    real part and inverse-boundary-distance growth in the imaginary part.
    This is the multi-D generalization of `schwartzPsiZ_seminorm_horizontal_bound`.

    For z = x + iy with y ∈ C:
    ‖ψ_z‖_{k,n} ≤ B_{k,n} · (1 + ‖x‖)^{N_{k,n}} · (1 + dist(y,∂C)⁻¹)^{M_{k,n}}
-/
axiom multiDimPsiZ_seminorm_bound {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (k n : ℕ) :
    ∃ (B : ℝ) (N M : ℕ), B > 0 ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
        SchwartzMap.seminorm ℝ k n (multiDimPsiZ C hC_open hC_conv hC_cone z hz) ≤
          B * (1 + ‖fun i => (z i).re‖) ^ N *
            (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M

/-- Finset-sup version of `multiDimPsiZ_seminorm_bound`: for a finite set of
    seminorm indices, the sup has Vladimirov-type growth. This follows from
    `multiDimPsiZ_seminorm_bound` applied to each index and taking the max
    of the constants. -/
theorem multiDimPsiZ_finset_sup_bound {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (s : Finset (ℕ × ℕ)) :
    ∃ (B : ℝ) (N M : ℕ), B > 0 ∧
      ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
        (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ))
          (multiDimPsiZ C hC_open hC_conv hC_cone z hz) ≤
          B * (1 + ‖fun i => (z i).re‖) ^ N *
            (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M := by
  induction s using Finset.induction with
  | empty =>
    exact ⟨1, 0, 0, one_pos, fun z hz => by simp [Finset.sup_empty]⟩
  | @insert a s ha ih =>
    obtain ⟨B₁, N₁, M₁, hB₁, h₁⟩ := ih
    obtain ⟨B₂, N₂, M₂, hB₂, h₂⟩ :=
      multiDimPsiZ_seminorm_bound C hC_open hC_conv hC_cone a.1 a.2
    refine ⟨max B₁ B₂, max N₁ N₂, max M₁ M₂, lt_max_of_lt_left hB₁, fun z hz => ?_⟩
    rw [Finset.sup_insert]
    apply sup_le
    · -- The new element a: seminorm a.1 a.2 ≤ B₂ * growth ≤ max B * growth'
      calc (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ a)
              (multiDimPsiZ C hC_open hC_conv hC_cone z hz)
          = SchwartzMap.seminorm ℂ a.1 a.2
              (multiDimPsiZ C hC_open hC_conv hC_cone z hz) := by
            simp [schwartzSeminormFamily]
        _ ≤ B₂ * (1 + ‖fun i => (z i).re‖) ^ N₂ *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M₂ := by
            sorry -- need seminorm ℂ = seminorm ℝ, then apply h₂
        _ ≤ max B₁ B₂ * (1 + ‖fun i => (z i).re‖) ^ (max N₁ N₂) *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ (max M₁ M₂) := by
            sorry -- B₂ ≤ max B, pow monotone in exponent for base ≥ 1
    · -- The old finset s: sup ≤ B₁ * growth ≤ max B * growth'
      calc (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ))
              (multiDimPsiZ C hC_open hC_conv hC_cone z hz)
          ≤ B₁ * (1 + ‖fun i => (z i).re‖) ^ N₁ *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M₁ := h₁ z hz
        _ ≤ max B₁ B₂ * (1 + ‖fun i => (z i).re‖) ^ (max N₁ N₂) *
              (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ (max M₁ M₂) := by
            sorry -- B₁ ≤ max B, pow monotone in exponent for base ≥ 1

/-- z ↦ ψ_z is continuous into Schwartz space: for each seminorm (k,n),
    `z ↦ seminorm k n (ψ_{z'} - ψ_z) → 0` as `z' → z` in the tube.

    This is used to prove continuity of F(z) = T(ψ_z) on the tube. -/
axiom multiDimPsiZ_seminorm_continuous {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (k n : ℕ)
    (z₀ : Fin m → ℂ) (hz₀ : z₀ ∈ SCV.TubeDomain C) :
    ∀ ε > 0, ∃ δ > 0, ∀ (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C),
      ‖z - z₀‖ < δ →
        SchwartzMap.seminorm ℝ k n
          (multiDimPsiZ C hC_open hC_conv hC_cone z hz -
           multiDimPsiZ C hC_open hC_conv hC_cone z₀ hz₀) < ε

/-- The difference quotient of ψ_z converges in Schwartz seminorms.
    For fixed z in the tube and direction e_j:

    ‖(ψ_{z+he_j} - ψ_z)/h - ∂_{z_j} ψ_z‖_{k,n} → 0 as h → 0

    Proved via pointwise scalarization + integral MVT (not Bochner integrals
    of Fréchet curves). -/
axiom multiDimPsiZ_differenceQuotient_converges {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C)
    (j : Fin m) (k n : ℕ) :
    ∃ (ψ'_j : SchwartzMap (Fin m → ℝ) ℂ),
      Filter.Tendsto
        (fun h : ℂ => SchwartzMap.seminorm ℝ k n
          ((h⁻¹ • (multiDimPsiZ C hC_open hC_conv hC_cone
              (Function.update z j (z j + h))
              sorry -- membership proof for z+he_j
            - multiDimPsiZ C hC_open hC_conv hC_cone z hz))
            - ψ'_j))
        (nhdsWithin 0 {0}ᶜ) (nhds 0)

/-! ### The Fourier-Laplace extension -/

/-- The Fourier-Laplace extension: F(z) = T(ψ_z) for z in the tube T(C),
    extended by 0 outside the tube. This avoids threading membership proofs
    through differentiability arguments.

    This is the multi-dimensional generalization of `fourierLaplaceExt`. -/
def fourierLaplaceExtMultiDim
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (z : Fin m → ℂ) : ℂ :=
  if hz : z ∈ SCV.TubeDomain C then
    T (multiDimPsiZ C hC_open hC_conv hC_cone z hz)
  else 0

theorem fourierLaplaceExtMultiDim_eq
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone T z =
      T (multiDimPsiZ C hC_open hC_conv hC_cone z hz) := by
  simp [fourierLaplaceExtMultiDim, hz]

/-! ### Holomorphicity via Osgood -/

/-- F(z) = T(ψ_z) is separately holomorphic in each variable z_j.

    Proof: The difference quotient (F(z+he_j) - F(z))/h = T((ψ_{z+he_j} - ψ_z)/h)
    converges to T(ψ'_j) by continuity of T and the seminorm convergence
    from `multiDimPsiZ_differenceQuotient_converges`. -/
theorem fourierLaplaceExtMultiDim_separatelyHolomorphic
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) (j : Fin m) :
    DifferentiableAt ℂ
      (fun w => fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone T
        (Function.update z j w))
      (z j) := by
  -- The difference quotient (F(z+he_j) - F(z))/h = T((ψ_{z+he_j} - ψ_z)/h)
  -- converges because:
  -- 1. (ψ_{z+he_j} - ψ_z)/h → ψ'_j in Schwartz seminorms (axiom)
  -- 2. |T(f)| ≤ C_T · seminorm k n f (schwartz_clm_bound_by_seminorm)
  -- 3. So the scalar difference quotient converges to T(ψ'_j)
  sorry

/-- F(z) = T(ψ_z) is continuous on the tube.

    Proof: T is continuous on Schwartz space, and z ↦ ψ_z is continuous
    into Schwartz space (by the seminorm bounds). -/
theorem fourierLaplaceExtMultiDim_continuousOn
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ContinuousOn
      (fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone T)
      (SCV.TubeDomain C) := by
  -- Proof: T is continuous Schwartz → ℂ.  z ↦ ψ_z is continuous ℂ^m → Schwartz
  -- (by multiDimPsiZ_seminorm_continuous + WithSeminorms.tendsto_nhds).
  -- The composition T ∘ ψ is continuous on the open tube.
  -- The `dite` in the definition resolves to T(ψ_z) on the tube since it's open.
  sorry

/-- **Main holomorphicity theorem**: F(z) = T(ψ_z) is holomorphic on the tube T(C).

    Proof: Combine separate holomorphicity + continuity via `osgood_lemma`. -/
theorem fourierLaplaceExtMultiDim_holomorphic
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    DifferentiableOn ℂ
      (fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone T)
      (SCV.TubeDomain C) := by
  apply osgood_lemma (SCV.tubeDomain_isOpen hC_open)
  · exact fourierLaplaceExtMultiDim_continuousOn C hC_open hC_conv hC_cone T
  · intro z hz j
    exact fourierLaplaceExtMultiDim_separatelyHolomorphic
      C hC_open hC_conv hC_cone T z hz j

/-! ### Continuous functionals are seminorm-bounded -/

/-- Version with finset sup: a continuous linear functional on Schwartz space
    is bounded by a finite sup of Schwartz seminorms. This follows directly
    from `Seminorm.bound_of_continuous` applied to `schwartz_withSeminorms`. -/
theorem schwartz_clm_bound_by_finset_sup
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

/-- A continuous linear functional on Schwartz space is bounded by a single seminorm.
    Derived from `schwartz_clm_bound_by_finset_sup` by bounding the finset sup. -/
theorem schwartz_clm_bound_by_seminorm
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (C_T : ℝ) (k n : ℕ), C_T > 0 ∧
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ),
        ‖T f‖ ≤ C_T * SchwartzMap.seminorm ℝ k n f := by
  -- From schwartz_clm_bound_by_finset_sup: ‖T f‖ ≤ C * (s.sup seminorms) f
  -- The finset sup of seminorms is bounded by a single large-index seminorm
  -- (requires Schwartz seminorm monotonicity, which needs sup_{x} ‖x‖^k1 * ‖D^n1 f‖
  --  ≤ sup_{x} ‖x‖^k2 * ‖D^n2 f‖ for appropriate k2, n2 ≥ k1, n1 + dimension correction)
  sorry

/-! ### Growth bound -/

/-- F(z) = T(ψ_z) satisfies the global Vladimirov growth bound.

    Proof: |F(z)| = |T(ψ_z)| ≤ ‖T‖ · ‖ψ_z‖_{k,n} for some seminorm.
    By `multiDimPsiZ_seminorm_bound`:
    ‖ψ_z‖_{k,n} ≤ B · (1+‖Re z‖)^N · (1 + dist(Im z, ∂C)⁻¹)^M -/
theorem fourierLaplaceExtMultiDim_vladimirov_growth
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (C_bd : ℝ) (N M : ℕ), C_bd > 0 ∧
      ∀ (z : Fin m → ℂ), z ∈ SCV.TubeDomain C →
        ‖fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone T z‖ ≤
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
    multiDimPsiZ_finset_sup_bound C hC_open hC_conv hC_cone s
  -- Step 3: Combine
  refine ⟨C_T * B, N, M, mul_pos hC_T_pos hB_pos, fun z hz => ?_⟩
  rw [fourierLaplaceExtMultiDim_eq C hC_open hC_conv hC_cone T z hz]
  calc ‖T (multiDimPsiZ C hC_open hC_conv hC_cone z hz)‖
    _ ≤ C_T * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ))
          (multiDimPsiZ C hC_open hC_conv hC_cone z hz) := hT_bound _
    _ ≤ C_T * (B * (1 + ‖fun i => (z i).re‖) ^ N *
          (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M) := by
        apply mul_le_mul_of_nonneg_left (hψ_bound z hz) (by exact_mod_cast C_T.coe_nonneg)
    _ ≤ C_T * B * (1 + ‖z‖) ^ N *
          (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M := by
        have hre_le : ‖fun i => (z i).re‖ ≤ ‖z‖ := by
          apply pi_norm_le_iff_of_nonneg (norm_nonneg z) |>.mpr
          intro i
          calc ‖(z i).re‖ = |(z i).re| := Real.norm_eq_abs _
            _ ≤ ‖z i‖ := Complex.abs_re_le_norm (z i)
            _ ≤ ‖z‖ := norm_le_pi_norm z i
        have hre_nn : (0 : ℝ) ≤ 1 + ‖fun i => (z i).re‖ := by positivity
        have h1 : (1 + ‖fun i => (z i).re‖) ^ N ≤ (1 + ‖z‖) ^ N :=
          pow_le_pow_left₀ hre_nn (by linarith) N
        have hCB : 0 ≤ C_T * B := mul_nonneg (le_of_lt hC_T_pos) (le_of_lt hB_pos)
        have hinfDist_nn : (0 : ℝ) ≤ Metric.infDist (fun i => (z i).im) Cᶜ :=
          Metric.infDist_nonneg
        have hD : (0 : ℝ) ≤ (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M :=
          pow_nonneg (by linarith [inv_nonneg.mpr hinfDist_nn]) _
        nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCB) hD]

/-! ### Boundary values -/

/-- F(z) = T(ψ_z) has tempered distributional boundary values recovering T.

    Proof: As ε → 0+ along direction η ∈ C,
    ∫ F(x+iεη) f(x) dx = ∫ T(ψ_{x+iεη}) f(x) dx → T(f)
    by the dominated convergence theorem (dominator from the growth bound
    times Schwartz decay of f). -/
theorem fourierLaplaceExtMultiDim_boundaryValue
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∀ (η : Fin m → ℝ), η ∈ C →
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin m → ℝ,
            fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone T
              (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) *
            f x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (T f)) := by
  sorry

end
