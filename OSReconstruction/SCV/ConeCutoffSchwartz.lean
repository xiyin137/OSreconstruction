/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.FourierSupportCone
import OSReconstruction.SCV.FourierLaplaceCore
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# Concrete Construction of the Cone-Adapted Schwartz Family

This file constructs the multi-dimensional Schwartz family ψ_{z,R} concretely
from a `FixedConeCutoff` adapted to the dual cone.

## The construction

Given:
- C : an open convex salient cone in ℝ^m
- χ : a `FixedConeCutoff` for `DualConeFlat C` (the dual cone)
- R > 0 : the cutoff radius
- z ∈ T(C) : a point in the tube

Define:
  `psiZR χ R z ξ = χ(ξ/R) * exp(i z·ξ)`

where `z·ξ = ∑_j z_j * ξ_j`.

## Properties

- **Smooth in ξ**: χ is C^∞, exp is C^∞, product is C^∞
- **Schwartz decay**: On supp(χ(·/R)), ξ is within distance R of DualConeFlat(C).
  For y ∈ C (salient), `y·ξ ≥ c·‖ξ‖ - c'·R·‖y‖` on this support, giving
  `exp(-y·ξ) ≤ exp(c'·R·‖y‖) * exp(-c·‖ξ‖)` — exponential decay.
  Combined with polynomial growth of χ-derivatives (bounded by R^{-|α|}),
  the product is Schwartz.
- **Seminorm bound** (fixed R=1): `‖ψ_z‖_{k,n} ≤ B·(1+‖x‖)^N·exp(C·‖y‖)`
  (exponential in y — this is why fixed R doesn't give Vladimirov bound)
- **Seminorm bound** (dynamic R=1/(1+‖y‖)): `‖ψ_z‖_{k,n} ≤ B·(1+‖x‖)^N·(1+‖y‖)^M`
  (polynomial in y — the Vladimirov bound!)

## References

- Vladimirov, "Methods of Generalized Functions", §25
- See docs/vladimirov_tillmann_gemini_reviews.md for the dynamic scaling trick
-/

open scoped Classical ComplexConjugate BigOperators NNReal ContDiff
open MeasureTheory Complex
noncomputable section

variable {m : ℕ}

/-! ### Cone-scaling of infDist -/

/-- For a set S closed under positive scaling (a cone), the infDist scales:
    `infDist (a • ξ) S = |a| * infDist ξ S` for a > 0.
    Proof: inf_{η ∈ S} ‖aξ - η‖ = inf_{η ∈ S} ‖a(ξ - η/a)‖ = |a| * inf_{η' ∈ S} ‖ξ - η'‖
    where η' = η/a ranges over S. -/
theorem infDist_smul_cone {S : Set (Fin m → ℝ)}
    (hS_cone : ∀ (y : Fin m → ℝ), y ∈ S → ∀ (t : ℝ), 0 < t → t • y ∈ S)
    {a : ℝ} (ha : 0 < a) (ξ : Fin m → ℝ) :
    Metric.infDist (a • ξ) S = a * Metric.infDist ξ S := by
  have ha_inv : 0 < a⁻¹ := inv_pos.mpr ha
  let e : ↥S ≃ ↥S :=
    { toFun := fun y => ⟨a • y.1, hS_cone y.1 y.2 a ha⟩
      invFun := fun y => ⟨a⁻¹ • y.1, hS_cone y.1 y.2 a⁻¹ ha_inv⟩
      left_inv := by
        intro y
        ext i
        simp [Pi.smul_apply]
        rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      right_inv := by
        intro y
        ext i
        simp [Pi.smul_apply]
        rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] }
  rw [Metric.infDist_eq_iInf, Metric.infDist_eq_iInf]
  calc
    (⨅ y : S, dist (a • ξ) y) = ⨅ y : S, dist (a • ξ) (e y) := by
      symm
      exact Equiv.iInf_congr e fun _ => rfl
    _ = ⨅ y : S, a * dist ξ y := by
      congr with y
      change ‖a • ξ - a • (y : Fin m → ℝ)‖ = a * ‖ξ - y‖
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg ha.le]
    _ = a * ⨅ y : S, dist ξ y := by
      rw [← Real.mul_iInf_of_nonneg ha.le]

/-! ### The raw function (not yet a SchwartzMap) -/

/-- The raw cone-adapted exponential-cutoff function.
    `psiZRaw χ R z ξ = χ(ξ/R) * exp(i z·ξ)` -/
def psiZRaw {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    (R : ℝ) (z : Fin m → ℂ) (ξ : Fin m → ℝ) : ℂ :=
  (χ.val (fun i => R⁻¹ * ξ i) : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))

/-- The raw function is smooth in ξ (for fixed z and R > 0). -/
theorem psiZRaw_contDiff {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    (R : ℝ) (z : Fin m → ℂ) :
    ContDiff ℝ ∞ (psiZRaw χ R z) := by
  unfold psiZRaw
  have hscale : ContDiff ℝ ∞ (fun ξ : Fin m → ℝ => fun i => R⁻¹ * ξ i) := by
    refine contDiff_pi.2 fun i => ?_
    simpa [Pi.smul_apply, smul_eq_mul] using
      (((R⁻¹ : ℝ) •
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i)).contDiff :
        ContDiff ℝ ∞ ((R⁻¹ : ℝ) •
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i)))
  have hcutoff : ContDiff ℝ ∞
      (fun ξ : Fin m → ℝ => (χ.val (fun i => R⁻¹ * ξ i) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (χ.smooth.comp hscale)
  have hexpArg : ContDiff ℝ ∞
      (fun ξ : Fin m → ℝ => I * ∑ i, z i * (ξ i : ℂ)) := by
    refine contDiff_const.mul <| ContDiff.sum fun i _ => ?_
    exact contDiff_const.mul <|
      Complex.ofRealCLM.contDiff.comp
        ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i).contDiff)
  exact hcutoff.mul (Complex.contDiff_exp.comp hexpArg)

/-- The raw function vanishes for ξ far from the dual cone (distance > R). -/
theorem psiZRaw_support {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    {R : ℝ} (hR : 0 < R) (z : Fin m → ℂ) (ξ : Fin m → ℝ)
    (hξ : Metric.infDist ξ (DualConeFlat C) > R) :
    psiZRaw χ R z ξ = 0 := by
  simp only [psiZRaw]
  have hχ_zero : χ.val (fun i => R⁻¹ * ξ i) = 0 := by
    apply χ.support_bound
    -- infDist(R⁻¹ξ, DualConeFlat C) = R⁻¹ * infDist(ξ, DualConeFlat C) > R⁻¹ * R = 1
    -- DualConeFlat C is a cone (scaling-closed)
    have hS_cone : ∀ (y : Fin m → ℝ), y ∈ DualConeFlat C →
        ∀ (t : ℝ), 0 < t → t • y ∈ DualConeFlat C := by
      intro y hy t ht
      rw [mem_dualConeFlat] at hy ⊢
      intro w hw
      have := hy w hw
      simp [Pi.smul_apply, smul_eq_mul]
      calc ∑ i, w i * (t * y i) = t * ∑ i, w i * y i := by
            rw [Finset.mul_sum]; congr 1; ext i; ring
        _ ≥ 0 := mul_nonneg (le_of_lt ht) this
    have hscale : Metric.infDist (R⁻¹ • ξ) (DualConeFlat C) =
        R⁻¹ * Metric.infDist ξ (DualConeFlat C) :=
      infDist_smul_cone hS_cone (inv_pos.mpr hR) ξ
    show Metric.infDist (fun i => R⁻¹ * ξ i) (DualConeFlat C) > 1
    simp only [show (fun i => R⁻¹ * ξ i) = R⁻¹ • ξ from rfl]
    rw [hscale]
    calc 1 = R⁻¹ * R := by rw [inv_mul_cancel₀ (ne_of_gt hR)]
      _ < R⁻¹ * Metric.infDist ξ (DualConeFlat C) := by
          apply mul_lt_mul_of_pos_left hξ (inv_pos.mpr hR)
  simp [hχ_zero]

/-- Two cutoff radii give the same function on the dual cone itself. -/
theorem psiZRaw_eq_on_dualCone {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (z : Fin m → ℂ) (ξ : Fin m → ℝ)
    (hξ : ξ ∈ DualConeFlat C) :
    psiZRaw χ R₁ z ξ = psiZRaw χ R₂ z ξ := by
  simp only [psiZRaw]
  -- Both χ(ξ/R₁) = 1 and χ(ξ/R₂) = 1 because:
  -- ξ ∈ DualConeFlat C, DualConeFlat is a cone, so R⁻¹ξ ∈ DualConeFlat C
  have hξ₁ : (fun i => R₁⁻¹ * ξ i) ∈ DualConeFlat C := by
    rw [mem_dualConeFlat] at hξ ⊢
    intro y hy
    have := hξ y hy
    calc ∑ i, y i * (R₁⁻¹ * ξ i)
        = R₁⁻¹ * ∑ i, y i * ξ i := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≥ 0 := mul_nonneg (inv_nonneg.mpr (le_of_lt hR₁)) this
  have hξ₂ : (fun i => R₂⁻¹ * ξ i) ∈ DualConeFlat C := by
    rw [mem_dualConeFlat] at hξ ⊢
    intro y hy
    have := hξ y hy
    calc ∑ i, y i * (R₂⁻¹ * ξ i)
        = R₂⁻¹ * ∑ i, y i * ξ i := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≥ 0 := mul_nonneg (inv_nonneg.mpr (le_of_lt hR₂)) this
  obtain ⟨ε, hε, hone⟩ := χ.one_on_neighborhood
  have h1 : χ.val (fun i => R₁⁻¹ * ξ i) = 1 :=
    hone _ (by rw [Metric.infDist_zero_of_mem hξ₁]; exact hε)
  have h2 : χ.val (fun i => R₂⁻¹ * ξ i) = 1 :=
    hone _ (by rw [Metric.infDist_zero_of_mem hξ₂]; exact hε)
  rw [h1, h2]

/-! ### Cone-coercivity lemma -/

/-- **Strict positivity**: For y in an open cone C and ξ ∈ DualConeFlat(C) \ {0},
    the pairing y·ξ is strictly positive.

    Proof: If y·ξ₀ = 0 for some ξ₀ ∈ C* \ {0}, then since C is open, there exists
    w ∈ C near y with w·ξ₀ < 0 (perturb y in the -ξ₀ direction). This contradicts
    ξ₀ ∈ C* = {ξ : ∀ w ∈ C, w·ξ ≥ 0}. -/
theorem dualConeFlat_pairing_pos_of_open
    {C : Set (Fin m → ℝ)} (hC_open : IsOpen C)
    {y : Fin m → ℝ} (hy : y ∈ C) {ξ : Fin m → ℝ} (hξ : ξ ∈ DualConeFlat C)
    (hξ_ne : ξ ≠ 0) :
    0 < ∑ i, y i * ξ i := by
  by_contra h
  push_neg at h
  have h_nn := hξ y hy
  have h_zero : ∑ i, y i * ξ i = 0 := le_antisymm h h_nn
  -- Since C is open and y ∈ C, there exists ε > 0 with B(y,ε) ∩ C nonempty
  -- In particular, y - t•ξ ∈ C for small t > 0
  rw [Metric.isOpen_iff] at hC_open
  obtain ⟨ε, hε, hball⟩ := hC_open y hy
  -- ξ ≠ 0 so ‖ξ‖ > 0
  have hξ_norm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ_ne
  -- Choose t = ε / (2 * ‖ξ‖), so ‖t • ξ‖ = t * ‖ξ‖ = ε/2 < ε
  set t := ε / (2 * ‖ξ‖) with ht_def
  have ht_pos : 0 < t := div_pos hε (mul_pos two_pos hξ_norm)
  have ht_small : ‖t • ξ‖ < ε := by
    rw [norm_smul, Real.norm_of_nonneg ht_pos.le, ht_def]
    calc ε / (2 * ‖ξ‖) * ‖ξ‖ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  -- y - t•ξ ∈ C (within the ε-ball)
  have hw_mem : y - t • ξ ∈ C := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    simp [ht_small]
  -- But (y - t•ξ)·ξ = y·ξ - t*‖ξ‖² = 0 - t*‖ξ‖² < 0
  have hw_neg : ∑ i, (y - t • ξ) i * ξ i < 0 := by
    -- (y - tξ)·ξ = y·ξ - t(ξ·ξ) = 0 - t‖ξ‖² < 0
    have hsum_sq_pos : 0 < ∑ i, ξ i * ξ i := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hξ_ne
      have hterm_pos : 0 < ξ i * ξ i := by
        nlinarith [sq_pos_of_ne_zero hi]
      have hterm_le : ξ i * ξ i ≤ ∑ j, ξ j * ξ j := by
        simpa using
          (Finset.single_le_sum (fun j _ => mul_self_nonneg (ξ j)) (by simp : i ∈ Finset.univ))
      exact lt_of_lt_of_le hterm_pos hterm_le
    calc
      ∑ i, (y - t • ξ) i * ξ i
          = ∑ i, (y i * ξ i - (t • ξ) i * ξ i) := by
              congr with i
              simp [Pi.sub_apply, sub_mul]
      _ = ∑ i, y i * ξ i - ∑ i, (t • ξ) i * ξ i := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ i, y i * ξ i - t * ∑ i, ξ i * ξ i := by
            congr 1
            calc
              ∑ i, (t • ξ) i * ξ i = ∑ i, t * (ξ i * ξ i) := by
                congr with i
                simp [Pi.smul_apply]
                ring
              _ = t * ∑ i, ξ i * ξ i := by
                rw [Finset.mul_sum]
      _ = -(t * ∑ i, ξ i * ξ i) := by rw [h_zero, zero_sub]
      _ < 0 := by
            have hprod_pos : 0 < t * ∑ i, ξ i * ξ i := mul_pos ht_pos hsum_sq_pos
            linarith
  -- This contradicts ξ ∈ DualConeFlat C
  exact absurd (hξ (y - t • ξ) hw_mem) (not_le.mpr hw_neg)

/-- **Cone-coercivity**: For y in an open cone C, there exists c > 0 such that
    y·ξ ≥ c * ‖ξ‖ for all ξ ∈ DualConeFlat(C).

    Proof: The function ξ ↦ y·ξ is continuous and strictly positive on the
    compact set C* ∩ S^{m-1}. Its minimum c on this set is > 0.
    For general ξ ∈ C*, y·ξ = ‖ξ‖ · (y · ξ/‖ξ‖) ≥ ‖ξ‖ · c. -/
theorem dualConeFlat_coercivity
    {C : Set (Fin m → ℝ)} (hC_open : IsOpen C) (hC_cone : IsCone C)
    {y : Fin m → ℝ} (hy : y ∈ C)
    (hC_star_ne : (DualConeFlat C).Nonempty)
    (hC_star_closed : IsClosed (DualConeFlat C)) :
    ∃ c > 0, ∀ ξ ∈ DualConeFlat C, ∑ i, y i * ξ i ≥ c * ‖ξ‖ := by
  let K : Set (Fin m → ℝ) := Metric.sphere (0 : Fin m → ℝ) 1 ∩ DualConeFlat C
  let f : (Fin m → ℝ) → ℝ := fun ξ => ∑ i, y i * ξ i
  have hDual_cone : ∀ (ξ : Fin m → ℝ), ξ ∈ DualConeFlat C →
      ∀ (t : ℝ), 0 < t → t • ξ ∈ DualConeFlat C := by
    intro ξ hξ t ht
    rw [mem_dualConeFlat] at hξ ⊢
    intro w hw
    have hpair := hξ w hw
    calc
      ∑ i, w i * (t • ξ) i = t * ∑ i, w i * ξ i := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        simp [Pi.smul_apply]
        ring
      _ ≥ 0 := mul_nonneg ht.le hpair
  by_cases hK : K.Nonempty
  · have hK_compact : IsCompact K := by
      dsimp [K]
      exact (isCompact_sphere (0 : Fin m → ℝ) 1).inter_right hC_star_closed
    have hf_cont : Continuous f := by
      dsimp [f]
      continuity
    obtain ⟨ξ₀, hξ₀K, hmin⟩ := hK_compact.exists_isMinOn hK hf_cont.continuousOn
    have hξ₀_ne : ξ₀ ≠ 0 := by
      intro hzero
      have hnorm : ‖ξ₀‖ = 1 := by
        simpa [K, Metric.mem_sphere, dist_eq_norm] using hξ₀K.1
      simpa [hzero] using hnorm
    refine ⟨f ξ₀, dualConeFlat_pairing_pos_of_open hC_open hy hξ₀K.2 hξ₀_ne, ?_⟩
    intro ξ hξ
    by_cases hξ_zero : ξ = 0
    · simp [hξ_zero]
    · have hξ_norm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ_zero
      let u : Fin m → ℝ := ‖ξ‖⁻¹ • ξ
      have hu_dual : u ∈ DualConeFlat C := by
        dsimp [u]
        exact hDual_cone ξ hξ ‖ξ‖⁻¹ (inv_pos.mpr hξ_norm)
      have hu_sphere : u ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm]
        dsimp [u]
        simpa using (show ‖‖ξ‖⁻¹ • ξ‖ = 1 by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hξ_norm.le), inv_mul_cancel₀]
          exact norm_ne_zero_iff.mpr hξ_zero)
      have huK : u ∈ K := ⟨hu_sphere, hu_dual⟩
      have hpair_u : f u = ‖ξ‖⁻¹ * f ξ := by
        dsimp [f, u]
        calc
          ∑ i, y i * ((‖ξ‖⁻¹ • ξ) i) = ∑ i, ‖ξ‖⁻¹ * (y i * ξ i) := by
            congr with i
            simp [Pi.smul_apply]
            ring
          _ = ‖ξ‖⁻¹ * ∑ i, y i * ξ i := by
            rw [Finset.mul_sum]
      have hpair_eq : f ξ = ‖ξ‖ * f u := by
        rw [hpair_u]
        field_simp [norm_ne_zero_iff.mpr hξ_zero]
      have hmul : ‖ξ‖ * f ξ₀ ≤ ‖ξ‖ * f u :=
        mul_le_mul_of_nonneg_left (hmin huK) hξ_norm.le
      calc
        f ξ = ‖ξ‖ * f u := hpair_eq
        _ ≥ ‖ξ‖ * f ξ₀ := hmul
        _ = f ξ₀ * ‖ξ‖ := by ring
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ξ hξ
    by_cases hξ_zero : ξ = 0
    · simp [hξ_zero]
    · have hξ_norm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ_zero
      let u : Fin m → ℝ := ‖ξ‖⁻¹ • ξ
      have hu_dual : u ∈ DualConeFlat C := by
        dsimp [u]
        exact hDual_cone ξ hξ ‖ξ‖⁻¹ (inv_pos.mpr hξ_norm)
      have hu_sphere : u ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm]
        dsimp [u]
        simpa using (show ‖‖ξ‖⁻¹ • ξ‖ = 1 by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hξ_norm.le), inv_mul_cancel₀]
          exact norm_ne_zero_iff.mpr hξ_zero)
      exact False.elim (hK ⟨u, ⟨hu_sphere, hu_dual⟩⟩)

theorem zero_mem_dualConeFlat (C : Set (Fin m → ℝ)) :
    (0 : Fin m → ℝ) ∈ DualConeFlat C := by
  rw [mem_dualConeFlat]
  intro y hy
  simp

theorem dualConeFlat_closed (C : Set (Fin m → ℝ)) :
    IsClosed (DualConeFlat C) := by
  have hrepr : DualConeFlat C = ⋂ y ∈ C, {ξ : Fin m → ℝ | (0 : ℝ) ≤ ∑ i, y i * ξ i} := by
    ext ξ
    simp [DualConeFlat]
  rw [hrepr]
  refine isClosed_biInter ?_
  intro y hy
  exact isClosed_le continuous_const (by continuity)

/-! ### Schwartz decay (the hard part) -/

/-- The raw function has Schwartz decay when the cone is salient.
    This is the key analytic estimate: on supp(χ(·/R)),
    `exp(-y·ξ) ≤ exp(c·R·‖y‖)` (bounded in the transition region),
    combined with exponential decay `exp(-c'·‖ξ‖)` on the cone interior,
    gives overall rapid decay. -/
theorem psiZRaw_schwartz_decay
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_cone : IsCone C)
    (hC_salient : IsSalientCone C)
    (χ : FixedConeCutoff (DualConeFlat C))
    {R : ℝ} (hR : 0 < R)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C)
    (k : ℕ) :
    ∃ (D : ℝ), ∀ (ξ : Fin m → ℝ),
      ‖ξ‖ ^ k * ‖psiZRaw χ R z ξ‖ ≤ D := by
  let yIm : Fin m → ℝ := fun i => (z i).im
  have hyIm : yIm ∈ C := hz
  have hC_star_ne : (DualConeFlat C).Nonempty := ⟨0, zero_mem_dualConeFlat C⟩
  have hC_star_closed : IsClosed (DualConeFlat C) := dualConeFlat_closed C
  obtain ⟨c, hc_pos, hc⟩ :=
    dualConeFlat_coercivity hC_open hC_cone hyIm hC_star_ne hC_star_closed
  let B : ℝ := ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖yIm‖
  let A : ℝ := c + B
  obtain ⟨M, hM_pos, hM⟩ := SCV.pow_mul_exp_neg_le_const hc_pos k
  refine ⟨Real.exp (A * R) * M, fun ξ => ?_⟩
  by_cases hfar : Metric.infDist ξ (DualConeFlat C) > R
  · have hzero : psiZRaw χ R z ξ = 0 := psiZRaw_support χ hR z ξ hfar
    rw [hzero]
    have hDpos : 0 < Real.exp (A * R) * M := mul_pos (Real.exp_pos _) hM_pos
    simpa using (le_of_lt hDpos)
  · have hdist : Metric.infDist ξ (DualConeFlat C) ≤ R := le_of_not_gt hfar
    obtain ⟨η, hηcl, hηdist⟩ :=
      Metric.exists_mem_closure_infDist_eq_dist hC_star_ne ξ
    have hη : η ∈ DualConeFlat C := by
      simpa [hC_star_closed.closure_eq] using hηcl
    let d : Fin m → ℝ := ξ - η
    have hd_norm : ‖d‖ ≤ R := by
      dsimp [d]
      simpa [dist_eq_norm] using (show dist ξ η ≤ R by rwa [← hηdist])
    have hpair_err_norm :
        ‖∑ i, yIm i * d i‖ ≤ B * ‖d‖ := by
      have hy_sum :
          ∑ i, ‖yIm i‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖yIm‖ := by
        simpa [nsmul_eq_mul] using (Pi.sum_norm_apply_le_norm yIm)
      have hd_sum :
          ∑ i, ‖d i‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖d‖ := by
        simpa [nsmul_eq_mul] using (Pi.sum_norm_apply_le_norm d)
      calc
        ‖∑ i, yIm i * d i‖ ≤ ∑ i, ‖yIm i * d i‖ := norm_sum_le _ _
        _ = ∑ i, ‖yIm i‖ * ‖d i‖ := by simp [norm_mul]
        _ ≤ ∑ i, ∑ j, ‖yIm i‖ * ‖d j‖ := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact
                (Finset.single_le_sum
                  (s := Finset.univ)
                  (f := fun j : Fin m => ‖yIm i‖ * ‖d j‖)
                  (fun j hj => mul_nonneg (norm_nonneg _) (norm_nonneg _))
                  (Finset.mem_univ i))
        _ = (∑ i, ‖yIm i‖) * ∑ j, ‖d j‖ := by
              rw [Finset.sum_mul_sum]
        _ ≤ ((Fintype.card (Fin m) : ℝ) * ‖yIm‖) * ((Fintype.card (Fin m) : ℝ) * ‖d‖) := by
              gcongr
        _ = B * ‖d‖ := by
              dsimp [B]
              ring
    have hpair_err_lower :
        -(B * ‖d‖) ≤ ∑ i, yIm i * d i := by
      have habs : |∑ i, yIm i * d i| ≤ B * ‖d‖ := by
        simpa [Real.norm_eq_abs] using hpair_err_norm
      nlinarith [abs_le.mp habs]
    have hdecomp : ξ = η + d := by
      ext i
      simp [d]
    have hnorm_xi_le : ‖ξ‖ ≤ ‖η‖ + ‖d‖ := by
      calc
        ‖ξ‖ = ‖η + d‖ := by rw [hdecomp]
        _ ≤ ‖η‖ + ‖d‖ := norm_add_le _ _
    have hpair_decomp :
        ∑ i, yIm i * ξ i = ∑ i, yIm i * η i + ∑ i, yIm i * d i := by
      calc
        ∑ i, yIm i * ξ i = ∑ i, yIm i * (η i + d i) := by simp [hdecomp]
        _ = ∑ i, (yIm i * η i + yIm i * d i) := by
              congr with i
              ring
        _ = ∑ i, yIm i * η i + ∑ i, yIm i * d i := by
              rw [Finset.sum_add_distrib]
    have hpair_lower :
        c * ‖ξ‖ - A * R ≤ ∑ i, yIm i * ξ i := by
      have hηlower : c * ‖η‖ ≤ ∑ i, yIm i * η i := hc η hη
      have hη_from_ξ : c * ‖ξ‖ - c * ‖d‖ ≤ c * ‖η‖ := by
        nlinarith [hnorm_xi_le, hc_pos]
      have hmain :
          c * ‖ξ‖ - c * ‖d‖ - B * ‖d‖
            ≤ ∑ i, yIm i * η i + ∑ i, yIm i * d i := by
        nlinarith [hηlower, hpair_err_lower, hη_from_ξ]
      have hRstep :
          c * ‖ξ‖ - A * R
            ≤ c * ‖ξ‖ - c * ‖d‖ - B * ‖d‖ := by
        have hAnonneg : 0 ≤ A := by
          dsimp [A, B]
          positivity
        have hmul : A * ‖d‖ ≤ A * R := mul_le_mul_of_nonneg_left hd_norm hAnonneg
        dsimp [A] at hmul ⊢
        nlinarith
      rw [hpair_decomp]
      exact le_trans hRstep hmain
    have hExpRe :
        Complex.re (Complex.I * ∑ i, z i * (ξ i : ℂ)) = - ∑ i, yIm i * ξ i := by
      simp [yIm, Complex.mul_re, Complex.mul_im, mul_comm, mul_left_comm, mul_assoc]
    have hExpBound :
        ‖Complex.exp (Complex.I * ∑ i, z i * (ξ i : ℂ))‖ ≤
          Real.exp (A * R) * Real.exp (-(c * ‖ξ‖)) := by
      rw [Complex.norm_exp, hExpRe]
      have hre : -(∑ i, yIm i * ξ i) ≤ A * R - c * ‖ξ‖ := by
        linarith
      calc
        Real.exp (-∑ i, yIm i * ξ i) ≤ Real.exp (A * R - c * ‖ξ‖) := by
          exact Real.exp_le_exp.mpr hre
        _ = Real.exp (A * R) * Real.exp (-(c * ‖ξ‖)) := by
          rw [sub_eq_add_neg, Real.exp_add]
    have hχnorm :
        ‖((χ.val (fun i => R⁻¹ * ξ i) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (χ.val_nonneg _)]
      exact χ.val_le_one _
    calc
      ‖ξ‖ ^ k * ‖psiZRaw χ R z ξ‖
          = ‖ξ‖ ^ k * (‖((χ.val (fun i => R⁻¹ * ξ i) : ℝ) : ℂ)‖ *
              ‖Complex.exp (Complex.I * ∑ i, z i * (ξ i : ℂ))‖) := by
                simp [psiZRaw, norm_mul]
      _ ≤ ‖ξ‖ ^ k * (1 * (Real.exp (A * R) * Real.exp (-(c * ‖ξ‖)))) := by
            gcongr
      _ = Real.exp (A * R) * (‖ξ‖ ^ k * Real.exp (-(c * ‖ξ‖))) := by ring
      _ ≤ Real.exp (A * R) * M := by
            gcongr
            exact hM ‖ξ‖ (norm_nonneg _)
/-! ### Packaging as SchwartzMap -/

/-- **Exponential bound on the support region**: For `z ∈ T(C)` with coercivity constant `c`,
    when `infDist(ξ, DualConeFlat C) ≤ R`, the complex exponential satisfies
    `‖cexp(iz·ξ)‖ ≤ exp(A·R) · exp(-c·‖ξ‖)` where `A = c + m² · ‖Im(z)‖`. -/
theorem cexp_bound_on_support
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_cone : IsCone C)
    {z : Fin m → ℂ} (hz : z ∈ SCV.TubeDomain C)
    {c : ℝ} (hc_pos : 0 < c)
    (hc : ∀ ξ ∈ DualConeFlat C, ∑ i, (fun i => (z i).im) i * ξ i ≥ c * ‖ξ‖)
    {R : ℝ} (hR : 0 < R)
    (ξ : Fin m → ℝ) (hdist : Metric.infDist ξ (DualConeFlat C) ≤ R) :
    ‖cexp (I * ∑ i, z i * (ξ i : ℂ))‖ ≤
      Real.exp (((c + ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖fun i => (z i).im‖)) * R) *
        Real.exp (-(c * ‖ξ‖)) := by
  let yIm : Fin m → ℝ := fun i => (z i).im
  let B : ℝ := ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖yIm‖
  let A : ℝ := c + B
  have hC_star_ne : (DualConeFlat C).Nonempty := ⟨0, zero_mem_dualConeFlat C⟩
  obtain ⟨η, hηcl, hηdist⟩ :=
    Metric.exists_mem_closure_infDist_eq_dist hC_star_ne ξ
  have hη : η ∈ DualConeFlat C := by
    simpa [(dualConeFlat_closed C).closure_eq] using hηcl
  let d : Fin m → ℝ := ξ - η
  have hd_norm : ‖d‖ ≤ R := by
    dsimp [d]
    simpa [dist_eq_norm] using (show dist ξ η ≤ R by rwa [← hηdist])
  have hpair_err_norm :
      ‖∑ i, yIm i * d i‖ ≤ B * ‖d‖ := by
    have hy_sum :
        ∑ i, ‖yIm i‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖yIm‖ := by
      simpa [nsmul_eq_mul] using (Pi.sum_norm_apply_le_norm yIm)
    have hd_sum :
        ∑ i, ‖d i‖ ≤ (Fintype.card (Fin m) : ℝ) * ‖d‖ := by
      simpa [nsmul_eq_mul] using (Pi.sum_norm_apply_le_norm d)
    calc
      ‖∑ i, yIm i * d i‖ ≤ ∑ i, ‖yIm i * d i‖ := norm_sum_le _ _
      _ = ∑ i, ‖yIm i‖ * ‖d i‖ := by simp [norm_mul]
      _ ≤ ∑ i, ∑ j, ‖yIm i‖ * ‖d j‖ := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact
              (Finset.single_le_sum
                (s := Finset.univ)
                (f := fun j : Fin m => ‖yIm i‖ * ‖d j‖)
                (fun j hj => mul_nonneg (norm_nonneg _) (norm_nonneg _))
                (Finset.mem_univ i))
      _ = (∑ i, ‖yIm i‖) * ∑ j, ‖d j‖ := by
            rw [Finset.sum_mul_sum]
      _ ≤ ((Fintype.card (Fin m) : ℝ) * ‖yIm‖) * ((Fintype.card (Fin m) : ℝ) * ‖d‖) := by
            gcongr
      _ = B * ‖d‖ := by
            dsimp [B]
            ring
  have hpair_err_lower :
      -(B * ‖d‖) ≤ ∑ i, yIm i * d i := by
    have habs : |∑ i, yIm i * d i| ≤ B * ‖d‖ := by
      simpa [Real.norm_eq_abs] using hpair_err_norm
    nlinarith [abs_le.mp habs]
  have hdecomp : ξ = η + d := by
    ext i
    simp [d]
  have hnorm_xi_le : ‖ξ‖ ≤ ‖η‖ + ‖d‖ := by
    calc
      ‖ξ‖ = ‖η + d‖ := by rw [hdecomp]
      _ ≤ ‖η‖ + ‖d‖ := norm_add_le _ _
  have hpair_decomp :
      ∑ i, yIm i * ξ i = ∑ i, yIm i * η i + ∑ i, yIm i * d i := by
    calc
      ∑ i, yIm i * ξ i = ∑ i, yIm i * (η i + d i) := by simp [hdecomp]
      _ = ∑ i, (yIm i * η i + yIm i * d i) := by
            congr with i
            ring
      _ = ∑ i, yIm i * η i + ∑ i, yIm i * d i := by
            rw [Finset.sum_add_distrib]
  have hpair_lower :
      c * ‖ξ‖ - A * R ≤ ∑ i, yIm i * ξ i := by
    have hηlower : c * ‖η‖ ≤ ∑ i, yIm i * η i := hc η hη
    have hη_from_ξ : c * ‖ξ‖ - c * ‖d‖ ≤ c * ‖η‖ := by
      nlinarith [hnorm_xi_le, hc_pos]
    have hmain :
        c * ‖ξ‖ - c * ‖d‖ - B * ‖d‖
          ≤ ∑ i, yIm i * η i + ∑ i, yIm i * d i := by
      nlinarith [hηlower, hpair_err_lower, hη_from_ξ]
    have hRstep :
        c * ‖ξ‖ - A * R
          ≤ c * ‖ξ‖ - c * ‖d‖ - B * ‖d‖ := by
      have hAnonneg : 0 ≤ A := by
        dsimp [A, B]
        positivity
      have hmul : A * ‖d‖ ≤ A * R := mul_le_mul_of_nonneg_left hd_norm hAnonneg
      dsimp [A] at hmul ⊢
      nlinarith
    rw [hpair_decomp]
    exact le_trans hRstep hmain
  have hExpRe :
      Complex.re (Complex.I * ∑ i, z i * (ξ i : ℂ)) = - ∑ i, yIm i * ξ i := by
    simp [yIm, Complex.mul_re, Complex.mul_im, mul_comm, mul_left_comm, mul_assoc]
  rw [Complex.norm_exp, hExpRe]
  have hre : -(∑ i, yIm i * ξ i) ≤ A * R - c * ‖ξ‖ := by
    linarith
  calc
    Real.exp (-∑ i, yIm i * ξ i) ≤ Real.exp (A * R - c * ‖ξ‖) := by
      exact Real.exp_le_exp.mpr hre
    _ = Real.exp (A * R) * Real.exp (-(c * ‖ξ‖)) := by
      rw [sub_eq_add_neg, Real.exp_add]

/-- Higher-derivative decay for the concrete cone-adapted exponential-cutoff function.
    This is the multivariate Leibniz/scaling estimate used to package `psiZRaw`
    as a `SchwartzMap`. -/
theorem psiZRaw_iteratedFDeriv_decay
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_cone : IsCone C)
    (hC_salient : IsSalientCone C)
    (χ : FixedConeCutoff (DualConeFlat C))
    {R : ℝ} (hR : 0 < R)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C)
    (k n : ℕ) :
    ∃ (D : ℝ), ∀ (ξ : Fin m → ℝ),
      ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (psiZRaw χ R z) ξ‖ ≤ D := by
  /-
  The key estimate: psiZRaw χ R z = fχ * gExp where fχ is the cutoff factor
  and gExp is the exponential. By the Leibniz rule for iteratedFDeriv of a product
  (norm_iteratedFDeriv_mul_le), the n-th derivative is bounded by a sum of
  products of cutoff derivatives (uniformly bounded) and exponential derivatives
  (bounded by ‖L‖^j * ‖gExp‖). On the support region, the exponential decays
  as exp(-c‖ξ‖) by cone-coercivity, so ‖ξ‖^k * (product) ≤ D.
  -/
  -- ── Setup: coercivity and polynomial-vs-exponential constant ──
  let yIm : Fin m → ℝ := fun i => (z i).im
  have hyIm : yIm ∈ C := hz
  have hC_star_ne : (DualConeFlat C).Nonempty := ⟨0, zero_mem_dualConeFlat C⟩
  have hC_star_closed : IsClosed (DualConeFlat C) := dualConeFlat_closed C
  obtain ⟨c, hc_pos, hc⟩ :=
    dualConeFlat_coercivity hC_open hC_cone hyIm hC_star_ne hC_star_closed
  let B : ℝ := ((Fintype.card (Fin m) : ℝ) ^ 2) * ‖yIm‖
  let A : ℝ := c + B
  obtain ⟨M, hM_pos, hM⟩ := SCV.pow_mul_exp_neg_le_const hc_pos k
  -- ── Support containment: psiZRaw vanishes when infDist > R ──
  have hsupp_sub : Function.support (psiZRaw χ R z) ⊆
      {ξ | Metric.infDist ξ (DualConeFlat C) ≤ R} := by
    intro ξ hξ
    simp only [Function.mem_support] at hξ
    by_contra h
    simp only [Set.mem_setOf_eq, not_le] at h
    exact hξ (psiZRaw_support χ hR z ξ h)
  have hclosed_region : IsClosed {ξ : Fin m → ℝ | Metric.infDist ξ (DualConeFlat C) ≤ R} :=
    isClosed_le (Metric.continuous_infDist_pt (s := DualConeFlat C)) continuous_const
  have htsupport_sub : tsupport (psiZRaw χ R z) ⊆
      {ξ | Metric.infDist ξ (DualConeFlat C) ≤ R} :=
    closure_minimal hsupp_sub hclosed_region
  -- ── The two factors ──
  let fχ : (Fin m → ℝ) → ℂ := fun ξ => (χ.val (fun i => R⁻¹ * ξ i) : ℂ)
  let gExp : (Fin m → ℝ) → ℂ := fun ξ => cexp (I * ∑ i, z i * (ξ i : ℂ))
  -- Smoothness of the two factors (from psiZRaw_contDiff proof)
  have hfχ_smooth : ContDiff ℝ ∞ fχ := by
    exact Complex.ofRealCLM.contDiff.comp (χ.smooth.comp
      (contDiff_pi.2 fun i =>
        (((R⁻¹ : ℝ) •
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i)).contDiff)))
  have hgExp_smooth : ContDiff ℝ ∞ gExp := by
    refine Complex.contDiff_exp.comp ?_
    refine contDiff_const.mul <| ContDiff.sum fun i _ => ?_
    exact contDiff_const.mul <|
      Complex.ofRealCLM.contDiff.comp
        ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i).contDiff)
  -- ── Uniform bound on cutoff derivatives ──
  have hfχ_deriv_bound : ∀ i : ℕ, ∃ (Ci : ℝ), 0 ≤ Ci ∧ ∀ ξ : Fin m → ℝ,
      ‖iteratedFDeriv ℝ i fχ ξ‖ ≤ Ci := by
    intro i
    let S : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := R⁻¹ • ContinuousLinearMap.id ℝ (Fin m → ℝ)
    obtain ⟨Cχ, hCχ⟩ := χ.deriv_bound i
    have hχS_smooth : ContDiff ℝ ∞ (χ.val ∘ S) := χ.smooth.comp S.contDiff
    refine ⟨(max Cχ 0 + 1) * (‖S‖ ^ i + 1), by positivity, fun ξ => ?_⟩
    have hS_eq : ∀ ξ : Fin m → ℝ, S ξ = fun j => R⁻¹ * ξ j := by
      intro ξ
      ext j
      simp [S, Pi.smul_apply, smul_eq_mul]
    have hfχ_eq : fχ = (RCLike.ofRealLI (K := ℂ)) ∘ (χ.val ∘ S) := by
      funext ξ
      simp only [fχ, Function.comp, RCLike.ofRealLI_apply]
      -- Goal: ↑(χ.val (fun i => R⁻¹ * ξ i)) = ↑(χ.val (R⁻¹ • ξ))
      norm_cast
    calc ‖iteratedFDeriv ℝ i fχ ξ‖
        = ‖iteratedFDeriv ℝ i ((RCLike.ofRealLI (K := ℂ)) ∘ (χ.val ∘ S)) ξ‖ := by
            rw [hfχ_eq]
      _ = ‖iteratedFDeriv ℝ i (χ.val ∘ S) ξ‖ :=
            (RCLike.ofRealLI (K := ℂ)).norm_iteratedFDeriv_comp_left hχS_smooth.contDiffAt
              (by exact_mod_cast le_top)
      _ = ‖(iteratedFDeriv ℝ i χ.val (S ξ)).compContinuousLinearMap fun _ => S‖ := by
            rw [S.iteratedFDeriv_comp_right χ.smooth ξ (by exact_mod_cast le_top)]
      _ ≤ ‖iteratedFDeriv ℝ i χ.val (S ξ)‖ * ∏ _ : Fin i, ‖S‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ i χ.val (S ξ)‖ * ‖S‖ ^ i := by
            rw [Finset.prod_const, Finset.card_fin]
      _ ≤ Cχ * ‖S‖ ^ i := by
            gcongr
            exact hCχ (S ξ)
      _ ≤ (max Cχ 0 + 1) * (‖S‖ ^ i + 1) := by
            nlinarith [le_max_left Cχ 0, le_max_right Cχ 0,
                        pow_nonneg (norm_nonneg S) i]
  -- ── Bound on exponential derivatives via iteratedFDeriv of cexp ──
  -- The linear exponent map L : (Fin m → ℝ) →L[ℝ] ℂ
  let L : (Fin m → ℝ) →L[ℝ] ℂ :=
    ∑ i : Fin m, ((I * z i) : ℂ) • (Complex.ofRealCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i))
  have hL_eq : gExp = cexp ∘ L := by
    ext ξ
    simp only [gExp, Function.comp, L, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
      Complex.ofRealCLM_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Function.comp_apply]
    congr 1
    rw [Finset.mul_sum]
    congr 1
    ext i
    ring
  -- Key: ‖iteratedFDeriv ℝ j cexp w‖ ≤ ‖cexp w‖
  have hcexp_iterFDeriv_norm : ∀ (j : ℕ) (w : ℂ),
      ‖iteratedFDeriv ℝ j cexp w‖ ≤ ‖cexp w‖ := by
    intro j w
    -- Step 1: ‖iteratedFDeriv ℂ j cexp w‖ = ‖cexp w‖
    have hiter_deriv : iteratedDeriv j (Complex.exp) w = cexp w := by
      rw [iteratedDeriv_eq_iterate]
      simp [Complex.iter_deriv_exp]
    have hComplex_norm : ‖iteratedFDeriv ℂ j cexp w‖ = ‖cexp w‖ := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact congrArg _ hiter_deriv
    -- Step 2: iteratedFDeriv ℝ = restrictScalars ∘ iteratedFDeriv ℂ
    have hSmooth : ContDiffAt ℂ (j : ℕ∞) cexp w := by
      exact (Complex.contDiff_exp (n := (j : ℕ∞))).contDiffAt
    have hRestrict : ((ContinuousMultilinearMap.restrictScalars ℝ) ∘
        iteratedFDeriv ℂ j cexp) w = iteratedFDeriv ℝ j cexp w :=
      hSmooth.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
    -- Step 3: Combine
    rw [← hRestrict, Function.comp_apply,
        ContinuousMultilinearMap.norm_restrictScalars, hComplex_norm]
  -- Bound on gExp derivatives
  have hgExp_deriv_bound : ∀ (j : ℕ) (ξ : Fin m → ℝ),
      ‖iteratedFDeriv ℝ j gExp ξ‖ ≤ ‖L‖ ^ j * ‖gExp ξ‖ := by
    intro j ξ
    have hcexp_smooth : ContDiff ℝ ⊤ (Complex.exp : ℂ → ℂ) :=
      show ContDiff ℝ ⊤ (cexp ∘ id) from Complex.contDiff_exp.comp contDiff_id
    calc ‖iteratedFDeriv ℝ j gExp ξ‖
        = ‖iteratedFDeriv ℝ j (cexp ∘ ⇑L) ξ‖ := by rw [hL_eq]
      _ = ‖(iteratedFDeriv ℝ j cexp (L ξ)).compContinuousLinearMap fun _ => L‖ := by
            rw [L.iteratedFDeriv_comp_right hcexp_smooth ξ (by exact_mod_cast le_top)]
      _ ≤ ‖iteratedFDeriv ℝ j cexp (L ξ)‖ * ∏ _ : Fin j, ‖L‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ j cexp (L ξ)‖ * ‖L‖ ^ j := by
            rw [Finset.prod_const, Finset.card_fin]
      _ ≤ ‖cexp (L ξ)‖ * ‖L‖ ^ j :=
            mul_le_mul_of_nonneg_right (hcexp_iterFDeriv_norm j (L ξ))
              (pow_nonneg (norm_nonneg _) _)
      _ = ‖L‖ ^ j * ‖cexp (L ξ)‖ := mul_comm _ _
      _ = ‖L‖ ^ j * ‖gExp ξ‖ := by
            congr 1
            -- cexp (L ξ) = gExp ξ by definition
            have hLξ : L ξ = I * ∑ i, z i * (ξ i : ℂ) := by
              simp only [L, ContinuousLinearMap.coe_sum', Finset.sum_apply,
                ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
                Complex.ofRealCLM_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
                Function.comp_apply]
              rw [Finset.mul_sum]
              congr 1
              ext i
              ring
            rw [hLξ]
  -- ── Assemble the constant D ──
  choose Cχ_fun hCχ_nonneg hCχ_bound using hfχ_deriv_bound
  let LeibConst : ℝ := Finset.sum (Finset.range (n + 1))
    (fun i => (n.choose i : ℝ) * Cχ_fun i * ‖L‖ ^ (n - i))
  have hLeibConst_nonneg : 0 ≤ LeibConst := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg
    apply mul_nonneg
    · exact Nat.cast_nonneg _
    · exact hCχ_nonneg i
    · exact pow_nonneg (norm_nonneg _) _
  refine ⟨LeibConst * (Real.exp (A * R) * M), fun ξ => ?_⟩
  by_cases hfar : Metric.infDist ξ (DualConeFlat C) > R
  · -- Case 1: outside support, iteratedFDeriv = 0
    have hξ_not_tsupport : ξ ∉ tsupport (psiZRaw χ R z) := by
      intro h
      have := htsupport_sub h
      simp only [Set.mem_setOf_eq] at this
      linarith
    have hξ_not_supp : ξ ∉ Function.support (iteratedFDeriv ℝ n (psiZRaw χ R z)) :=
      fun h => hξ_not_tsupport (support_iteratedFDeriv_subset n h)
    have hiter_zero : iteratedFDeriv ℝ n (psiZRaw χ R z) ξ = 0 := by
      rwa [Function.notMem_support] at hξ_not_supp
    simp only [hiter_zero, norm_zero, mul_zero]
    exact mul_nonneg hLeibConst_nonneg (mul_nonneg (Real.exp_pos _).le hM_pos.le)
  · -- Case 2: inside support region, use Leibniz + exponential decay
    push_neg at hfar
    -- Leibniz bound
    have hLeib : ‖iteratedFDeriv ℝ n (psiZRaw χ R z) ξ‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i fχ ξ‖ *
            ‖iteratedFDeriv ℝ (n - i) gExp ξ‖ :=
      norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (A := ℂ) hfχ_smooth hgExp_smooth ξ
        (by exact_mod_cast le_top)
    -- Bound the Leibniz sum by LeibConst * ‖gExp ξ‖
    have hsum_bound : ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i fχ ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) gExp ξ‖ ≤ LeibConst * ‖gExp ξ‖ := by
      have hstep1 : ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i fχ ξ‖ *
            ‖iteratedFDeriv ℝ (n - i) gExp ξ‖
          ≤ ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * Cχ_fun i * (‖L‖ ^ (n - i) * ‖gExp ξ‖) := by
        apply Finset.sum_le_sum
        intro i _hi
        have h1 := hCχ_bound i ξ
        have h2 := hgExp_deriv_bound (n - i) ξ
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        · exact h2
        · exact norm_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _) (hCχ_nonneg i)
      have hstep2 : ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * Cχ_fun i * (‖L‖ ^ (n - i) * ‖gExp ξ‖)
          = LeibConst * ‖gExp ξ‖ := by
        dsimp only [LeibConst]
        rw [Finset.sum_mul]
        congr 1 with i
        ring
      linarith
    -- Exponential norm bound
    have hExpBound : ‖gExp ξ‖ ≤ Real.exp (A * R) * Real.exp (-(c * ‖ξ‖)) :=
      cexp_bound_on_support hC_open hC_cone hz hc_pos hc hR ξ hfar
    -- Assemble
    calc ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (psiZRaw χ R z) ξ‖
        ≤ ‖ξ‖ ^ k * (LeibConst * ‖gExp ξ‖) := by
          apply mul_le_mul_of_nonneg_left (le_trans hLeib hsum_bound)
            (pow_nonneg (norm_nonneg _) _)
      _ = LeibConst * (‖ξ‖ ^ k * ‖gExp ξ‖) := by ring
      _ ≤ LeibConst * (‖ξ‖ ^ k * (Real.exp (A * R) * Real.exp (-(c * ‖ξ‖)))) := by
          apply mul_le_mul_of_nonneg_left _ hLeibConst_nonneg
          apply mul_le_mul_of_nonneg_left hExpBound (pow_nonneg (norm_nonneg _) _)
      _ = LeibConst * (Real.exp (A * R) * (‖ξ‖ ^ k * Real.exp (-(c * ‖ξ‖)))) := by ring
      _ ≤ LeibConst * (Real.exp (A * R) * M) := by
          apply mul_le_mul_of_nonneg_left _ hLeibConst_nonneg
          apply mul_le_mul_of_nonneg_left (hM ‖ξ‖ (norm_nonneg _)) (Real.exp_pos _).le


/-- The cone-adapted Schwartz function, packaged as a `SchwartzMap`.
    Requires the cone to be salient for Schwartz decay. -/
def psiZRSchwartz
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_cone : IsCone C)
    (hC_salient : IsSalientCone C)
    (χ : FixedConeCutoff (DualConeFlat C))
    (R : ℝ) (hR : 0 < R)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    SchwartzMap (Fin m → ℝ) ℂ where
  toFun := psiZRaw χ R z
  smooth' := by
    exact (psiZRaw_contDiff χ R z).of_le (by simp)
  decay' := by
    intro k n
    exact psiZRaw_iteratedFDeriv_decay hC_open hC_cone hC_salient χ hR z hz k n

end
