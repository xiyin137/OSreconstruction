/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.Spacetime.MinkowskiGeometry
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

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

open MeasureTheory Complex Filter Set Topology Module

/-! ### Momentum-Space Spectral Condition Definitions -/

section SpectralConditionDefinitions

variable (d : ℕ) [NeZero d]

/-- The product of closed forward light cones V̄₊ⁿ in momentum space.
    A momentum configuration (q₁, ..., qₙ) lies in this set iff each qₖ ∈ V̄₊. -/
def ProductForwardMomentumCone (n : ℕ) : Set (Fin n → Fin (d + 1) → ℝ) :=
  { q | ∀ k : Fin n, q k ∈ ForwardMomentumCone d }

/-- Uncurrying `(Fin n → Fin m → ℝ)` to `(Fin n × Fin m → ℝ)` as a linear equivalence. -/
def uncurryLinearEquiv (d n : ℕ) :
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
noncomputable def nPointToEuclidean (n : ℕ) :
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
noncomputable def diffVarSection (n : ℕ) :
    NPointSpacetime d n →L[ℝ] NPointSpacetime d (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ k μ => ∑ j : Fin k.val, ξ ⟨j.val, by omega⟩ μ
      map_add' := by
        intro ξ η; ext k μ; simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c ξ; ext k μ; simp [Finset.mul_sum] }

omit [NeZero d] in
@[simp] theorem diffVarSection_zero (n : ℕ)
    (ξ : NPointSpacetime d n) (μ : Fin (d + 1)) :
    diffVarSection d n ξ 0 μ = 0 := by
  simp [diffVarSection]

omit [NeZero d] in
@[simp] theorem diffVarSection_succ (n : ℕ)
    (ξ : NPointSpacetime d n) (k : Fin n) (μ : Fin (d + 1)) :
    diffVarSection d n ξ k.succ μ =
      diffVarSection d n ξ k.castSucc μ + ξ k μ := by
  change (∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ) =
    (∑ j : Fin k.val, ξ ⟨j.val, by omega⟩ μ) + ξ k μ
  rw [Fin.sum_univ_castSucc]
  simp [Fin.val_castSucc, Fin.val_last]

omit [NeZero d] in
theorem diffVarSection_injective (n : ℕ) :
    Function.Injective (diffVarSection d n) := by
  intro ξ₁ ξ₂ h
  ext k μ
  have h_succ := congr_fun₂ h k.succ μ
  have h_cast := congr_fun₂ h k.castSucc μ
  simp only [diffVarSection_succ] at h_succ
  linarith

/-- The integrand `a ↦ f(a + s(ξ))` of the fiber integral is integrable.
    The composition of a Schwartz function with the affine embedding
    `a ↦ (a, a+ξ₁, …)` is rapidly decreasing (since `‖embedding(a)‖ ≥ ‖a‖`),
    hence integrable on `ℝ^{d+1}`. -/
private theorem diffVarReduction_integrable (n : ℕ)
    (f : SchwartzNPointSpace d (n + 1)) (ξ : NPointSpacetime d n) :
    Integrable (fun a : Fin (d + 1) → ℝ =>
      f (fun k μ => a μ + diffVarSection d n ξ k μ)) := by
  -- Bound ‖f(T(a))‖ ≤ C_f * (1+‖a‖)^{-N} using Schwartz decay + ‖T(a)‖ ≥ ‖a‖,
  -- then use integrability of (1+‖·‖)^{-N} on ℝ^{d+1} (JapaneseBracket).
  set N : ℕ := d + 2
  have hN : (finrank ℝ (Fin (d + 1) → ℝ) : ℝ) < (N : ℝ) := by
    simp [N, finrank_fin_fun]
  -- Schwartz seminorm bound: (1+‖x‖)^N * ‖f x‖ ≤ C_f
  set C_f : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f
  have hC_f_nn : 0 ≤ C_f := by positivity
  -- The dominator (1+‖·‖)^{-N} is integrable on ℝ^{d+1}
  have hdom := integrable_one_add_norm (E := Fin (d + 1) → ℝ) (μ := volume) hN
  -- Use mono': ‖integrand‖ ≤ C_f * ‖(1+‖·‖)^{-N}‖ and the RHS is integrable
  refine Integrable.mono' (hdom.smul C_f) ?_ ?_
  · exact (f.continuous.comp (continuous_pi fun k =>
      continuous_pi fun μ => (continuous_apply μ).add continuous_const)).aestronglyMeasurable
  · filter_upwards with a
    set T_a : NPointSpacetime d (n + 1) := fun k μ => a μ + diffVarSection d n ξ k μ
    -- ‖T(a)‖ ≥ ‖a‖ since T(a)(0) = a (diffVarSection at k=0 is zero)
    have hT_norm : ‖a‖ ≤ ‖T_a‖ := by
      calc ‖a‖ = ‖T_a 0‖ := by
            congr 1; ext μ; simp [T_a, diffVarSection_zero]
        _ ≤ ‖T_a‖ := norm_le_pi_norm T_a 0
    -- Schwartz bound with (1+‖x‖): (1+‖T(a)‖)^N * ‖f(T(a))‖ ≤ C_f
    have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
      (m := (N, 0)) (le_refl N) (le_refl 0) f T_a
    rw [norm_iteratedFDeriv_zero] at hSch
    -- (1+‖a‖) ≤ (1+‖T(a)‖) so (1+‖a‖)^N * ‖f(T(a))‖ ≤ C_f
    have h1 : (1 + ‖a‖) ^ N * ‖f T_a‖ ≤ C_f :=
      le_trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) N) (norm_nonneg _)) hSch
    -- Goal: ‖f T_a‖ ≤ (C_f • (1+‖·‖)^{-N}) a = C_f * (1+‖a‖)^{-N}
    show ‖f T_a‖ ≤ C_f * (1 + ‖a‖) ^ (-(N : ℝ))
    have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N := pow_pos (by positivity) N
    rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
    exact le_mul_inv_iff₀ hpos |>.mpr (by rwa [mul_comm])

/-- The fiber integral of a Schwartz function is smooth in ξ.
    Follows from differentiation under the integral sign with
    dominated convergence (the integrand is uniformly Schwartz in a). -/
private theorem diffVarReduction_contDiff (n : ℕ)
    (f : SchwartzNPointSpace d (n + 1)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun ξ : NPointSpacetime d n => ∫ a : Fin (d + 1) → ℝ,
      f (fun k μ => a μ + diffVarSection d n ξ k μ)) := by
  let A := Fin (d + 1) → ℝ
  let X := NPointSpacetime d n
  let Z := NPointSpacetime d (n + 1)
  let S : X →L[ℝ] Z := diffVarSection d n
  let N : ℕ := d + 2
  let T : A → X → Z := fun a ξ k μ => a μ + S ξ k μ
  have hN : (finrank ℝ A : ℝ) < (N : ℝ) := by
    simp [A, N]
  have hdom := integrable_one_add_norm (E := A) (μ := volume) hN
  have hintegrable :
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V) (ξ : X),
        Integrable (fun a : A => g (T a ξ)) := by
    intro V _ _ _ g ξ
    let Cg : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
    refine Integrable.mono' (hdom.smul Cg) ?_ ?_
    · exact ((g.continuous.comp <| by
          refine continuous_pi fun k => continuous_pi fun μ =>
            (continuous_apply μ).add continuous_const)).aestronglyMeasurable
    · filter_upwards with a
      have hT_norm : ‖a‖ ≤ ‖T a ξ‖ := by
        calc
          ‖a‖ = ‖(T a ξ) 0‖ := by
            congr 1
            ext μ
            simp [T, S, diffVarSection]
          _ ≤ ‖T a ξ‖ := norm_le_pi_norm _ 0
      have hmono : 1 + ‖a‖ ≤ 1 + ‖T a ξ‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hT_norm 1
      have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (N, 0)) (le_refl N) (le_refl 0) g (T a ξ)
      rw [norm_iteratedFDeriv_zero] at hSch
      have h1 : (1 + ‖a‖) ^ N * ‖g (T a ξ)‖ ≤ Cg := by
        exact le_trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hmono N) (norm_nonneg _))
          hSch
      show ‖g (T a ξ)‖ ≤ Cg * (1 + ‖a‖) ^ (-(N : ℝ))
      have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N := pow_pos (by positivity) N
      rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
      exact le_mul_inv_iff₀ hpos |>.mpr (by rwa [mul_comm])
  have hderiv :
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V) (ξ : X),
        HasFDerivAt
          (fun ξ' : X => ∫ a : A, g (T a ξ'))
          (((ContinuousLinearMap.compL ℝ X Z V).flip S)
            (∫ a : A, (SchwartzMap.fderivCLM ℝ Z V g) (T a ξ)))
          ξ := by
    intro V _ _ _ g ξ
    let L : (Z →L[ℝ] V) →L[ℝ] (X →L[ℝ] V) :=
      (ContinuousLinearMap.compL ℝ X Z V).flip S
    let g' : SchwartzMap Z (Z →L[ℝ] V) := SchwartzMap.fderivCLM ℝ Z V g
    let Cg' : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g'
    let bound : A → ℝ := fun a => (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N : ℝ))
    have hF_meas :
        ∀ᶠ ξ' in 𝓝 ξ, AEStronglyMeasurable (fun a : A => g (T a ξ')) volume := by
      exact Filter.Eventually.of_forall fun ξ' =>
        ((g.continuous.comp <| by
          refine continuous_pi fun k => continuous_pi fun μ =>
            (continuous_apply μ).add continuous_const)).aestronglyMeasurable
    have hF_int : Integrable (fun a : A => g (T a ξ)) volume := hintegrable V g ξ
    have hF'_meas :
        AEStronglyMeasurable (fun a : A => L (g' (T a ξ))) volume := by
      have hpath : Continuous fun a : A => T a ξ := by
        refine continuous_pi fun k => continuous_pi fun μ =>
          (continuous_apply μ).add continuous_const
      exact (L.continuous.comp (g'.continuous.comp hpath)).aestronglyMeasurable
    have hbound_all :
        ∀ a : A, ∀ ξ' : X, ‖L (g' (T a ξ'))‖ ≤ bound a := by
      intro a ξ'
      have hT_norm : ‖a‖ ≤ ‖T a ξ'‖ := by
        calc
          ‖a‖ = ‖(T a ξ') 0‖ := by
            congr 1
            ext μ
            simp [T, S, diffVarSection]
          _ ≤ ‖T a ξ'‖ := norm_le_pi_norm _ 0
      have hmono : 1 + ‖a‖ ≤ 1 + ‖T a ξ'‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hT_norm 1
      have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (N, 0)) (le_refl N) (le_refl 0) g' (T a ξ')
      rw [norm_iteratedFDeriv_zero] at hSch
      have h1 : ‖g' (T a ξ')‖ ≤ Cg' * (1 + ‖a‖) ^ (-(N : ℝ)) := by
        have hpow : (1 + ‖a‖) ^ N * ‖g' (T a ξ')‖ ≤ Cg' := by
          exact le_trans
            (mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (by positivity) hmono N) (norm_nonneg _))
            hSch
        have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N := pow_pos (by positivity) N
        rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
        exact le_mul_inv_iff₀ hpos |>.mpr (by rwa [mul_comm] at hpow)
      calc
        ‖L (g' (T a ξ'))‖ ≤ ‖L‖ * ‖g' (T a ξ')‖ := ContinuousLinearMap.le_opNorm L (g' (T a ξ'))
        _ ≤ ‖L‖ * (Cg' * (1 + ‖a‖) ^ (-(N : ℝ))) := by gcongr
        _ = (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N : ℝ)) := by
          rw [smul_eq_mul, ← mul_assoc]
        _ = bound a := rfl
    have hbound :
        ∀ᵐ a ∂volume, ∀ ξ' ∈ (Set.univ : Set X), ‖L (g' (T a ξ'))‖ ≤ bound a := by
      exact Filter.Eventually.of_forall fun a ξ' _ => hbound_all a ξ'
    have hbound_int : Integrable bound volume := by
      change Integrable (fun a : A => (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N : ℝ))) volume
      exact hdom.smul (‖L‖ * Cg')
    have hdiff :
        ∀ᵐ a ∂volume,
          ∀ ξ' ∈ (Set.univ : Set X), HasFDerivAt (fun ξ'' : X => g (T a ξ'')) (L (g' (T a ξ'))) ξ' := by
      refine Filter.Eventually.of_forall ?_
      intro a ξ' _
      have hinner : HasFDerivAt (fun ξ'' : X => T a ξ'') S ξ' := by
        change HasFDerivAt (fun ξ'' : X => (fun k μ => a μ) + S ξ'') S ξ'
        exact S.hasFDerivAt.const_add (fun k μ => a μ)
      have hg : HasFDerivAt g (g' (T a ξ')) (T a ξ') := by
        simpa [g', SchwartzMap.fderivCLM_apply] using g.hasFDerivAt (x := T a ξ')
      have hcomp : HasFDerivAt (fun ξ'' : X => g (T a ξ'')) ((g' (T a ξ')).comp S) ξ' := by
        exact hg.comp ξ' hinner
      simpa [L, ContinuousLinearMap.compL_apply] using hcomp
    have hmain :=
      hasFDerivAt_integral_of_dominated_of_fderiv_le
        (μ := (volume : Measure A))
        (s := (Set.univ : Set X))
        (x₀ := ξ)
        (F := fun ξ' a => g (T a ξ'))
        (F' := fun ξ' a => L (g' (T a ξ')))
        Filter.univ_mem hF_meas hF_int hF'_meas hbound hbound_int hdiff
    have hLint : ∫ a : A, L (g' (T a ξ)) = L (∫ a : A, g' (T a ξ)) := by
      exact ContinuousLinearMap.integral_comp_comm L (hintegrable (Z →L[ℝ] V) g' ξ)
    simpa [hLint] using hmain
  have hnat :
      ∀ (m : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V), ContDiff ℝ m (fun ξ : X => ∫ a : A, g (T a ξ)) := by
    intro m
    induction m with
    | zero =>
        intro V _ _ _ g
        exact contDiff_zero.2 <|
          continuous_iff_continuousAt.2 fun ξ => (hderiv V g ξ).continuousAt
    | succ m ihm =>
        intro V _ _ _ g
        let L : (Z →L[ℝ] V) →L[ℝ] (X →L[ℝ] V) :=
          (ContinuousLinearMap.compL ℝ X Z V).flip S
        let g' : SchwartzMap Z (Z →L[ℝ] V) := SchwartzMap.fderivCLM ℝ Z V g
        refine (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ)
          (n := m) (f := fun ξ : X => ∫ a : A, g (T a ξ))).2 ?_
        refine ⟨fun ξ => L (∫ a : A, g' (T a ξ)), ?_, ?_⟩
        · exact L.contDiff.comp (ihm (Z →L[ℝ] V) g')
        · intro ξ
          simpa [L] using (hderiv V g ξ)
  rw [contDiff_infty]
  intro m
  simpa [A, X, Z, S, T] using (hnat m ℂ f)

set_option maxHeartbeats 800000
 /-- The fiber integral of a Schwartz function has Schwartz decay in ξ.
     Follows from dominated convergence: the polynomial weight
     `(1+‖ξ‖)^k` passes inside the integral, and the integrand
     remains uniformly integrable by Schwartz decay of f. -/
private theorem diffVarReduction_decay (n : ℕ)
    (f : SchwartzNPointSpace d (n + 1)) :
    ∀ (k m : ℕ), ∃ (C : ℝ), ∀ (ξ : NPointSpacetime d n),
      ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ m (fun ξ' : NPointSpacetime d n =>
        ∫ a : Fin (d + 1) → ℝ,
          f (fun k' μ => a μ + diffVarSection d n ξ' k' μ)) ξ‖ ≤ C := by
  let A := Fin (d + 1) → ℝ
  let X := NPointSpacetime d n
  let Z := NPointSpacetime d (n + 1)
  let S : X →L[ℝ] Z := diffVarSection d n
  let N : ℕ := d + 2
  let T : A → X → Z := fun a ξ k μ => a μ + S ξ k μ
  have hN : (finrank ℝ A : ℝ) < (N : ℝ) := by
    simp [A, N]
  have hdom := integrable_one_add_norm (E := A) (μ := volume) hN
  have hintegrable :
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V) (ξ : X),
        Integrable (fun a : A => g (T a ξ)) := by
    intro V _ _ _ g ξ
    let Cg : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
    refine Integrable.mono' (hdom.smul Cg) ?_ ?_
    · exact ((g.continuous.comp <| by
          refine continuous_pi fun k => continuous_pi fun μ =>
            (continuous_apply μ).add continuous_const)).aestronglyMeasurable
    · filter_upwards with a
      have hT_norm : ‖a‖ ≤ ‖T a ξ‖ := by
        calc
          ‖a‖ = ‖(T a ξ) 0‖ := by
            congr 1
            ext μ
            simp [T, S, diffVarSection]
          _ ≤ ‖T a ξ‖ := norm_le_pi_norm _ 0
      have hmono : 1 + ‖a‖ ≤ 1 + ‖T a ξ‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hT_norm 1
      have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (N, 0)) (le_refl N) (le_refl 0) g (T a ξ)
      rw [norm_iteratedFDeriv_zero] at hSch
      have h1 : (1 + ‖a‖) ^ N * ‖g (T a ξ)‖ ≤ Cg := by
        exact le_trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hmono N) (norm_nonneg _))
          hSch
      show ‖g (T a ξ)‖ ≤ Cg * (1 + ‖a‖) ^ (-(N : ℝ))
      have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N := pow_pos (by positivity) N
      rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
      exact le_mul_inv_iff₀ hpos |>.mpr (by rwa [mul_comm])
  have hderiv :
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V) (ξ : X),
        HasFDerivAt
          (fun ξ' : X => ∫ a : A, g (T a ξ'))
          (((ContinuousLinearMap.compL ℝ X Z V).flip S)
            (∫ a : A, (SchwartzMap.fderivCLM ℝ Z V g) (T a ξ)))
          ξ := by
    intro V _ _ _ g ξ
    let L : (Z →L[ℝ] V) →L[ℝ] (X →L[ℝ] V) :=
      (ContinuousLinearMap.compL ℝ X Z V).flip S
    let g' : SchwartzMap Z (Z →L[ℝ] V) := SchwartzMap.fderivCLM ℝ Z V g
    let Cg' : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g'
    let bound : A → ℝ := fun a => (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N : ℝ))
    have hF_meas :
        ∀ᶠ ξ' in 𝓝 ξ, AEStronglyMeasurable (fun a : A => g (T a ξ')) volume := by
      exact Filter.Eventually.of_forall fun ξ' =>
        ((g.continuous.comp <| by
          refine continuous_pi fun k => continuous_pi fun μ =>
            (continuous_apply μ).add continuous_const)).aestronglyMeasurable
    have hF_int : Integrable (fun a : A => g (T a ξ)) volume := hintegrable V g ξ
    have hF'_meas :
        AEStronglyMeasurable (fun a : A => L (g' (T a ξ))) volume := by
      have hpath : Continuous fun a : A => T a ξ := by
        refine continuous_pi fun k => continuous_pi fun μ =>
          (continuous_apply μ).add continuous_const
      exact (L.continuous.comp (g'.continuous.comp hpath)).aestronglyMeasurable
    have hbound_all :
        ∀ a : A, ∀ ξ' : X, ‖L (g' (T a ξ'))‖ ≤ bound a := by
      intro a ξ'
      have hT_norm : ‖a‖ ≤ ‖T a ξ'‖ := by
        calc
          ‖a‖ = ‖(T a ξ') 0‖ := by
            congr 1
            ext μ
            simp [T, S, diffVarSection]
          _ ≤ ‖T a ξ'‖ := norm_le_pi_norm _ 0
      have hmono : 1 + ‖a‖ ≤ 1 + ‖T a ξ'‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hT_norm 1
      have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (N, 0)) (le_refl N) (le_refl 0) g' (T a ξ')
      rw [norm_iteratedFDeriv_zero] at hSch
      have h1 : ‖g' (T a ξ')‖ ≤ Cg' * (1 + ‖a‖) ^ (-(N : ℝ)) := by
        have hpow : (1 + ‖a‖) ^ N * ‖g' (T a ξ')‖ ≤ Cg' := by
          exact le_trans
            (mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (by positivity) hmono N) (norm_nonneg _))
            hSch
        have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N := pow_pos (by positivity) N
        rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
        exact le_mul_inv_iff₀ hpos |>.mpr (by rwa [mul_comm] at hpow)
      calc
        ‖L (g' (T a ξ'))‖ ≤ ‖L‖ * ‖g' (T a ξ')‖ := ContinuousLinearMap.le_opNorm L (g' (T a ξ'))
        _ ≤ ‖L‖ * (Cg' * (1 + ‖a‖) ^ (-(N : ℝ))) := by gcongr
        _ = (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N : ℝ)) := by
          rw [smul_eq_mul, ← mul_assoc]
        _ = bound a := rfl
    have hbound :
        ∀ᵐ a ∂volume, ∀ ξ' ∈ (Set.univ : Set X), ‖L (g' (T a ξ'))‖ ≤ bound a := by
      exact Filter.Eventually.of_forall fun a ξ' _ => hbound_all a ξ'
    have hbound_int : Integrable bound volume := by
      change Integrable (fun a : A => (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N : ℝ))) volume
      exact hdom.smul (‖L‖ * Cg')
    have hdiff :
        ∀ᵐ a ∂volume,
          ∀ ξ' ∈ (Set.univ : Set X),
            HasFDerivAt (fun ξ'' : X => g (T a ξ'')) (L (g' (T a ξ'))) ξ' := by
      refine Filter.Eventually.of_forall ?_
      intro a ξ' _
      have hinner : HasFDerivAt (fun ξ'' : X => T a ξ'') S ξ' := by
        change HasFDerivAt (fun ξ'' : X => (fun k μ => a μ) + S ξ'') S ξ'
        exact S.hasFDerivAt.const_add (fun k μ => a μ)
      have hg : HasFDerivAt g (g' (T a ξ')) (T a ξ') := by
        simpa [g', SchwartzMap.fderivCLM_apply] using g.hasFDerivAt (x := T a ξ')
      have hcomp : HasFDerivAt (fun ξ'' : X => g (T a ξ'')) ((g' (T a ξ')).comp S) ξ' := by
        exact hg.comp ξ' hinner
      simpa [L, ContinuousLinearMap.compL_apply] using hcomp
    have hmain :=
      hasFDerivAt_integral_of_dominated_of_fderiv_le
        (μ := (volume : Measure A))
        (s := (Set.univ : Set X))
        (x₀ := ξ)
        (F := fun ξ' a => g (T a ξ'))
        (F' := fun ξ' a => L (g' (T a ξ')))
        Filter.univ_mem hF_meas hF_int hF'_meas hbound hbound_int hdiff
    have hLint : ∫ a : A, L (g' (T a ξ)) = L (∫ a : A, g' (T a ξ)) := by
      exact ContinuousLinearMap.integral_comp_comm L (hintegrable (Z →L[ℝ] V) g' ξ)
    simpa [hLint] using hmain
  have hnat :
      ∀ (m : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V), ContDiff ℝ m (fun ξ : X => ∫ a : A, g (T a ξ)) := by
    intro m
    induction m with
    | zero =>
        intro V _ _ _ g
        exact contDiff_zero.2 <|
          continuous_iff_continuousAt.2 fun ξ => (hderiv V g ξ).continuousAt
    | succ m ihm =>
        intro V _ _ _ g
        let L : (Z →L[ℝ] V) →L[ℝ] (X →L[ℝ] V) :=
          (ContinuousLinearMap.compL ℝ X Z V).flip S
        let g' : SchwartzMap Z (Z →L[ℝ] V) := SchwartzMap.fderivCLM ℝ Z V g
        refine (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ)
          (n := m) (f := fun ξ : X => ∫ a : A, g (T a ξ))).2 ?_
        refine ⟨fun ξ => L (∫ a : A, g' (T a ξ)), ?_, ?_⟩
        · exact L.contDiff.comp (ihm (Z →L[ℝ] V) g')
        · intro ξ
          simpa [L] using (hderiv V g ξ)
  have hcontDiff :
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V), ContDiff ℝ (⊤ : ℕ∞) (fun ξ : X => ∫ a : A, g (T a ξ)) := by
    intro V _ _ _ g
    rw [contDiff_infty]
    intro m
    exact hnat m V g
  have hzero :
      ∀ (k : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V),
        ∃ C : ℝ, ∀ ξ : X, (1 + ‖ξ‖) ^ k * ‖∫ a : A, g (T a ξ)‖ ≤ C := by
    intro k V _ _ _ g
    let M : ℕ := k + N
    let Cg : ℝ := 2 ^ M * (Finset.Iic (M, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
    let C0 : ℝ := ∫ a : A, (1 + ‖a‖) ^ (-(N : ℝ))
    refine ⟨((2 : ℝ) ^ k * Cg) * C0, ?_⟩
    intro ξ
    have hpath : Continuous fun a : A => T a ξ := by
      refine continuous_pi fun k => continuous_pi fun μ =>
        (continuous_apply μ).add continuous_const
    let F : A → V := fun a => g (T a ξ)
    let I : ℝ := ∫ a : A, ‖F a‖
    have hnorm :
        ‖∫ a : A, g (T a ξ)‖ ≤ I := by
      simpa using
        (norm_integral_le_integral_norm (μ := (volume : Measure A))
          (f := F))
    let lower : A → ℝ := fun a => (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖
    let upper : A → ℝ := fun a => ((2 : ℝ) ^ k * Cg) * (1 + ‖a‖) ^ (-(N : ℝ))
    have hmajor_integrable :
        Integrable upper volume := by
      change Integrable (fun a : A => (((2 : ℝ) ^ k * Cg) : ℝ) • (1 + ‖a‖) ^ (-(N : ℝ))) volume
      exact hdom.smul (((2 : ℝ) ^ k) * Cg)
    have hbound_point :
        ∀ a : A,
          lower a ≤ upper a := by
      intro a
      dsimp [lower, upper]
      have hT_norm : ‖a‖ ≤ ‖T a ξ‖ := by
        calc
          ‖a‖ = ‖(T a ξ) 0‖ := by
            congr 1
            ext μ
            simp [T, S, diffVarSection]
          _ ≤ ‖T a ξ‖ := norm_le_pi_norm _ 0
      have hξ_coord :
          ∀ i : Fin n, ‖ξ i‖ ≤ 2 * ‖T a ξ‖ := by
        intro i
        have hdiff :
            ξ i = (T a ξ i.succ) - (T a ξ i.castSucc) := by
          ext μ
          have hs := diffVarSection_succ (d := d) n ξ i μ
          dsimp [T, S]
          linarith
        calc
          ‖ξ i‖ = ‖(T a ξ i.succ) - (T a ξ i.castSucc)‖ := by rw [hdiff]
          _ ≤ ‖T a ξ i.succ‖ + ‖T a ξ i.castSucc‖ := norm_sub_le _ _
          _ ≤ ‖T a ξ‖ + ‖T a ξ‖ := by
                gcongr <;> exact norm_le_pi_norm _ _
          _ = 2 * ‖T a ξ‖ := by ring
      have hξ_norm : ‖ξ‖ ≤ 2 * ‖T a ξ‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
        intro i
        exact hξ_coord i
      have hξ_mono : 1 + ‖ξ‖ ≤ 2 * (1 + ‖T a ξ‖) := by
        linarith
      have ha_mono : 1 + ‖a‖ ≤ 1 + ‖T a ξ‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hT_norm 1
      have hprod :
          (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N ≤ (2 : ℝ) ^ k * (1 + ‖T a ξ‖) ^ M := by
        have hpow1 : (1 + ‖ξ‖) ^ k ≤ (2 * (1 + ‖T a ξ‖)) ^ k := by
          exact pow_le_pow_left₀ (by positivity) hξ_mono k
        have hpow2 : (1 + ‖a‖) ^ N ≤ (1 + ‖T a ξ‖) ^ N := by
          exact pow_le_pow_left₀ (by positivity) ha_mono N
        calc
          (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N
              ≤ (2 * (1 + ‖T a ξ‖)) ^ k * (1 + ‖T a ξ‖) ^ N := by
                    exact mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
          _ = (2 : ℝ) ^ k * ((1 + ‖T a ξ‖) ^ k * (1 + ‖T a ξ‖) ^ N) := by
                rw [mul_pow, ← mul_assoc]
          _ = (2 : ℝ) ^ k * (1 + ‖T a ξ‖) ^ M := by
                rw [show M = k + N by rfl, ← pow_add]
      have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (M, 0)) (le_refl M) (le_refl 0) g (T a ξ)
      rw [norm_iteratedFDeriv_zero] at hSch
      have h1 :
          (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N * ‖g (T a ξ)‖ ≤ (2 : ℝ) ^ k * Cg := by
        calc
          (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N * ‖g (T a ξ)‖
              = ((1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N) * ‖g (T a ξ)‖ := by ring
          _ ≤ ((2 : ℝ) ^ k * (1 + ‖T a ξ‖) ^ M) * ‖g (T a ξ)‖ := by
                exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
          _ = (2 : ℝ) ^ k * ((1 + ‖T a ξ‖) ^ M * ‖g (T a ξ)‖) := by ring
          _ ≤ (2 : ℝ) ^ k * Cg := by
                exact mul_le_mul_of_nonneg_left hSch (by positivity)
      have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N := pow_pos (by positivity) N
      rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
      have h1' :
          (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖ * (1 + ‖a‖) ^ N ≤ (2 : ℝ) ^ k * Cg := by
        calc
          (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖ * (1 + ‖a‖) ^ N
              = (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N * ‖g (T a ξ)‖ := by ring
          _ ≤ (2 : ℝ) ^ k * Cg := h1
      exact (le_mul_inv_iff₀ hpos).2 h1'
    have hlower_integrable :
        Integrable lower volume := by
      refine hmajor_integrable.mono' ?_ ?_
      · exact (continuous_const.mul ((g.continuous.comp hpath).norm)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall ?_
        intro a
        have hnonneg : 0 ≤ lower a := by
          dsimp [lower]
          positivity
        have habs :
            ‖lower a‖ = lower a := by
          exact Real.norm_of_nonneg hnonneg
        rw [habs]
        exact hbound_point a
    have hbound_ae :
        ∀ᵐ a : A ∂volume,
          lower a ≤ upper a := by
      exact Filter.Eventually.of_forall hbound_point
    have hint_eq :
        ∫ a : A, upper a =
          ((2 : ℝ) ^ k * Cg) * C0 := by
      dsimp [upper]
      rw [MeasureTheory.integral_const_mul]
    have hmono_int :
        ∫ a : A, lower a ≤ ∫ a : A, upper a := by
      exact MeasureTheory.integral_mono_ae
        (μ := (volume : Measure A)) hlower_integrable hmajor_integrable hbound_ae
    have hbase_nonneg : 0 ≤ 1 + ‖ξ‖ := by
      exact add_nonneg zero_le_one (norm_nonneg ξ)
    have hk_nonneg : 0 ≤ (1 + ‖ξ‖) ^ k := by
      exact pow_nonneg hbase_nonneg k
    have hstep2 :
        (1 + ‖ξ‖) ^ k * I =
          ∫ a : A, ((1 + ‖ξ‖) ^ k) * ‖F a‖ := by
      dsimp [I]
      exact (MeasureTheory.integral_const_mul ((1 + ‖ξ‖) ^ k)
        (fun a : A => ‖F a‖)).symm
    have hstep3 :
        ∫ a : A, ((1 + ‖ξ‖) ^ k) * ‖F a‖ ≤ ∫ a : A, upper a := by
      change ∫ a : A, lower a ≤ ∫ a : A, upper a
      exact hmono_int
    let L : ℝ := (1 + ‖ξ‖) ^ k * ‖∫ a : A, g (T a ξ)‖
    let K : ℝ := (1 + ‖ξ‖) ^ k * I
    have hstep12 :
        L ≤ K := by
      dsimp [L, K]
      exact mul_le_mul_of_nonneg_left hnorm hk_nonneg
    exact hstep12.trans ((hstep2.trans_le hstep3).trans_eq hint_eq)
  have hdecay :
      ∀ (k m : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (g : SchwartzMap Z V),
        ∃ C : ℝ, ∀ ξ : X,
          ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ m (fun ξ' : X => ∫ a : A, g (T a ξ')) ξ‖ ≤ C := by
    intro k m
    induction m with
    | zero =>
        intro V _ _ _ g
        obtain ⟨C, hC⟩ := hzero k V g
        refine ⟨C, ?_⟩
        intro ξ
        calc
          ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ 0 (fun ξ' : X => ∫ a : A, g (T a ξ')) ξ‖
              = ‖ξ‖ ^ k * ‖∫ a : A, g (T a ξ)‖ := by
                  rw [norm_iteratedFDeriv_zero]
          _ ≤ (1 + ‖ξ‖) ^ k * ‖∫ a : A, g (T a ξ)‖ := by
                have hξ_nonneg : 0 ≤ ‖ξ‖ := norm_nonneg _
                have hξ_le : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith
                exact mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ hξ_nonneg hξ_le k) (norm_nonneg _)
          _ ≤ C := hC ξ
    | succ m ihm =>
        intro V _ _ _ g
        let g' : SchwartzMap Z (Z →L[ℝ] V) := SchwartzMap.fderivCLM ℝ Z V g
        obtain ⟨C, hC⟩ := ihm (Z →L[ℝ] V) g'
        let L : (Z →L[ℝ] V) →L[ℝ] (X →L[ℝ] V) :=
          (ContinuousLinearMap.compL ℝ X Z V).flip S
        let C' : ℝ := ‖L‖ * C
        refine ⟨C', ?_⟩
        intro ξ
        have hEq :
            fderiv ℝ (fun ξ : X => ∫ a : A, g (T a ξ)) =
              fun ξ => L (∫ a : A, g' (T a ξ)) := by
          funext ξ'
          simpa [L, ContinuousLinearMap.compL_apply] using (hderiv V g ξ').fderiv
        calc
          ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) (fun ξ' : X => ∫ a : A, g (T a ξ')) ξ‖
              = ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ m
                    (fderiv ℝ (fun ξ' : X => ∫ a : A, g (T a ξ'))) ξ‖ := by
                    rw [norm_iteratedFDeriv_fderiv]
          _ = ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ m (L ∘ fun ξ : X => ∫ a : A, g' (T a ξ)) ξ‖ := by
                have hcompEq : (fun ξ : X => L (∫ a : A, g' (T a ξ))) =
                    L ∘ fun ξ : X => ∫ a : A, g' (T a ξ) := rfl
                rw [hEq, hcompEq]
          _ ≤ ‖ξ‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ m (fun ξ : X => ∫ a : A, g' (T a ξ)) ξ‖) := by
                gcongr
                exact L.norm_iteratedFDeriv_comp_left
                  ((hcontDiff (Z →L[ℝ] V) g').contDiffAt) (by exact_mod_cast le_top)
          _ = ‖L‖ * (‖ξ‖ ^ k * ‖iteratedFDeriv ℝ m (fun ξ : X => ∫ a : A, g' (T a ξ)) ξ‖) := by
                ring
          _ ≤ ‖L‖ * C := by
                gcongr
                exact hC ξ
          _ = C' := by rfl
  intro k m
  simpa [A, X, Z, S, T] using hdecay k m ℂ f

set_option maxHeartbeats 200000

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Continuity of the fiber-integral map in the Schwartz topology. -/
private theorem diffVarReduction_cont (n : ℕ) :
    Continuous (fun f : SchwartzNPointSpace d (n + 1) =>
      (⟨fun ξ => ∫ a : Fin (d + 1) → ℝ,
          f (fun k μ => a μ + diffVarSection d n ξ k μ),
        diffVarReduction_contDiff d n f,
        diffVarReduction_decay d n f⟩ : SchwartzNPointSpace d n)) := by
  letI : SMulCommClass ℝ ℝ ℂ :=
    ⟨fun a b z => by
      simp [mul_comm, mul_left_comm]⟩
  let A : SchwartzNPointSpace d (n + 1) →L[ℝ] SchwartzNPointSpace d n :=
    SchwartzMap.mkCLM (𝕜 := ℝ) (𝕜' := ℝ)
      (fun f ξ => ∫ a : Fin (d + 1) → ℝ,
        f (fun k μ => a μ + diffVarSection d n ξ k μ))
      (fun f g ξ => by
        show (∫ a : Fin (d + 1) → ℝ,
            (f + g) (fun k μ => a μ + diffVarSection d n ξ k μ)) =
          (∫ a : Fin (d + 1) → ℝ,
            f (fun k μ => a μ + diffVarSection d n ξ k μ)) +
            (∫ a : Fin (d + 1) → ℝ,
              g (fun k μ => a μ + diffVarSection d n ξ k μ))
        simp only [SchwartzMap.add_apply]
        exact integral_add
          (diffVarReduction_integrable d n f ξ)
          (diffVarReduction_integrable d n g ξ))
      (fun c f ξ => by
        show (∫ a : Fin (d + 1) → ℝ,
            (c • f) (fun k μ => a μ + diffVarSection d n ξ k μ)) =
          c • ∫ a : Fin (d + 1) → ℝ,
            f (fun k μ => a μ + diffVarSection d n ξ k μ)
        simpa [SchwartzMap.smul_apply] using
          (integral_smul c
            (fun a : Fin (d + 1) → ℝ =>
              f (fun k μ => a μ + diffVarSection d n ξ k μ))))
      (fun f => diffVarReduction_contDiff d n f) fun N => by
        let A0 := Fin (d + 1) → ℝ
        let X := NPointSpacetime d n
        let Z := NPointSpacetime d (n + 1)
        let S : X →L[ℝ] Z := diffVarSection d n
        let T : A0 → X → Z := fun a ξ k μ => a μ + S ξ k μ
        let N0 : ℕ := d + 2
        have hN0 : (finrank ℝ A0 : ℝ) < (N0 : ℝ) := by
          simp [A0, N0]
        have hdom :
            Integrable (fun a : A0 => (1 + ‖a‖) ^ (-(N0 : ℝ))) volume := by
          exact integrable_one_add_norm (E := A0) (μ := volume) hN0
        have hintegrable :
            ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
              (g : SchwartzMap Z V) (ξ : X),
              Integrable (fun a : A0 => g (T a ξ)) volume := by
          intro V _ _ _ g ξ
          let Cg : ℝ := 2 ^ N0 * (Finset.Iic (N0, 0)).sup
            (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
          refine Integrable.mono' (hdom.smul Cg) ?_ ?_
          · exact (g.continuous.comp (continuous_pi fun k =>
              continuous_pi fun μ => (continuous_apply μ).add continuous_const)).aestronglyMeasurable
          · filter_upwards with a
            have hT_norm : ‖a‖ ≤ ‖T a ξ‖ := by
              calc
                ‖a‖ = ‖(T a ξ) 0‖ := by
                  congr 1
                  ext μ
                  have hzero : S ξ 0 μ = 0 := by
                    change diffVarSection d n ξ 0 μ = 0
                    exact diffVarSection_zero (d := d) (n := n) ξ μ
                  change a μ = a μ + S ξ 0 μ
                  simpa [hzero]
                _ ≤ ‖T a ξ‖ := norm_le_pi_norm _ 0
            have hmono : 1 + ‖a‖ ≤ 1 + ‖T a ξ‖ := by
              simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hT_norm 1
            have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
              (m := (N0, 0)) (le_refl N0) (le_refl 0) g (T a ξ)
            rw [norm_iteratedFDeriv_zero] at hSch
            have h1 : (1 + ‖a‖) ^ N0 * ‖g (T a ξ)‖ ≤ Cg := by
              exact le_trans
                (mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ (by positivity) hmono N0) (norm_nonneg _))
                hSch
            show ‖g (T a ξ)‖ ≤ Cg * (1 + ‖a‖) ^ (-(N0 : ℝ))
            have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N0 := pow_pos (by positivity) N0
            rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
            exact le_mul_inv_iff₀ hpos |>.mpr (by rwa [mul_comm])
        have hderiv :
            ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
              (g : SchwartzMap Z V) (ξ : X),
              HasFDerivAt
                (fun ξ' : X => ∫ a : A0, g (T a ξ'))
                (((ContinuousLinearMap.compL ℝ X Z V).flip S)
                  (∫ a : A0, (SchwartzMap.fderivCLM ℝ Z V g) (T a ξ)))
                ξ := by
          intro V _ _ _ g ξ
          let L : (Z →L[ℝ] V) →L[ℝ] (X →L[ℝ] V) :=
            (ContinuousLinearMap.compL ℝ X Z V).flip S
          let g' : SchwartzMap Z (Z →L[ℝ] V) := SchwartzMap.fderivCLM ℝ Z V g
          let Cg' : ℝ := 2 ^ N0 * (Finset.Iic (N0, 0)).sup
            (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g'
          let bound : A0 → ℝ := fun a => (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N0 : ℝ))
          have hF_meas :
              ∀ᶠ ξ' in 𝓝 ξ, AEStronglyMeasurable (fun a : A0 => g (T a ξ')) volume := by
            exact Filter.Eventually.of_forall fun ξ' =>
              ((g.continuous.comp <| by
                refine continuous_pi fun k => continuous_pi fun μ =>
                  (continuous_apply μ).add continuous_const)).aestronglyMeasurable
          have hF_int : Integrable (fun a : A0 => g (T a ξ)) volume := hintegrable V g ξ
          have hF'_meas :
              AEStronglyMeasurable (fun a : A0 => L (g' (T a ξ))) volume := by
            have hpath : Continuous fun a : A0 => T a ξ := by
              refine continuous_pi fun k => continuous_pi fun μ =>
                (continuous_apply μ).add continuous_const
            exact (L.continuous.comp (g'.continuous.comp hpath)).aestronglyMeasurable
          have hbound_all :
              ∀ a : A0, ∀ ξ' : X, ‖L (g' (T a ξ'))‖ ≤ bound a := by
            intro a ξ'
            have hT_norm : ‖a‖ ≤ ‖T a ξ'‖ := by
              calc
                ‖a‖ = ‖(T a ξ') 0‖ := by
                  congr 1
                  ext μ
                  have hzero : S ξ' 0 μ = 0 := by
                    change diffVarSection d n ξ' 0 μ = 0
                    exact diffVarSection_zero (d := d) (n := n) ξ' μ
                  change a μ = a μ + S ξ' 0 μ
                  simpa [hzero]
                _ ≤ ‖T a ξ'‖ := norm_le_pi_norm _ 0
            have hmono : 1 + ‖a‖ ≤ 1 + ‖T a ξ'‖ := by
              simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hT_norm 1
            have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
              (m := (N0, 0)) (le_refl N0) (le_refl 0) g' (T a ξ')
            rw [norm_iteratedFDeriv_zero] at hSch
            have h1 : ‖g' (T a ξ')‖ ≤ Cg' * (1 + ‖a‖) ^ (-(N0 : ℝ)) := by
              have hpow : (1 + ‖a‖) ^ N0 * ‖g' (T a ξ')‖ ≤ Cg' := by
                exact le_trans
                  (mul_le_mul_of_nonneg_right
                    (pow_le_pow_left₀ (by positivity) hmono N0) (norm_nonneg _))
                  hSch
              have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N0 := pow_pos (by positivity) N0
              rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
              exact le_mul_inv_iff₀ hpos |>.mpr (by rwa [mul_comm] at hpow)
            calc
              ‖L (g' (T a ξ'))‖ ≤ ‖L‖ * ‖g' (T a ξ')‖ := ContinuousLinearMap.le_opNorm L _
              _ ≤ ‖L‖ * (Cg' * (1 + ‖a‖) ^ (-(N0 : ℝ))) := by gcongr
              _ = (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N0 : ℝ)) := by
                    rw [smul_eq_mul, ← mul_assoc]
              _ = bound a := rfl
          have hbound :
              ∀ᵐ a ∂volume, ∀ ξ' ∈ (Set.univ : Set X), ‖L (g' (T a ξ'))‖ ≤ bound a := by
            exact Filter.Eventually.of_forall fun a ξ' _ => hbound_all a ξ'
          have hbound_int : Integrable bound volume := by
            change Integrable (fun a : A0 => (‖L‖ * Cg') • (1 + ‖a‖) ^ (-(N0 : ℝ))) volume
            exact hdom.smul (‖L‖ * Cg')
          have hdiff :
              ∀ᵐ a ∂volume,
                ∀ ξ' ∈ (Set.univ : Set X),
                  HasFDerivAt (fun ξ'' : X => g (T a ξ'')) (L (g' (T a ξ'))) ξ' := by
            refine Filter.Eventually.of_forall ?_
            intro a ξ' _
            have hinner : HasFDerivAt (fun ξ'' : X => T a ξ'') S ξ' := by
              change HasFDerivAt (fun ξ'' : X => (fun k μ => a μ) + S ξ'') S ξ'
              exact S.hasFDerivAt.const_add (fun k μ => a μ)
            have hg : HasFDerivAt g (g' (T a ξ')) (T a ξ') := by
              simpa [g', SchwartzMap.fderivCLM_apply] using g.hasFDerivAt (x := T a ξ')
            have hcomp :
                HasFDerivAt (fun ξ'' : X => g (T a ξ'')) ((g' (T a ξ')).comp S) ξ' := by
              exact hg.comp ξ' hinner
            simpa [L, ContinuousLinearMap.compL_apply] using hcomp
          have hmain :=
            hasFDerivAt_integral_of_dominated_of_fderiv_le
              (μ := (volume : Measure A0))
              (s := (Set.univ : Set X))
              (x₀ := ξ)
              (F := fun ξ' a => g (T a ξ'))
              (F' := fun ξ' a => L (g' (T a ξ')))
              Filter.univ_mem hF_meas hF_int hF'_meas hbound hbound_int hdiff
          have hLint : ∫ a : A0, L (g' (T a ξ)) = L (∫ a : A0, g' (T a ξ)) := by
            exact ContinuousLinearMap.integral_comp_comm L (hintegrable (Z →L[ℝ] V) g' ξ)
          simpa [hLint] using hmain
        have hnat :
            ∀ (m : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
              [CompleteSpace V] (g : SchwartzMap Z V),
              ContDiff ℝ m (fun ξ : X => ∫ a : A0, g (T a ξ)) := by
          intro m
          induction m with
          | zero =>
              intro V _ _ _ g
              exact contDiff_zero.2 <|
                continuous_iff_continuousAt.2 fun ξ => (hderiv V g ξ).continuousAt
          | succ m ihm =>
              intro V _ _ _ g
              let L : (Z →L[ℝ] V) →L[ℝ] (X →L[ℝ] V) :=
                (ContinuousLinearMap.compL ℝ X Z V).flip S
              let g' : SchwartzMap Z (Z →L[ℝ] V) := SchwartzMap.fderivCLM ℝ Z V g
              refine (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ)
                (n := m) (f := fun ξ : X => ∫ a : A0, g (T a ξ))).2 ?_
              refine ⟨fun ξ => L (∫ a : A0, g' (T a ξ)), ?_, ?_⟩
              · exact L.contDiff.comp (ihm (Z →L[ℝ] V) g')
              · intro ξ
                simpa [L] using (hderiv V g ξ)
        have hbound :
            ∀ (k m : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
              [CompleteSpace V],
              ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
                ∀ (g : SchwartzMap Z V) (ξ : X),
                  ‖ξ‖ ^ k *
                      ‖iteratedFDeriv ℝ m
                          (fun ξ' : X => ∫ a : A0, g (T a ξ')) ξ‖ ≤
                    C * (s.sup (schwartzSeminormFamily ℝ Z V)) g := by
          intro k m
          induction m with
          | zero =>
              intro V _ _ _
              let M : ℕ := k + N0
              let s : Finset (ℕ × ℕ) := Finset.Iic (M, 0)
              let C0 : ℝ := ∫ a : A0, (1 + ‖a‖) ^ (-(N0 : ℝ))
              let Cbase : ℝ := (2 : ℝ) ^ k * 2 ^ M
              let C : ℝ := Cbase * C0
              refine ⟨s, C, by positivity, ?_⟩
              intro g ξ
              have hpath : Continuous fun a : A0 => T a ξ := by
                refine continuous_pi fun k => continuous_pi fun μ =>
                  (continuous_apply μ).add continuous_const
              have hnorm :
                  ‖∫ a : A0, g (T a ξ)‖ ≤ ∫ a : A0, ‖g (T a ξ)‖ := by
                simpa using
                  (norm_integral_le_integral_norm (μ := (volume : Measure A0))
                    (f := fun a : A0 => g (T a ξ)))
              have hmajor_integrable :
                  Integrable
                    (fun a : A0 => Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g *
                      (1 + ‖a‖) ^ (-(N0 : ℝ))) volume := by
                change Integrable
                  (fun a : A0 =>
                    ((Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g) : ℝ) •
                      (1 + ‖a‖) ^ (-(N0 : ℝ))) volume
                exact hdom.smul (Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g)
              have hbound_point :
                  ∀ a : A0,
                    (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖ ≤
                      Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g *
                        (1 + ‖a‖) ^ (-(N0 : ℝ)) := by
                intro a
                have hT_norm : ‖a‖ ≤ ‖T a ξ‖ := by
                  calc
                    ‖a‖ = ‖(T a ξ) 0‖ := by
                      congr 1
                      ext μ
                      have hzero : S ξ 0 μ = 0 := by
                        change diffVarSection d n ξ 0 μ = 0
                        exact diffVarSection_zero (d := d) (n := n) ξ μ
                      change a μ = a μ + S ξ 0 μ
                      simpa [hzero]
                    _ ≤ ‖T a ξ‖ := norm_le_pi_norm _ 0
                have hξ_coord :
                    ∀ i : Fin n, ‖ξ i‖ ≤ 2 * ‖T a ξ‖ := by
                  intro i
                  have hdiff :
                      ξ i = (T a ξ i.succ) - (T a ξ i.castSucc) := by
                    ext μ
                    have hs := diffVarSection_succ (d := d) n ξ i μ
                    dsimp [T, S]
                    linarith
                  calc
                    ‖ξ i‖ = ‖(T a ξ i.succ) - (T a ξ i.castSucc)‖ := by rw [hdiff]
                    _ ≤ ‖T a ξ i.succ‖ + ‖T a ξ i.castSucc‖ := norm_sub_le _ _
                    _ ≤ ‖T a ξ‖ + ‖T a ξ‖ := by
                          gcongr <;> exact norm_le_pi_norm _ _
                    _ = 2 * ‖T a ξ‖ := by ring
                have hξ_norm : ‖ξ‖ ≤ 2 * ‖T a ξ‖ := by
                  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
                  intro i
                  exact hξ_coord i
                have hξ_mono : 1 + ‖ξ‖ ≤ 2 * (1 + ‖T a ξ‖) := by
                  linarith
                have ha_mono : 1 + ‖a‖ ≤ 1 + ‖T a ξ‖ := by
                  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hT_norm 1
                have hprod :
                    (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N0 ≤
                      (2 : ℝ) ^ k * (1 + ‖T a ξ‖) ^ M := by
                  have hpow1 : (1 + ‖ξ‖) ^ k ≤ (2 * (1 + ‖T a ξ‖)) ^ k := by
                    exact pow_le_pow_left₀ (by positivity) hξ_mono k
                  have hpow2 : (1 + ‖a‖) ^ N0 ≤ (1 + ‖T a ξ‖) ^ N0 := by
                    exact pow_le_pow_left₀ (by positivity) ha_mono N0
                  calc
                    (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N0
                        ≤ (2 * (1 + ‖T a ξ‖)) ^ k * (1 + ‖T a ξ‖) ^ N0 := by
                              exact mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
                    _ = (2 : ℝ) ^ k * ((1 + ‖T a ξ‖) ^ k * (1 + ‖T a ξ‖) ^ N0) := by
                          rw [mul_pow, ← mul_assoc]
                    _ = (2 : ℝ) ^ k * (1 + ‖T a ξ‖) ^ M := by
                          rw [show M = k + N0 by rfl, ← pow_add]
                have hSch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
                  (m := (M, 0)) (le_refl M) (le_refl 0) g (T a ξ)
                rw [norm_iteratedFDeriv_zero] at hSch
                have h1 :
                    (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N0 * ‖g (T a ξ)‖ ≤
                      Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g := by
                  calc
                    (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N0 * ‖g (T a ξ)‖
                        = ((1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N0) * ‖g (T a ξ)‖ := by ring
                    _ ≤ ((2 : ℝ) ^ k * (1 + ‖T a ξ‖) ^ M) * ‖g (T a ξ)‖ := by
                          exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
                    _ = (2 : ℝ) ^ k * ((1 + ‖T a ξ‖) ^ M * ‖g (T a ξ)‖) := by ring
                    _ ≤ (2 : ℝ) ^ k *
                          (2 ^ M * (s.sup (schwartzSeminormFamily ℝ Z V)) g) := by
                          exact mul_le_mul_of_nonneg_left hSch (by positivity)
                    _ = Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g := by
                          dsimp [Cbase]
                          ring
                have hpos : (0 : ℝ) < (1 + ‖a‖) ^ N0 := pow_pos (by positivity) N0
                rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
                have h1' :
                    (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖ * (1 + ‖a‖) ^ N0 ≤
                      Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g := by
                  calc
                    (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖ * (1 + ‖a‖) ^ N0
                        = (1 + ‖ξ‖) ^ k * (1 + ‖a‖) ^ N0 * ‖g (T a ξ)‖ := by ring
                    _ ≤ Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g := h1
                exact (le_mul_inv_iff₀ hpos).2 h1'
              have hlower_integrable :
                  Integrable (fun a : A0 => (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖) volume := by
                refine hmajor_integrable.mono' ?_ ?_
                · exact (continuous_const.mul ((g.continuous.comp hpath).norm)).aestronglyMeasurable
                · refine Filter.Eventually.of_forall ?_
                  intro a
                  have hnonneg : 0 ≤ (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖ := by positivity
                  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
                  exact hbound_point a
              calc
                ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ 0 (fun ξ' : X => ∫ a : A0, g (T a ξ')) ξ‖
                    = ‖ξ‖ ^ k * ‖∫ a : A0, g (T a ξ)‖ := by
                        rw [norm_iteratedFDeriv_zero]
                _ ≤ (1 + ‖ξ‖) ^ k * ‖∫ a : A0, g (T a ξ)‖ := by
                      have hξ_nonneg : 0 ≤ ‖ξ‖ := norm_nonneg _
                      have hξ_le : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith
                      exact mul_le_mul_of_nonneg_right
                        (pow_le_pow_left₀ hξ_nonneg hξ_le k) (norm_nonneg _)
                _ ≤ (1 + ‖ξ‖) ^ k * ∫ a : A0, ‖g (T a ξ)‖ := by
                      exact mul_le_mul_of_nonneg_left hnorm (by positivity)
                _ = ∫ a : A0, (1 + ‖ξ‖) ^ k * ‖g (T a ξ)‖ := by
                      rw [← integral_const_mul]
                _ ≤ ∫ a : A0, Cbase * (s.sup (schwartzSeminormFamily ℝ Z V)) g *
                        (1 + ‖a‖) ^ (-(N0 : ℝ)) := by
                      refine MeasureTheory.integral_mono_ae hlower_integrable hmajor_integrable ?_
                      exact Filter.Eventually.of_forall hbound_point
                _ = C * (s.sup (schwartzSeminormFamily ℝ Z V)) g := by
                      dsimp [C, C0, Cbase]
                      rw [MeasureTheory.integral_const_mul]
                      ring
          | succ m ihm =>
              intro V _ _ _
              obtain ⟨s, C, hC, hCbound⟩ := ihm (Z →L[ℝ] V)
              let L : (Z →L[ℝ] V) →L[ℝ] (X →L[ℝ] V) :=
                (ContinuousLinearMap.compL ℝ X Z V).flip S
              let q : Seminorm ℝ (SchwartzMap Z V) :=
                (s.sup (schwartzSeminormFamily ℝ Z (Z →L[ℝ] V))).comp
                  (SchwartzMap.fderivCLM ℝ Z V).toLinearMap
              have hq_cont : Continuous q := by
                change Continuous (fun h : SchwartzMap Z V =>
                  (s.sup (schwartzSeminormFamily ℝ Z (Z →L[ℝ] V)))
                    (SchwartzMap.fderivCLM ℝ Z V h))
                exact (((schwartz_withSeminorms ℝ Z (Z →L[ℝ] V)).finset_sups).continuous_seminorm s).comp
                  (SchwartzMap.fderivCLM ℝ Z V).continuous
              obtain ⟨s', Cq, hCq_ne, hq_bound⟩ :=
                Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Z V) q hq_cont
              let C' : ℝ := ‖L‖ * C * Cq
              refine ⟨s', C', by positivity, ?_⟩
              intro g ξ
              let g' : SchwartzMap Z (Z →L[ℝ] V) := SchwartzMap.fderivCLM ℝ Z V g
              have hderivEq :
                  fderiv ℝ (fun ξ : X => ∫ a : A0, g (T a ξ)) =
                    fun ξ => L (∫ a : A0, g' (T a ξ)) := by
                funext ξ'
                simpa [L, ContinuousLinearMap.compL_apply] using (hderiv V g ξ').fderiv
              have hqg :
                  q g ≤ (Cq : ℝ) * (s'.sup (schwartzSeminormFamily ℝ Z V)) g := by
                simpa [q] using hq_bound g
              calc
                ‖ξ‖ ^ k *
                    ‖iteratedFDeriv ℝ (m + 1)
                        (fun ξ' : X => ∫ a : A0, g (T a ξ')) ξ‖
                    = ‖ξ‖ ^ k *
                        ‖iteratedFDeriv ℝ m
                            (fderiv ℝ (fun ξ' : X => ∫ a : A0, g (T a ξ'))) ξ‖ := by
                          rw [norm_iteratedFDeriv_fderiv]
                _ = ‖ξ‖ ^ k *
                      ‖iteratedFDeriv ℝ m
                          (L ∘ fun ξ : X => ∫ a : A0, g' (T a ξ)) ξ‖ := by
                      have hcompEq :
                          (fun ξ : X => L (∫ a : A0, g' (T a ξ))) =
                            L ∘ fun ξ : X => ∫ a : A0, g' (T a ξ) := rfl
                      rw [hderivEq, hcompEq]
                _ ≤ ‖ξ‖ ^ k *
                      (‖L‖ * ‖iteratedFDeriv ℝ m
                        (fun ξ : X => ∫ a : A0, g' (T a ξ)) ξ‖) := by
                      gcongr
                      exact L.norm_iteratedFDeriv_comp_left
                        (hnat m (Z →L[ℝ] V) g').contDiffAt le_rfl
                _ = ‖L‖ * (‖ξ‖ ^ k *
                      ‖iteratedFDeriv ℝ m
                        (fun ξ : X => ∫ a : A0, g' (T a ξ)) ξ‖) := by ring
                _ ≤ ‖L‖ * (C * (s.sup (schwartzSeminormFamily ℝ Z (Z →L[ℝ] V))) g') := by
                      exact mul_le_mul_of_nonneg_left (hCbound g' ξ) (by positivity)
                _ = ‖L‖ * (C * q g) := by rfl
                _ ≤ ‖L‖ * (C * ((Cq : ℝ) * (s'.sup (schwartzSeminormFamily ℝ Z V)) g)) := by
                      gcongr
                _ = C' * (s'.sup (schwartzSeminormFamily ℝ Z V)) g := by
                      dsimp [C']
                      ring
        obtain ⟨s, C, hC, hbound'⟩ := hbound N.1 N.2 ℂ
        refine ⟨s, C, hC, ?_⟩
        intro f ξ
        simpa [A0, X, Z, S, T] using hbound' f ξ
  refine A.continuous.congr ?_
  intro f
  ext ξ
  change (∫ a : Fin (d + 1) → ℝ,
      f (fun k μ => a μ + diffVarSection d n ξ k μ)) =
    ∫ a : Fin (d + 1) → ℝ,
      f (fun k μ => a μ + diffVarSection d n ξ k μ)
  rfl

/-- Fiber integration over the basepoint: maps a Schwartz function on (n+1)
    spacetime points to a Schwartz function of n difference variables by
    integrating over the common translation orbit:

      `(diffVarReduction f)(ξ) = ∫ₐ f(a, a + ξ₁, a + ξ₁ + ξ₂, …) da`

    where `a ∈ ℝ^{d+1}` is the basepoint. This is the correct test-function
    reduction for translation-invariant distributions: if `W_{n+1}` is
    translation-invariant, then `W_{n+1}(f) = w(diffVarReduction f)` defines
    the reduced distribution `w` in difference variables. -/
noncomputable def diffVarReduction (n : ℕ) :
    SchwartzNPointSpace d (n + 1) →L[ℂ] SchwartzNPointSpace d n where
  toFun f :=
    ⟨fun ξ => ∫ a : Fin (d + 1) → ℝ,
        f (fun k μ => a μ + diffVarSection d n ξ k μ),
      diffVarReduction_contDiff d n f,
      diffVarReduction_decay d n f⟩
  map_add' f g := by
    ext ξ; show (∫ a, (f + g) _) = (∫ a, f _) + (∫ a, g _)
    simp only [SchwartzMap.add_apply]
    exact integral_add (diffVarReduction_integrable d n f ξ)
      (diffVarReduction_integrable d n g ξ)
  map_smul' c f := by
    ext ξ; show (∫ a, (c • f) _) = c • (∫ a, f _)
    simp only [SchwartzMap.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  cont := diffVarReduction_cont d n

/-- **Spectral condition (distribution-level / Streater-Wightman form).**

    For each n, there exists a tempered distribution `w` on n copies of spacetime
    (the reduced Wightman function in difference variables ξⱼ = xⱼ₊₁ - xⱼ) such that:
    1. `w` determines `W_{n+1}` via fiber integration over the basepoint:
       `W_{n+1}(f) = w(diffVarReduction f)` where
       `(diffVarReduction f)(ξ) = ∫ₐ f(a, a+ξ₁, a+ξ₁+ξ₂, …) da`.
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
    with a global polynomial-growth bound there, and with distributional boundary
    values recovering `W_n`.

    This matches the Vladimirov / Paley-Wiener-Schwartz tube hypothesis used by the
    backward implication to spectral support: holomorphicity alone plus boundary
    values is too weak without the slow-growth condition in the tube. -/
def ForwardTubeAnalyticity
    (W : (n : ℕ) → SchwartzNPointSpace d n → ℂ) : Prop :=
  ∀ (n : ℕ),
    ∃ (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d n) ∧
      (∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ z, z ∈ ForwardTube d n → ‖W_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N) ∧
      (∀ (f : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W n f)))

end SpectralConditionDefinitions


variable {d : ℕ} [NeZero d]

def euclideanDot (η p : Fin (d + 1) → ℝ) : ℝ :=
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

/-- **Self-duality of the closed forward cone (qualitative).**
    For `y, p ∈ V̄₊`, the Euclidean dot product `∑_μ y(μ) · p(μ) ≥ 0`.

    Proof: `y₀p₀ ≥ √(spatialNormSq y) · √(spatialNormSq p) ≥ |spatialInner y p|`
    by Cauchy-Schwarz. So `euclideanDot y p = y₀p₀ + spatialInner y p ≥ 0`. -/
lemma euclideanDot_nonneg_closedCone
    (y : Fin (d + 1) → ℝ) (hy : y ∈ ForwardMomentumCone d)
    (p : Fin (d + 1) → ℝ) (hp : p ∈ ForwardMomentumCone d) :
    euclideanDot y p ≥ 0 := by
  -- Unpack V̄₊ membership: causal + forward
  simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
    MinkowskiSpace.ForwardLightCone, Set.mem_setOf_eq,
    MinkowskiSpace.IsCausal, MinkowskiSpace.timeComponent] at hy hp
  have hy0 : y 0 ≥ 0 := hy.2
  have hp0 : p 0 ≥ 0 := hp.2
  have hy_spatial : MinkowskiSpace.spatialNormSq d y ≤ (y 0) ^ 2 := by
    have := MinkowskiSpace.minkowskiNormSq_decomp d y; linarith [hy.1]
  have hp_spatial : MinkowskiSpace.spatialNormSq d p ≤ (p 0) ^ 2 := by
    have := MinkowskiSpace.minkowskiNormSq_decomp d p; linarith [hp.1]
  -- Decompose euclideanDot = y₀p₀ + spatialInner
  have h_decomp : euclideanDot y p = y 0 * p 0 + MinkowskiSpace.spatialInner d y p := by
    simp only [euclideanDot, MinkowskiSpace.spatialInner, Fin.sum_univ_succ]
  rw [h_decomp]
  -- Cauchy-Schwarz: (spatialInner y p)² ≤ spatialNormSq y * spatialNormSq p ≤ (y₀ p₀)²
  have hcs := MinkowskiSpace.spatial_cauchy_schwarz d y p
  have h_sq_le : (MinkowskiSpace.spatialInner d y p) ^ 2 ≤ (y 0 * p 0) ^ 2 := by
    calc (MinkowskiSpace.spatialInner d y p) ^ 2
        ≤ MinkowskiSpace.spatialNormSq d y * MinkowskiSpace.spatialNormSq d p := hcs
      _ ≤ (y 0) ^ 2 * (p 0) ^ 2 := mul_le_mul hy_spatial hp_spatial
          (MinkowskiSpace.spatialNormSq_nonneg d p) (sq_nonneg _)
      _ = (y 0 * p 0) ^ 2 := by ring
  -- spatialInner y p ≥ -(y₀ p₀), so y₀p₀ + spatialInner ≥ 0
  have := (abs_le_of_sq_le_sq' h_sq_le (mul_nonneg hy0 hp0)).1
  linarith

/-! ### Main Theorem -/

variable (d) in
/-- **Equivalence of the two spectral condition formulations.**

    `SpectralConditionDistribution d W ↔ ForwardTubeAnalyticity d W`.

    The forward direction uses the Fourier-Laplace representation theorem
    (Vladimirov §25), and the backward direction uses the converse
    Paley-Wiener-Schwartz tube theorem (Vladimirov §26), so the tube side must
    include the standard global polynomial-growth hypothesis in addition to
    holomorphicity and boundary-value recovery.

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
  sorry

end
