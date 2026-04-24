/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.Spacetime.MinkowskiGeometry
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Spectral Condition: Definitions and One-Way Theorem

This file contains:
1. **Momentum-space spectral condition definitions**: Fourier transform on n-point
   Schwartz space, difference-variable reduction, `SpectralConditionDistribution`,
   `ForwardTubeAnalyticity`.
2. **One-way implication only**:
   `ForwardTubeAnalyticity d W → SpectralConditionDistribution d W`,
   using the converse Paley-Wiener-Schwartz tube theorem
   (Vladimirov §26 Thm 26.1 / RS II §IX.3).

## Main Results

- `spectralConditionDistribution_of_forwardTubeAnalyticity`:
  `ForwardTubeAnalyticity d W → SpectralConditionDistribution d W`

The reverse direction under the global polynomial-growth hypothesis is
deferred: the standard Fourier-Laplace transform of a cone-supported tempered
distribution satisfies only Vladimirov slow growth, which is weaker than a
uniform `(1 + ‖z‖)^N` bound on the whole tube.
-/

noncomputable section

open MeasureTheory Complex Filter Set Topology Module OSReconstruction

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

/-! ### One-Way Direction Infrastructure -/

private abbrev BasepointSpace (d : ℕ) := Fin (d + 1) → ℝ

/-- A normalized Schwartz bump on the basepoint variable. This is the cutoff
used to choose a section of `diffVarReduction`. The implementation should
eventually follow the local `normedUnitBumpSchwartzPi` pattern recorded in the
blueprint. -/
private noncomputable def normedUnitBumpSchwartzLocal :
    SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => ((b.normed MeasureTheory.volume x : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

private lemma integral_normedUnitBumpSchwartzLocal :
    ∫ x : ℝ, normedUnitBumpSchwartzLocal x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have happly :
      (fun x : ℝ => normedUnitBumpSchwartzLocal x) =
        fun x : ℝ => ((b.normed MeasureTheory.volume x : ℝ) : ℂ) := by
    funext x
    have hf_smooth : ContDiff ℝ (⊤ : ENat)
        (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) := by
      exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
    have hf_compact :
        HasCompactSupport (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) :=
      b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
    simpa [normedUnitBumpSchwartzLocal, b] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x)
  rw [happly, integral_complex_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.integral_normed (μ := MeasureTheory.volume))

private noncomputable def normedUnitBumpSchwartzPi : ∀ k : ℕ,
    SchwartzMap (Fin k → ℝ) ℂ
  | 0 => by
      let f : (Fin 0 → ℝ) → ℂ := fun _ => 1
      have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
        simpa [f] using
          (contDiff_const : ContDiff ℝ (⊤ : ENat) (fun _ : Fin 0 → ℝ => (1 : ℂ)))
      have hf_compact : HasCompactSupport f := by
        simpa [HasCompactSupport, tsupport, Function.support, f] using
          (show IsCompact (Set.univ : Set (Fin 0 → ℝ)) from isCompact_univ)
      exact hf_compact.toSchwartzMap hf_smooth
  | k + 1 => normedUnitBumpSchwartzLocal.prependField (normedUnitBumpSchwartzPi k)

private lemma integral_normedUnitBumpSchwartzPi :
    ∀ k : ℕ, ∫ x : Fin k → ℝ, normedUnitBumpSchwartzPi k x = 1
  | 0 => by
      have happly :
          (fun x : Fin 0 → ℝ => normedUnitBumpSchwartzPi 0 x) =
            fun _ : Fin 0 → ℝ => (1 : ℂ) := by
        funext x
        simp [normedUnitBumpSchwartzPi]
      rw [happly]
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
            MeasureTheory.Measure.dirac default := by
        simpa using
          (MeasureTheory.Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => ℝ) (x := default))
      simpa [hvol] using
        (MeasureTheory.integral_dirac (a := default) (f := fun _ : Fin 0 → ℝ => (1 : ℂ)))
  | k + 1 => by
      calc
        ∫ x : Fin (k + 1) → ℝ, normedUnitBumpSchwartzPi (k + 1) x
            =
          ∫ z : ℝ × (Fin k → ℝ), normedUnitBumpSchwartzPi (k + 1) (Fin.cons z.1 z.2) := by
              simpa using
                (OSReconstruction.integral_finSucc_cons_eq
                  (f := fun x : Fin (k + 1) → ℝ => normedUnitBumpSchwartzPi (k + 1) x)).symm
        _ = ∫ z : ℝ × (Fin k → ℝ),
              normedUnitBumpSchwartzLocal z.1 * normedUnitBumpSchwartzPi k z.2 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              simp [normedUnitBumpSchwartzPi, SchwartzMap.prependField_apply]
        _ = (∫ x : ℝ, normedUnitBumpSchwartzLocal x) *
              (∫ y : Fin k → ℝ, normedUnitBumpSchwartzPi k y) := by
              simpa using
                (MeasureTheory.integral_prod_mul
                  (f := fun x : ℝ => normedUnitBumpSchwartzLocal x)
                  (g := fun y : Fin k → ℝ => normedUnitBumpSchwartzPi k y))
        _ = 1 := by
              rw [integral_normedUnitBumpSchwartzLocal, integral_normedUnitBumpSchwartzPi k]
              ring

private noncomputable def normalizedBasepointBump (d : ℕ) :
    SchwartzMap (BasepointSpace d) ℂ :=
  normedUnitBumpSchwartzPi (d + 1)

private lemma integral_normalizedBasepointBump (d : ℕ) :
    ∫ a : BasepointSpace d, normalizedBasepointBump d a = 1 := by
  simpa [normalizedBasepointBump] using integral_normedUnitBumpSchwartzPi (d + 1)

private noncomputable def basepointDiffCLE (d : ℕ) (n : ℕ) :
    NPointSpacetime d (n + 1) ≃L[ℝ] (Fin (n + 1) → BasepointSpace d) where
  toFun x := Fin.cons (x 0) (fun k => fun μ => x k.succ μ - x k.castSucc μ)
  invFun y k μ := y 0 μ + diffVarSection d n (fun i => y i.succ) k μ
  left_inv := by
    intro x; ext k μ
    refine Fin.cases ?_ ?_ k
    · simp [diffVarSection_zero]
    · intro i
      suffices h : ∀ j : Fin (n + 1),
          x 0 μ + diffVarSection d n (fun l ν => x l.succ ν - x l.castSucc ν) j μ = x j μ from
        h i.succ
      intro j; induction j using Fin.induction with
      | zero => simp [diffVarSection_zero]
      | succ j ih =>
          have hsucc := diffVarSection_succ (d := d) n (fun l ν => x l.succ ν - x l.castSucc ν) j μ
          simp only [] at hsucc
          linarith
  right_inv := by
    intro y; ext k μ
    refine Fin.cases ?_ ?_ k
    · simp [diffVarSection_zero]
    · intro i
      change (y 0 μ + diffVarSection d n (fun j => y j.succ) i.succ μ) -
          (y 0 μ + diffVarSection d n (fun j => y j.succ) i.castSucc μ) = y i.succ μ
      rw [diffVarSection_succ]
      ring
  map_add' := by
    intro x y
    ext k μ <;> refine Fin.cases ?_ ?_ k <;> simp [Pi.add_apply, add_sub_add_comm]
  map_smul' := by
    intro c x
    ext k μ <;> refine Fin.cases ?_ ?_ k <;> simp [Pi.smul_apply, smul_sub, mul_sub]
  continuous_toFun := by
    apply continuous_pi; intro k; refine Fin.cases ?_ ?_ k
    · simp only [Fin.cons_zero]
      exact continuous_apply 0
    · intro i; simp only [Fin.cons_succ]
      exact continuous_pi fun μ =>
        ((continuous_apply μ).comp (continuous_apply i.succ)).sub
          ((continuous_apply μ).comp (continuous_apply i.castSucc))
  continuous_invFun := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    apply Continuous.add
    · exact (continuous_apply μ).comp (continuous_apply 0)
    · exact (continuous_apply μ).comp ((continuous_apply k).comp
        ((diffVarSection d n).continuous.comp
          (continuous_pi fun i => continuous_apply i.succ)))

@[simp] private lemma basepointDiffCLE_apply_zero (d : ℕ) (n : ℕ)
    (x : NPointSpacetime d (n + 1)) :
    basepointDiffCLE d n x 0 = x 0 := rfl

@[simp] private lemma basepointDiffCLE_apply_succ (d : ℕ) (n : ℕ)
    (x : NPointSpacetime d (n + 1)) (k : Fin n) :
    basepointDiffCLE d n x k.succ = fun μ => x k.succ μ - x k.castSucc μ := rfl

/-- A chosen Schwartz section of `diffVarReduction`. This should eventually be
implemented by transporting the tensor product `(a, ξ) ↦ φ₀(a) g(ξ)` back from
basepoint-plus-difference coordinates. -/
private noncomputable def sectionOf (d : ℕ) (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ) :
    SchwartzNPointSpace d n → SchwartzNPointSpace d (n + 1) :=
  fun g =>
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (basepointDiffCLE d n)
      (φ₀.prependField g)

private noncomputable def sectionOfCLM (d : ℕ) (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ) :
    SchwartzNPointSpace d n →L[ℂ] SchwartzNPointSpace d (n + 1) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (basepointDiffCLE d n)).comp
    (SchwartzMap.prependFieldCLMRight φ₀)

@[simp] private lemma sectionOfCLM_apply (d : ℕ) (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ) (g : SchwartzNPointSpace d n) :
    sectionOfCLM d n φ₀ g = sectionOf d n φ₀ g := rfl

/-- The chosen section is a right inverse to `diffVarReduction` once the bump
has total integral `1`. -/
private lemma diffVarReduction_sectionOf (d : ℕ) [NeZero d] (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ)
    (hφ₀ : ∫ a : BasepointSpace d, φ₀ a = 1)
    (g : SchwartzNPointSpace d n) :
    diffVarReduction d n (sectionOf d n φ₀ g) = g := by
  ext ξ
  change
    ∫ a : Fin (d + 1) → ℝ,
      sectionOf d n φ₀ g (fun k μ => a μ + diffVarSection d n ξ k μ) = g ξ
  calc
    ∫ a : Fin (d + 1) → ℝ,
        sectionOf d n φ₀ g (fun k μ => a μ + diffVarSection d n ξ k μ)
      = ∫ a : Fin (d + 1) → ℝ, φ₀ a * g ξ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with a
          show (φ₀.prependField g)
              (basepointDiffCLE d n (fun k μ => a μ + diffVarSection d n ξ k μ)) = φ₀ a * g ξ
          have key : basepointDiffCLE d n (fun k μ => a μ + diffVarSection d n ξ k μ) =
              Fin.cons a ξ := by
            funext k μ; refine Fin.cases ?_ ?_ k
            · simp [diffVarSection_zero]
            · intro i
              simp only [basepointDiffCLE_apply_succ, Fin.cons_succ, diffVarSection_succ]
              ring
          simp [key, SchwartzMap.prependField_apply, Fin.cons_zero, Fin.cons_succ]
    _ = (∫ a : Fin (d + 1) → ℝ, φ₀ a) * g ξ := by
          trans g ξ • ∫ a : Fin (d + 1) → ℝ, (φ₀ a : ℂ)
          · rw [← integral_smul]
            congr 1; funext a; rw [smul_eq_mul, mul_comm]
          · rw [smul_eq_mul, mul_comm]
    _ = g ξ := by rw [hφ₀]; ring

private lemma diffVarReduction_sub_sectionOf_eq_zero (d : ℕ) [NeZero d] (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ)
    (hφ₀ : ∫ a : BasepointSpace d, φ₀ a = 1)
    (f : SchwartzNPointSpace d (n + 1)) :
    diffVarReduction d n
      (f - sectionOf d n φ₀ (diffVarReduction d n f)) = 0 := by
  rw [(diffVarReduction d n).map_sub, diffVarReduction_sectionOf d n φ₀ hφ₀, sub_self]

private theorem eq_of_splitFirst_eq_splitLast_eq_local {p q : ℕ}
    {x y : Fin (p + q) → ℝ}
    (hfirst : splitFirst p q x = splitFirst p q y)
    (hlast : splitLast p q x = splitLast p q y) :
    x = y := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    exact congrFun hfirst a
  · intro b
    exact congrFun hlast b

private theorem splitFirst_smul_local {p q : ℕ} (r : ℝ)
    (x : Fin (p + q) → ℝ) :
    splitFirst p q (r • x) = r • splitFirst p q x := by
  ext i
  simp [splitFirst, Pi.smul_apply]

private theorem splitLast_smul_local {p q : ℕ} (r : ℝ)
    (x : Fin (p + q) → ℝ) :
    splitLast p q (r • x) = r • splitLast p q x := by
  ext i
  simp [splitLast, Pi.smul_apply]

@[simp] private theorem castFinCLE_apply_local {a b : ℕ} (h : a = b)
    (x : Fin a → ℝ) (i : Fin b) :
    castFinCLE h x i = x ((finCongr h).symm i) := rfl

private noncomputable def basepointDiffPairCLE (d : ℕ) (n : ℕ) :
    NPointSpacetime d (n + 1) ≃L[ℝ] (BasepointSpace d × NPointSpacetime d n) where
  toFun x := (x 0, fun k μ => x k.succ μ - x k.castSucc μ)
  invFun y k μ := y.1 μ + diffVarSection d n y.2 k μ
  left_inv := by
    intro x
    ext k μ
    refine Fin.cases ?_ ?_ k
    · simp [diffVarSection_zero]
    · intro i
      suffices h : ∀ j : Fin (n + 1),
          x 0 μ + diffVarSection d n (fun l ν => x l.succ ν - x l.castSucc ν) j μ = x j μ by
        exact h i.succ
      intro j
      induction j using Fin.induction with
      | zero =>
          simp [diffVarSection_zero]
      | succ j ih =>
          have hsucc :=
            diffVarSection_succ (d := d) n
              (fun l ν => x l.succ ν - x l.castSucc ν) j μ
          simp only [] at hsucc
          linarith
  right_inv := by
    intro y
    rcases y with ⟨a, ξ⟩
    apply Prod.ext
    · funext μ
      simp [diffVarSection_zero]
    · funext k
      funext μ
      change (a μ + diffVarSection d n ξ k.succ μ) -
          (a μ + diffVarSection d n ξ k.castSucc μ) = ξ k μ
      rw [diffVarSection_succ]
      ring
  map_add' := by
    intro x y
    apply Prod.ext
    · funext μ
      simp
    · funext k
      funext μ
      simp [add_sub_add_comm]
  map_smul' := by
    intro c x
    apply Prod.ext
    · funext μ
      simp
    · funext k
      funext μ
      change c * x k.succ μ - c * x k.castSucc μ = c * (x k.succ μ - x k.castSucc μ)
      ring
  continuous_toFun := by
    exact Continuous.prodMk (continuous_apply 0) <| by
      apply continuous_pi
      intro k
      apply continuous_pi
      intro μ
      exact ((continuous_apply μ).comp (continuous_apply k.succ)).sub
        ((continuous_apply μ).comp (continuous_apply k.castSucc))
  continuous_invFun := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    apply Continuous.add
    · exact (continuous_apply μ).comp continuous_fst
    · exact (continuous_apply μ).comp
        ((continuous_apply k).comp
          ((diffVarSection d n).continuous.comp continuous_snd))

@[simp] private lemma basepointDiffPairCLE_apply
    (d : ℕ) (n : ℕ) (x : NPointSpacetime d (n + 1)) :
    basepointDiffPairCLE d n x =
      (x 0, fun k μ => x k.succ μ - x k.castSucc μ) := rfl

@[simp] private lemma basepointDiffPairCLE_translate_diagonal
    (d : ℕ) (n : ℕ) (a : BasepointSpace d) (x : NPointSpacetime d (n + 1)) :
    basepointDiffPairCLE d n (fun i μ => x i μ + a μ) =
      ((basepointDiffPairCLE d n x).1 + a, (basepointDiffPairCLE d n x).2) := by
  apply Prod.ext
  · funext μ
    simp [basepointDiffPairCLE]
  · funext k
    funext μ
    simp [basepointDiffPairCLE, add_sub_add_right_eq_sub]

private noncomputable def flattenDiffCLE (d : ℕ) (n : ℕ) :
    NPointSpacetime d n ≃L[ℝ] (Fin (n * (d + 1)) → ℝ) :=
  (({ (Equiv.curry (Fin n) (Fin (d + 1)) ℝ).symm with
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl } :
      (Fin n → Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin n × Fin (d + 1) → ℝ)).trans
    (LinearEquiv.funCongrLeft ℝ ℝ finProdFinEquiv.symm)).toContinuousLinearEquiv

@[simp] private lemma flattenDiffCLE_symm_apply
    (d : ℕ) (n : ℕ) (u : Fin (n * (d + 1)) → ℝ) (i : Fin n) (j : Fin (d + 1)) :
    (flattenDiffCLE d n).symm u i j = u (finProdFinEquiv (i, j)) := rfl

@[simp] private lemma flattenSchwartzNPoint_apply_flattenDiff
    (d : ℕ) (n : ℕ) (g : SchwartzNPointSpace d n) (u : Fin (n * (d + 1)) → ℝ) :
    flattenSchwartzNPoint (d := d) g u = g ((flattenDiffCLE d n).symm u) := by
  rw [flattenSchwartzNPoint_apply]
  congr 1

private noncomputable def flattenBasepointDiffCLE (d : ℕ) (n : ℕ) :
    (BasepointSpace d × NPointSpacetime d n) ≃L[ℝ]
      (Fin ((d + 1) + n * (d + 1)) → ℝ) :=
  (({ toFun := fun y =>
        zeroTailBlockShift (m := d + 1) (n := n * (d + 1)) y.1 +
          zeroHeadBlockShift (m := d + 1) (n := n * (d + 1))
            (flattenDiffCLE d n y.2)
      invFun := fun u =>
        (splitFirst (d + 1) (n * (d + 1)) u,
          (flattenDiffCLE d n).symm (splitLast (d + 1) (n * (d + 1)) u))
      left_inv := by
        intro y
        rcases y with ⟨a, ξ⟩
        apply Prod.ext
        · funext μ
          simp
        · apply (flattenDiffCLE d n).injective
          funext i
          simp
      right_inv := by
        intro u
        apply eq_of_splitFirst_eq_splitLast_eq_local
        · simp
        · simp
      map_add' := by
        intro y z
        apply eq_of_splitFirst_eq_splitLast_eq_local
        · simp [map_add]
        · simp [map_add]
      map_smul' := by
        intro r y
        apply eq_of_splitFirst_eq_splitLast_eq_local
        · simp [splitFirst_smul_local, map_smul]
        · simp [splitLast_smul_local, map_smul] } :
      (BasepointSpace d × NPointSpacetime d n) ≃ₗ[ℝ]
        (Fin ((d + 1) + n * (d + 1)) → ℝ))).toContinuousLinearEquiv

@[simp] private lemma flattenBasepointDiffCLE_add_basepoint
    (d : ℕ) (n : ℕ) (a₀ : BasepointSpace d)
    (y : BasepointSpace d × NPointSpacetime d n) :
    flattenBasepointDiffCLE d n (y.1 + a₀, y.2) =
      flattenBasepointDiffCLE d n y +
        zeroTailBlockShift (m := d + 1) (n := n * (d + 1)) a₀ := by
  rcases y with ⟨a, ξ⟩
  apply eq_of_splitFirst_eq_splitLast_eq_local
  · ext i
    simp [flattenBasepointDiffCLE, splitFirst_add, add_assoc, add_left_comm, add_comm]
  · ext i
    simp [flattenBasepointDiffCLE, splitLast_add, add_assoc, add_left_comm, add_comm]

private noncomputable def flattenBasepointDiffSchwartz (d : ℕ) (n : ℕ) :
    SchwartzNPointSpace d (n + 1) →L[ℂ]
      SchwartzMap (Fin ((d + 1) + n * (d + 1)) → ℝ) ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (flattenBasepointDiffCLE d n).symm).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (basepointDiffPairCLE d n).symm)

@[simp] private lemma flattenBasepointDiffSchwartz_apply
    (d : ℕ) (n : ℕ) (f : SchwartzNPointSpace d (n + 1))
    (u : Fin ((d + 1) + n * (d + 1)) → ℝ) :
    flattenBasepointDiffSchwartz d n f u =
      f ((basepointDiffPairCLE d n).symm ((flattenBasepointDiffCLE d n).symm u)) := by
  simp [flattenBasepointDiffSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

private noncomputable def unflattenBasepointDiffSchwartz (d : ℕ) (n : ℕ) :
    SchwartzMap (Fin ((d + 1) + n * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzNPointSpace d (n + 1) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (basepointDiffPairCLE d n)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenBasepointDiffCLE d n))

@[simp] private lemma unflatten_flattenBasepointDiffSchwartz
    (d : ℕ) (n : ℕ) (f : SchwartzNPointSpace d (n + 1)) :
    unflattenBasepointDiffSchwartz d n (flattenBasepointDiffSchwartz d n f) = f := by
  ext x
  simpa [unflattenBasepointDiffSchwartz, flattenBasepointDiffSchwartz, basepointDiffPairCLE] using
    congrArg f ((basepointDiffPairCLE d n).symm_apply_apply x)

private noncomputable def transportedWHeadBlockCLM
    (d : ℕ) (n : ℕ)
    (W : SchwartzNPointSpace d (n + 1) → ℂ)
    (hW_cont : Continuous W)
    (hW_lin : IsLinearMap ℂ W) :
    SchwartzMap (Fin ((d + 1) + n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
  { toFun := fun ψ => W (unflattenBasepointDiffSchwartz d n ψ)
    map_add' := by
      intro ψ χ
      simp [unflattenBasepointDiffSchwartz, hW_lin.map_add]
    map_smul' := by
      intro c ψ
      simp [unflattenBasepointDiffSchwartz, hW_lin.map_smul]
    cont := hW_cont.comp (unflattenBasepointDiffSchwartz d n).continuous }

private lemma transportedWHeadBlockInvariant
    (d : ℕ) [NeZero d] (n : ℕ)
    {W : SchwartzNPointSpace d (n + 1) → ℂ}
    (hW_cont : Continuous W)
    (hW_lin : IsLinearMap ℂ W)
    (hW_transl : ∀ (a : BasepointSpace d)
      (f g : SchwartzNPointSpace d (n + 1)),
      (∀ x : NPointSpacetime d (n + 1),
        g.toFun x = f.toFun (fun i => x i + a)) →
      W f = W g) :
    IsHeadBlockTranslationInvariantSchwartzCLM
      (m := d + 1) (n := n * (d + 1))
      (transportedWHeadBlockCLM d n W hW_cont hW_lin) := by
  intro a
  ext ψ
  symm
  refine hW_transl a _ _ ?_
  intro x
  change ψ
      (flattenBasepointDiffCLE d n (basepointDiffPairCLE d n x) +
        zeroTailBlockShift (m := d + 1) (n := n * (d + 1)) a) =
    ψ (flattenBasepointDiffCLE d n
      (basepointDiffPairCLE d n (fun i μ => x i μ + a μ)))
  rw [basepointDiffPairCLE_translate_diagonal, flattenBasepointDiffCLE_add_basepoint]

private def basepointAssemble (d : ℕ) (m : ℕ) (hm : m ≤ d + 1) :
    (Fin m → ℝ) → (Fin (d + 1 - m) → ℝ) → (Fin (d + 1) → ℝ) :=
  fun aHead aTail =>
    castFinCLE (Nat.add_sub_of_le hm)
      (fun i : Fin (m + (d + 1 - m)) =>
        Fin.addCases (fun j => aHead (Fin.rev j)) aTail i)

@[simp] private lemma basepointAssemble_zero
    (d : ℕ) (aTail : Fin (d + 1) → ℝ) :
    basepointAssemble d 0 (Nat.zero_le (d + 1)) default aTail = aTail := by
  ext i
  rw [basepointAssemble, castFinCLE_apply_local]
  have hidx :
      ((finCongr (Nat.add_sub_of_le (Nat.zero_le (d + 1)))).symm i) = Fin.natAdd 0 i := by
    apply Fin.ext
    simp [Fin.natAdd]
  rw [hidx, Fin.addCases_right]

@[simp] private lemma basepointAssemble_zero_any
    (d : ℕ) (hm : 0 ≤ d + 1) (aTail : Fin (d + 1) → ℝ) :
    basepointAssemble d 0 hm default aTail = aTail := by
  have hproof : hm = Nat.zero_le (d + 1) := Subsingleton.elim _ _
  cases hproof
  simpa using basepointAssemble_zero d aTail

private lemma basepointAssemble_cons
    (d : ℕ) (m : ℕ) (hm : m + 1 ≤ d + 1)
    (aHead : Fin m → ℝ) (aTail : Fin (d + 1 - (m + 1)) → ℝ) (t : ℝ) :
    basepointAssemble d m (by omega) aHead
      (show Fin (d + 1 - m) → ℝ from
        castFinCLE (by omega : (d + 1 - (m + 1)) + 1 = d + 1 - m) (Fin.cons t aTail)) =
      basepointAssemble d (m + 1) hm (Fin.cons t aHead) aTail := by
  have hm₀ : m ≤ d + 1 := by omega
  have h' : (d + 1 - (m + 1)) + 1 = d + 1 - m := by omega
  ext i
  -- Unfold both basepointAssemble evaluations through castFinCLE
  rw [basepointAssemble, basepointAssemble]
  simp only [castFinCLE_apply_local]
  -- Name the reindexed points
  set iL : Fin (m + (d + 1 - m)) :=
    (finCongr (Nat.add_sub_of_le hm₀)).symm i with hiL_def
  set iR : Fin ((m + 1) + (d + 1 - (m + 1))) :=
    (finCongr (Nat.add_sub_of_le hm)).symm i with hiR_def
  have hiL_val : iL.val = i.val := by simp [iL]
  have hiR_val : iR.val = i.val := by simp [iR]
  -- Case analysis on i.val
  rcases lt_or_ge i.val m with h₁ | h₁
  · -- i.val < m: both sides reduce to aHead evaluated at the reversed head index
    have hLlt : iL.val < m := hiL_val ▸ h₁
    have hRlt : iR.val < m + 1 := by rw [hiR_val]; omega
    have hL_eq : iL = Fin.castAdd (d + 1 - m) (iL.castLT hLlt) := by
      apply Fin.ext; simp
    have hR_eq : iR = Fin.castAdd (d + 1 - (m + 1)) (iR.castLT hRlt) := by
      apply Fin.ext; simp
    rw [hL_eq, Fin.addCases_left, hR_eq, Fin.addCases_left]
    -- Both head indices have the same val = i.val < m, so the right is
    -- `Fin.castSucc` of the left.
    have hcastSucc :
        (iR.castLT hRlt : Fin (m + 1)) = Fin.castSucc (iL.castLT hLlt) := by
      apply Fin.ext
      simp [hiL_val, hiR_val]
    rw [hcastSucc, Fin.rev_castSucc, Fin.cons_succ]
  · rcases eq_or_lt_of_le h₁ with h₂ | h₂
    · -- i.val = m: LHS hits the new cons head `t`; RHS hits Fin.cons t aHead 0 = t
      have hLnlt : ¬ iL.val < m := by rw [hiL_val, ← h₂]; omega
      have hRlt : iR.val < m + 1 := by rw [hiR_val, ← h₂]; omega
      have hLge : m ≤ iL.val := by rw [hiL_val, ← h₂]
      have hR_eq : iR = Fin.castAdd (d + 1 - (m + 1)) (iR.castLT hRlt) := by
        apply Fin.ext; simp
      -- LHS: use right branch of addCases with subNat-reconstruction
      have hLsub_val :
          (⟨iL.val - m, by
            have : iL.val < m + (d + 1 - m) := iL.isLt
            omega⟩ : Fin (d + 1 - m)).val = 0 := by
        show iL.val - m = 0
        omega
      have hL_eq :
          iL = Fin.natAdd m
            (⟨iL.val - m, by
              have : iL.val < m + (d + 1 - m) := iL.isLt
              omega⟩ : Fin (d + 1 - m)) := by
        apply Fin.ext
        show iL.val = m + (iL.val - m)
        omega
      rw [hL_eq, Fin.addCases_right, hR_eq, Fin.addCases_left]
      -- RHS head index: val m on Fin (m + 1) → Fin.last m
      have hRlast : (iR.castLT hRlt : Fin (m + 1)) = Fin.last m := by
        apply Fin.ext
        show iR.val = m
        omega
      rw [hRlast, Fin.rev_last, Fin.cons_zero]
      -- LHS: castFinCLE h' (Fin.cons t aTail) at the subNat index (val 0) equals t
      rw [castFinCLE_apply_local]
      have h0 :
          ((finCongr h').symm (⟨iL.val - m, by
            have : iL.val < m + (d + 1 - m) := iL.isLt
            omega⟩ : Fin (d + 1 - m)) : Fin ((d + 1 - (m + 1)) + 1)) = 0 := by
        apply Fin.ext
        exact hLsub_val
      rw [h0, Fin.cons_zero]
    · -- i.val > m: both sides reduce to `aTail` at the tail index i.val - (m+1)
      have hLnlt : ¬ iL.val < m := by rw [hiL_val]; omega
      have hRnlt : ¬ iR.val < m + 1 := by rw [hiR_val]; omega
      have hLge : m ≤ iL.val := by rw [hiL_val]; omega
      have hRge : m + 1 ≤ iR.val := by rw [hiR_val]; omega
      have hL_eq :
          iL = Fin.natAdd m
            (⟨iL.val - m, by
              have : iL.val < m + (d + 1 - m) := iL.isLt
              omega⟩ : Fin (d + 1 - m)) := by
        apply Fin.ext
        show iL.val = m + (iL.val - m)
        omega
      have hR_eq :
          iR = Fin.natAdd (m + 1)
            (⟨iR.val - (m + 1), by
              have : iR.val < (m + 1) + (d + 1 - (m + 1)) := iR.isLt
              omega⟩ : Fin (d + 1 - (m + 1))) := by
        apply Fin.ext
        show iR.val = (m + 1) + (iR.val - (m + 1))
        omega
      rw [hL_eq, Fin.addCases_right, hR_eq, Fin.addCases_right]
      -- LHS: castFinCLE h' (Fin.cons t aTail) at a subNat index with val > 0
      rw [castFinCLE_apply_local]
      -- Show the cast index equals Fin.succ of something, then use Fin.cons_succ
      have hsucc :
          ((finCongr h').symm (⟨iL.val - m, by
            have : iL.val < m + (d + 1 - m) := iL.isLt
            omega⟩ : Fin (d + 1 - m)) : Fin ((d + 1 - (m + 1)) + 1)) =
          Fin.succ (⟨iR.val - (m + 1), by
            have : iR.val < (m + 1) + (d + 1 - (m + 1)) := iR.isLt
            omega⟩ : Fin (d + 1 - (m + 1))) := by
        apply Fin.ext
        simp [hiL_val, hiR_val]
        omega
      rw [hsucc, Fin.cons_succ]

@[simp] private lemma splitFirst_flattenBasepointDiffCLE
    (d : ℕ) (n : ℕ) (y : BasepointSpace d × NPointSpacetime d n) :
    splitFirst (d + 1) (n * (d + 1))
      (flattenBasepointDiffCLE d n y) = y.1 := by
  rcases y with ⟨a, ξ⟩
  simp [flattenBasepointDiffCLE]

@[simp] private lemma splitLast_flattenBasepointDiffCLE
    (d : ℕ) (n : ℕ) (y : BasepointSpace d × NPointSpacetime d n) :
    splitLast (d + 1) (n * (d + 1))
      (flattenBasepointDiffCLE d n y) = flattenDiffCLE d n y.2 := by
  rcases y with ⟨a, ξ⟩
  simp [flattenBasepointDiffCLE]

private lemma splitFirst_castFinCLE_succ_add_symm_cons_local {m n : ℕ}
    (t : ℝ) (x : Fin (m + n) → ℝ) :
    splitFirst (m + 1) n ((castFinCLE (Nat.succ_add m n)).symm (Fin.cons t x)) =
      Fin.cons t (splitFirst m n x) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · have hcast :
        Fin.cast (Nat.succ_add m n) (Fin.castAdd n (0 : Fin (m + 1))) = 0 := by
      apply Fin.ext
      simp
    simp [splitFirst, hcast]
  · intro i
    have hcast :
        Fin.cast (Nat.succ_add m n) (Fin.castAdd n i.succ) = (Fin.castAdd n i).succ := by
      apply Fin.ext
      simp
    simp [splitFirst, hcast]

private lemma splitLast_castFinCLE_succ_add_symm_cons_local {m n : ℕ}
    (t : ℝ) (x : Fin (m + n) → ℝ) :
    splitLast (m + 1) n ((castFinCLE (Nat.succ_add m n)).symm (Fin.cons t x)) =
      splitLast m n x := by
  ext j
  have hcast :
      Fin.cast (Nat.succ_add m n) (Fin.natAdd (m + 1) j) = (Fin.natAdd m j).succ := by
    apply Fin.ext
    simp
    omega
  simp [splitLast, hcast]

private lemma sliceIntegral_flattenBasepointDiff_step
    (d : ℕ) (n : ℕ) (m : ℕ)
    (hm : m + 1 ≤ d + 1)
    (f : SchwartzNPointSpace d (n + 1))
    (x : Fin (m + ((d + 1 - (m + 1)) + n * (d + 1))) → ℝ) :
    sliceIntegral
      (reindexSchwartzFin
        (Nat.succ_add m ((d + 1 - (m + 1)) + n * (d + 1)))
        (reindexSchwartzFin
          (by omega : (d + 1) + n * (d + 1) =
            (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)))
          (flattenBasepointDiffSchwartz d n f))) x
      =
    ∫ t : ℝ,
      (reindexSchwartzFin
        (by omega : (d + 1) + n * (d + 1) =
          (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)))
        (flattenBasepointDiffSchwartz d n f))
        ((castFinCLE
            (Nat.succ_add m ((d + 1 - (m + 1)) + n * (d + 1)))).symm
          (Fin.cons t x)) := by
  simp [sliceIntegral_apply, sliceIntegralRaw, reindexSchwartzFin_apply]

private lemma integrateHeadBlock_slice_swap_flattenBasepoint
    {m N : ℕ}
    (F : SchwartzMap (Fin ((m + 1) + N) → ℝ) ℂ)
    (u : Fin N → ℝ) :
    integrateHeadBlock (m := m)
        (n := N)
        (sliceIntegral
          (reindexSchwartzFin (Nat.succ_add m N) F)) u =
      ∫ t : ℝ,
        integrateHeadBlock (m := m)
            (n := N + 1)
            (reindexSchwartzFin (by omega : (m + 1) + N = m + (N + 1)) F)
          (Fin.cons t u) := by
  induction m generalizing N u with
  | zero =>
      simp only [integrateHeadBlock, reindexSchwartzFin_apply, sliceIntegral_apply,
        sliceIntegralRaw]
      congr 1
      funext t
      apply congrArg
      ext i
      rcases i with ⟨iv, hiv⟩
      cases iv with
      | zero =>
          simp only [castFinCLE_symm_apply, Fin.cons]
          rfl
      | succ k =>
          simp only [castFinCLE_symm_apply, Fin.cons]
          rfl
  | succ m ihm =>
      -- F : SchwartzMap (Fin (((m + 1) + 1) + N) → ℝ) ℂ
      -- which equals Fin ((m + 2) + N) → ℝ by defn-eq (since (m+1)+1 = m+2 defn).
      -- Goal: integrateHeadBlock (m+1) (sliceIntegral (reindexSchwartzFin (Nat.succ_add (m+1) N) F)) u = ...
      -- Unfold integrateHeadBlock (m+1) on LHS via its recursive definition.
      let G :
          SchwartzMap (Fin ((m + 1) + N) → ℝ) ℂ :=
        sliceIntegral (reindexSchwartzFin (Nat.succ_add (m + 1) N) F)
      let F' :
          SchwartzMap (Fin ((m + 1) + (N + 1)) → ℝ) ℂ :=
        reindexSchwartzFin (by omega : ((m + 1) + 1) + N = (m + 1) + (N + 1)) F
      have hG_reindex :
          reindexSchwartzFin (by omega : (m + 1) + N = m + (N + 1)) G =
          sliceIntegral (reindexSchwartzFin (Nat.succ_add m (N + 1)) F') := by
        ext x
        simp only [G, F', reindexSchwartzFin_apply, sliceIntegral_apply, sliceIntegralRaw]
        congr 1
        funext t
        apply congrArg
        ext i
        rcases i with ⟨iv, hiv⟩
        cases iv with
        | zero =>
            simp only [castFinCLE_symm_apply, Fin.cons]
            rfl
        | succ k =>
            simp only [castFinCLE_symm_apply, Fin.cons]
            rfl
      calc
        integrateHeadBlock (m := m + 1) (n := N)
            (sliceIntegral (reindexSchwartzFin (Nat.succ_add (m + 1) N) F)) u
          =
            integrateHeadBlock (m := m) (n := N)
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add m N) G)) u := by
                simp [integrateHeadBlock, G]
        _ =
            ∫ s : ℝ,
              integrateHeadBlock (m := m) (n := N + 1)
                (reindexSchwartzFin (by omega : (m + 1) + N = m + (N + 1)) G)
                (Fin.cons s u) := by
                  exact ihm (N := N) (u := u) (F := G)
        _ =
            ∫ s : ℝ,
              integrateHeadBlock (m := m) (n := N + 1)
                (sliceIntegral (reindexSchwartzFin (Nat.succ_add m (N + 1)) F'))
                (Fin.cons s u) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with s
                  rw [hG_reindex]
        _ =
            ∫ s : ℝ, ∫ t : ℝ,
              integrateHeadBlock (m := m) (n := (N + 1) + 1)
                (reindexSchwartzFin (by omega : (m + 1) + (N + 1) = m + ((N + 1) + 1)) F')
                (Fin.cons t (Fin.cons s u)) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with s
                  exact ihm (N := N + 1) (u := Fin.cons s u) (F := F')
        _ =
            ∫ s : ℝ,
              integrateHeadBlock (m := m + 1) (n := N + 1)
                (reindexSchwartzFin
                  (by omega : ((m + 1) + 1) + N = (m + 1) + (N + 1)) F)
                (Fin.cons s u) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with s
                  symm
                  show integrateHeadBlock (m := m + 1) (n := N + 1) F' (Fin.cons s u) = _
                  show integrateHeadBlock (m := m) (n := N + 1)
                      (sliceIntegral (reindexSchwartzFin (Nat.succ_add m (N + 1)) F'))
                      (Fin.cons s u) = _
                  exact ihm (N := N + 1) (u := Fin.cons s u) (F := F')


private lemma integrateHeadBlock_flattenBasepointDiff_aux_m
    (d : ℕ) [NeZero d] (n : ℕ)
    (m : ℕ) (hm : m ≤ d + 1)
    (f : SchwartzNPointSpace d (n + 1))
    (u : Fin ((d + 1 - m) + n * (d + 1)) → ℝ) :
    integrateHeadBlock (m := m) (n := (d + 1 - m) + n * (d + 1))
      (reindexSchwartzFin (by omega)
        (flattenBasepointDiffSchwartz d n f)) u =
    ∫ aHead : Fin m → ℝ,
      f (fun k μ =>
        (basepointAssemble d m hm aHead
          (splitFirst (d + 1 - m) (n * (d + 1)) u)) μ +
        diffVarSection d n
          ((flattenDiffCLE d n).symm
            (splitLast (d + 1 - m) (n * (d + 1)) u)) k μ) := by
  induction m with
  | zero =>
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
            MeasureTheory.Measure.dirac default := by
        simpa using
          (MeasureTheory.Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => ℝ) (x := default))
      have hu :
          ((castFinCLE
              (by omega : (d + 1) + n * (d + 1) =
                0 + (d + 1 - 0 + n * (d + 1)))).symm
            ((castFinCLE (Nat.zero_add (d + 1 - 0 + n * (d + 1)))).symm u)) = u := by
        ext i
        simp [castFinCLE_symm_apply]
      rw [integrateHeadBlock, hvol, MeasureTheory.integral_dirac]
      rw [reindexSchwartzFin_apply]
      rw [reindexSchwartzFin_apply]
      rw [flattenBasepointDiffSchwartz_apply]
      rw [hu]
      have hA :
          basepointAssemble d 0 hm default
            (splitFirst (d + 1 - 0) (n * (d + 1)) u) =
          splitFirst (d + 1 - 0) (n * (d + 1)) u := by
        simpa using
          basepointAssemble_zero_any d hm
            (splitFirst (d + 1 - 0) (n * (d + 1)) u)
      congr 1
      ext k μ
      rw [hA]
      change ((flattenBasepointDiffCLE d n).symm u).1 μ +
          diffVarSection d n (((flattenBasepointDiffCLE d n).symm u).2) k μ =
        splitFirst (d + 1) (n * (d + 1)) u μ +
          diffVarSection d n
            ((flattenDiffCLE d n).symm (splitLast (d + 1) (n * (d + 1)) u)) k μ
      simp [flattenBasepointDiffCLE]
  | succ m ihm =>
      have hm' : m + 1 ≤ d + 1 := hm
      have hmle : m ≤ d + 1 := by omega
      have hdiff : (d + 1 - m) = (d + 1 - (m + 1)) + 1 := by omega
      have hcastEq : (d + 1 - m) + n * (d + 1) =
          ((d + 1 - (m + 1)) + n * (d + 1)) + 1 := by omega
      have hRindex : (d + 1) + n * (d + 1) =
          (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)) := by omega
      have hRindex' : (d + 1) + n * (d + 1) =
          m + ((d + 1 - m) + n * (d + 1)) := by omega
      rw [integrateHeadBlock]
      have hswap :
          integrateHeadBlock (m := m)
              (n := (d + 1 - (m + 1)) + n * (d + 1))
              (sliceIntegral
                (reindexSchwartzFin
                  (Nat.succ_add m ((d + 1 - (m + 1)) + n * (d + 1)))
                  (reindexSchwartzFin hRindex
                    (flattenBasepointDiffSchwartz d n f)))) u =
            ∫ t : ℝ,
              integrateHeadBlock (m := m)
                  (n := (d + 1 - m) + n * (d + 1))
                  (reindexSchwartzFin hRindex'
                    (flattenBasepointDiffSchwartz d n f))
                ((castFinCLE hcastEq).symm (Fin.cons t u)) := by
        have hswap0 :=
          integrateHeadBlock_slice_swap_flattenBasepoint
            (F := reindexSchwartzFin hRindex (flattenBasepointDiffSchwartz d n f))
            (u := u)
        have hreindex :
            reindexSchwartzFin
                (by omega : (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)) =
                  m + (((d + 1 - (m + 1)) + n * (d + 1)) + 1))
                (reindexSchwartzFin hRindex
                  (flattenBasepointDiffSchwartz d n f)) =
              reindexSchwartzFin
                (by omega : m + (d + 1 - m + n * (d + 1)) =
                  m + (((d + 1 - (m + 1)) + n * (d + 1)) + 1))
                (reindexSchwartzFin hRindex'
                  (flattenBasepointDiffSchwartz d n f)) := by
          ext x
          rw [reindexSchwartzFin_apply, reindexSchwartzFin_apply,
            reindexSchwartzFin_apply, reindexSchwartzFin_apply]
          rw [flattenBasepointDiffSchwartz_apply, flattenBasepointDiffSchwartz_apply]
          congr 1
        calc
          integrateHeadBlock (m := m)
              (n := (d + 1 - (m + 1)) + n * (d + 1))
              (sliceIntegral
                (reindexSchwartzFin
                  (Nat.succ_add m ((d + 1 - (m + 1)) + n * (d + 1)))
                  (reindexSchwartzFin hRindex
                    (flattenBasepointDiffSchwartz d n f)))) u
              =
            ∫ t : ℝ,
              integrateHeadBlock (m := m)
                  (n := ((d + 1 - (m + 1)) + n * (d + 1)) + 1)
                  (reindexSchwartzFin
                    (by omega : (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)) =
                      m + (((d + 1 - (m + 1)) + n * (d + 1)) + 1))
                    (reindexSchwartzFin hRindex
                      (flattenBasepointDiffSchwartz d n f)))
                  (Fin.cons t u) := by
                    exact hswap0
          _ =
            ∫ t : ℝ,
              integrateHeadBlock (m := m)
                  (n := (d + 1 - m) + n * (d + 1))
                  (reindexSchwartzFin hRindex'
                    (flattenBasepointDiffSchwartz d n f))
                  ((castFinCLE hcastEq).symm (Fin.cons t u)) := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards with t
                    have hG :
                        integrateHeadBlock (m := m)
                            (n := ((d + 1 - (m + 1)) + n * (d + 1)) + 1)
                            (reindexSchwartzFin
                              (by omega : (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)) =
                                m + (((d + 1 - (m + 1)) + n * (d + 1)) + 1))
                              (reindexSchwartzFin hRindex
                                (flattenBasepointDiffSchwartz d n f)))
                            (Fin.cons t u)
                          =
                        integrateHeadBlock (m := m)
                            (n := (d + 1 - m) + n * (d + 1))
                            (reindexSchwartzFin hRindex'
                              (flattenBasepointDiffSchwartz d n f))
                            ((castFinCLE hcastEq).symm (Fin.cons t u)) := by
                      rw [hreindex]
                      have hnat : ∀ (p : ℕ) (a b : ℕ) (hab : a = b)
                          (h : p + a = p + b)
                          (F : SchwartzMap (Fin (p + a) → ℝ) ℂ) (y : Fin b → ℝ),
                          integrateHeadBlock (m := p) (n := b)
                              (reindexSchwartzFin h F) y =
                            integrateHeadBlock (m := p) (n := a) F
                              ((castFinCLE hab).symm y) := by
                        intro p
                        induction p with
                        | zero =>
                            intro a b hab h F y
                            simp only [integrateHeadBlock, reindexSchwartzFin_apply]
                            apply congrArg F
                            ext i
                            simp only [castFinCLE_symm_apply]
                            apply congrArg y
                            apply Fin.ext
                            rfl
                        | succ k ihk =>
                            intro a b hab h F y
                            show integrateHeadBlock (m := k) (n := b)
                                  (sliceIntegral
                                    (reindexSchwartzFin (Nat.succ_add k b)
                                      (reindexSchwartzFin h F))) y =
                                integrateHeadBlock (m := k) (n := a)
                                  (sliceIntegral
                                    (reindexSchwartzFin (Nat.succ_add k a) F))
                                  ((castFinCLE hab).symm y)
                            have h' : k + a = k + b := by omega
                            have hs :
                                sliceIntegral
                                    (reindexSchwartzFin (Nat.succ_add k b)
                                      (reindexSchwartzFin h F))
                                  =
                                reindexSchwartzFin h'
                                  (sliceIntegral
                                    (reindexSchwartzFin (Nat.succ_add k a) F)) := by
                              apply SchwartzMap.ext
                              intro z
                              simp only [reindexSchwartzFin_apply, sliceIntegral_apply,
                                sliceIntegralRaw]
                              congr 1
                              funext tt
                              apply congrArg F
                              ext i
                              rcases i with ⟨iv, hiv⟩
                              cases iv with
                              | zero =>
                                  simp only [castFinCLE_symm_apply, Fin.cons]
                                  rfl
                              | succ iv' =>
                                  simp only [castFinCLE_symm_apply, Fin.cons]
                                  rfl
                            rw [hs]
                            exact ihk a b hab h' _ y
                      exact hnat m _ _ hcastEq _ _ (Fin.cons t u)
                    exact hG
      rw [hswap]
      simp_rw [ihm hmle]
      have hSF : ∀ t : ℝ,
          splitFirst (d + 1 - m) (n * (d + 1))
            ((castFinCLE hcastEq).symm (Fin.cons t u)) =
          (castFinCLE hdiff).symm
            (Fin.cons t (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) := by
        intro t
        ext i
        simp only [splitFirst, castFinCLE_symm_apply]
        rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
        · have hL_zero :
              (finCongr hcastEq) (Fin.castAdd (n * (d + 1)) i) =
                (0 : Fin (d + 1 - (m + 1) + n * (d + 1) + 1)) := by
            apply Fin.ext
            simp [Fin.val_castAdd, hi0]
          have hR_zero :
              (finCongr hdiff) i = (0 : Fin (d + 1 - (m + 1) + 1)) := by
            apply Fin.ext
            simp [hi0]
          rw [hL_zero, hR_zero, Fin.cons_zero, Fin.cons_zero]
        · have hipred : i.val - 1 < d + 1 - (m + 1) := by
            have := i.isLt; omega
          have hipred' : i.val - 1 < d + 1 - (m + 1) + n * (d + 1) := by
            have := i.isLt; omega
          have hL_succ :
              (finCongr hcastEq) (Fin.castAdd (n * (d + 1)) i) =
                Fin.succ ⟨i.val - 1, hipred'⟩ := by
            apply Fin.ext
            simp [Fin.val_castAdd, Fin.val_succ]
            omega
          have hR_succ :
              (finCongr hdiff) i = Fin.succ ⟨i.val - 1, hipred⟩ := by
            apply Fin.ext
            simp [Fin.val_succ]
            omega
          rw [hL_succ, hR_succ, Fin.cons_succ, Fin.cons_succ]
          rfl
      have hSL : ∀ t : ℝ,
          splitLast (d + 1 - m) (n * (d + 1))
            ((castFinCLE hcastEq).symm (Fin.cons t u)) =
          splitLast (d + 1 - (m + 1)) (n * (d + 1)) u := by
        intro t
        ext j
        simp only [splitLast, castFinCLE_symm_apply]
        have hjpos :
            0 < ((finCongr hcastEq) (Fin.natAdd (d + 1 - m) j)).val := by
          simp [Fin.val_natAdd]
          omega
        have hj_pred_lt :
            ((finCongr hcastEq) (Fin.natAdd (d + 1 - m) j)).val - 1 <
              d + 1 - (m + 1) + n * (d + 1) := by
          have := ((finCongr hcastEq) (Fin.natAdd (d + 1 - m) j)).isLt
          omega
        have hj_succ :
            (finCongr hcastEq) (Fin.natAdd (d + 1 - m) j) =
              Fin.succ ⟨((finCongr hcastEq) (Fin.natAdd (d + 1 - m) j)).val - 1,
                hj_pred_lt⟩ := by
          apply Fin.ext
          simp [Fin.val_succ]
          omega
        rw [hj_succ, Fin.cons_succ]
        apply congrArg u
        apply Fin.ext
        simp [Fin.val_natAdd]
        omega
      simp_rw [hSF, hSL]
      have happend :
          ∀ (t : ℝ) (aHead : Fin m → ℝ),
            basepointAssemble d m hmle aHead
              ((castFinCLE hdiff).symm
                (Fin.cons t
                  (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u))) =
              basepointAssemble d (m + 1) hm' (Fin.cons t aHead)
                (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u) := by
        intro t aHead
        simpa using
          (basepointAssemble_cons (d := d) (m := m) (hm := hm')
            (aHead := aHead)
            (aTail := splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u) t)
      simp_rw [happend]
      have hFubini :
          (∫ z : ℝ × (Fin m → ℝ),
            f (fun k μ =>
              (basepointAssemble d (m + 1) hm' (Fin.cons z.1 z.2)
                (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) μ +
              diffVarSection d n
                ((flattenDiffCLE d n).symm
                  (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)) k μ)
            ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
              (MeasureTheory.Measure.pi fun _ : Fin m =>
                (MeasureTheory.volume : MeasureTheory.Measure ℝ)))) =
          ∫ a : Fin (m + 1) → ℝ,
            f (fun k μ =>
              (basepointAssemble d (m + 1) hm' a
                (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) μ +
              diffVarSection d n
                ((flattenDiffCLE d n).symm
                  (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)) k μ) := by
        simpa using
          (OSReconstruction.integral_finSucc_cons_eq
            (f := fun a : Fin (m + 1) → ℝ =>
              f (fun k μ =>
                (basepointAssemble d (m + 1) hm' a
                  (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) μ +
                diffVarSection d n
                  ((flattenDiffCLE d n).symm
                    (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)) k μ)))
      -- Use Fubini: the integrand (as a function of z = (t, aHead)) is integrable because
      -- it equals a Schwartz function composed with an affine transformation, hence rapidly
      -- decaying in both variables. Apply `MeasureTheory.integral_prod` + `hFubini`.
      have hint :
          MeasureTheory.Integrable
            (fun z : ℝ × (Fin m → ℝ) =>
              f (fun k μ =>
                (basepointAssemble d (m + 1) hm' (Fin.cons z.1 z.2)
                  (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) μ +
                diffVarSection d n
                  ((flattenDiffCLE d n).symm
                    (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)) k μ))
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
              (MeasureTheory.Measure.pi fun _ : Fin m =>
                (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := by
        -- Define the affine map `g : (Fin (m+1) → ℝ) → NPointSpacetime d (n+1)`
        -- whose composition with f gives the integrand.
        let gBase : (Fin (m + 1) → ℝ) → (Fin (d + 1) → ℝ) := fun a =>
          basepointAssemble d (m + 1) hm' a
            (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)
        let gDiff : NPointSpacetime d n :=
          (flattenDiffCLE d n).symm
            (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)
        let g : (Fin (m + 1) → ℝ) → NPointSpacetime d (n + 1) := fun a =>
          (basepointDiffPairCLE d n).symm (gBase a, gDiff)
        -- Linear part of `gBase`: a ↦ basepointAssemble d (m+1) hm' a 0.
        let L : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
          { toFun := fun a => basepointAssemble d (m + 1) hm' a
              (0 : Fin (d + 1 - (m + 1)) → ℝ)
            map_add' := by
              intro a a'
              ext i
              simp only [basepointAssemble, castFinCLE_apply_local, Pi.add_apply]
              set j := (finCongr (Nat.add_sub_of_le hm')).symm i
              induction j using Fin.addCases with
              | left k => simp
              | right k => simp
            map_smul' := by
              intro r a
              ext i
              simp only [basepointAssemble, castFinCLE_apply_local, Pi.smul_apply,
                RingHom.id_apply, smul_eq_mul]
              set j := (finCongr (Nat.add_sub_of_le hm')).symm i
              induction j using Fin.addCases with
              | left k => simp
              | right k => simp
            cont := by
              apply continuous_pi
              intro i
              simp only [basepointAssemble, castFinCLE_apply_local]
              set j := (finCongr (Nat.add_sub_of_le hm')).symm i with hj
              clear_value j
              induction j using Fin.addCases with
              | left k =>
                  simp only [Fin.addCases_left]
                  exact continuous_apply _
              | right k =>
                  simp only [Fin.addCases_right]
                  exact continuous_const }
        let cBase : Fin (d + 1) → ℝ :=
          basepointAssemble d (m + 1) hm' (0 : Fin (m + 1) → ℝ)
            (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)
        have hgBase_eq : ∀ a, gBase a = L a + cBase := by
          intro a
          ext i
          change basepointAssemble d (m + 1) hm' a
              (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u) i =
            basepointAssemble d (m + 1) hm' a
              (0 : Fin (d + 1 - (m + 1)) → ℝ) i +
            basepointAssemble d (m + 1) hm' (0 : Fin (m + 1) → ℝ)
              (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u) i
          simp only [basepointAssemble, castFinCLE_apply_local]
          set j := (finCongr (Nat.add_sub_of_le hm')).symm i
          induction j using Fin.addCases with
          | left k => simp
          | right k => simp
        have hgBase_temp : Function.HasTemperateGrowth gBase := by
          have hL_temp := L.hasTemperateGrowth
          have hcBase_temp :
              Function.HasTemperateGrowth (fun _ : Fin (m + 1) → ℝ => cBase) :=
            Function.HasTemperateGrowth.const cBase
          have hsum :
              Function.HasTemperateGrowth (fun a => L a + cBase) :=
            hL_temp.add hcBase_temp
          have heq : (fun a => L a + cBase) = gBase := by
            funext a
            exact (hgBase_eq a).symm
          rwa [heq] at hsum
        -- K : CLM y ↦ CLE.symm (y, 0)
        let K : (Fin (d + 1) → ℝ) →L[ℝ] NPointSpacetime d (n + 1) :=
          (basepointDiffPairCLE d n).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.inl ℝ (Fin (d + 1) → ℝ) (NPointSpacetime d n))
        let c_g : NPointSpacetime d (n + 1) :=
          (basepointDiffPairCLE d n).symm ((0 : Fin (d + 1) → ℝ), gDiff)
        have hg_eq : ∀ a, g a = K (gBase a) + c_g := by
          intro a
          show (basepointDiffPairCLE d n).symm (gBase a, gDiff) =
              (basepointDiffPairCLE d n).symm (gBase a, (0 : NPointSpacetime d n)) +
              (basepointDiffPairCLE d n).symm ((0 : Fin (d + 1) → ℝ), gDiff)
          rw [← ContinuousLinearEquiv.map_add]
          congr 1
          simp
        have hg_temp : Function.HasTemperateGrowth g := by
          have hK_temp := K.hasTemperateGrowth
          have hK_comp :
              Function.HasTemperateGrowth (fun a => K (gBase a)) :=
            hK_temp.comp hgBase_temp
          have hc_g_temp :
              Function.HasTemperateGrowth (fun _ : Fin (m + 1) → ℝ => c_g) :=
            Function.HasTemperateGrowth.const c_g
          have hsum :
              Function.HasTemperateGrowth (fun a => K (gBase a) + c_g) :=
            hK_comp.add hc_g_temp
          have heq : (fun a => K (gBase a) + c_g) = g := by
            funext a
            exact (hg_eq a).symm
          rwa [heq] at hsum
        -- Upper bound: ‖a‖ ≤ ‖g a‖ ≤ 1 * (1 + ‖g a‖)^1
        have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ a, ‖a‖ ≤ C * (1 + ‖g a‖) ^ k := by
          refine ⟨1, 1, ?_⟩
          intro a
          -- Step 1: ‖a‖ ≤ ‖gBase a‖  (each coord of a appears in gBase a)
          have hhead : ‖a‖ ≤ ‖gBase a‖ := by
            rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
            intro i
            have hμ_eq : gBase a
                ((finCongr (Nat.add_sub_of_le hm'))
                  (Fin.castAdd (d + 1 - (m + 1)) (Fin.rev i))) = a i := by
              simp only [gBase, basepointAssemble, castFinCLE_apply_local]
              have hj_eq :
                  (finCongr (Nat.add_sub_of_le hm')).symm
                    ((finCongr (Nat.add_sub_of_le hm'))
                      (Fin.castAdd (d + 1 - (m + 1)) (Fin.rev i))) =
                    Fin.castAdd (d + 1 - (m + 1)) (Fin.rev i) := by
                simp
              rw [hj_eq, Fin.addCases_left, Fin.rev_rev]
            rw [← hμ_eq]
            exact norm_le_pi_norm (gBase a) _
          -- Step 2: g a 0 = gBase a, so ‖gBase a‖ = ‖g a 0‖
          have hg0 : g a 0 = gBase a := by
            ext μ
            show (gBase a) μ + diffVarSection d n gDiff 0 μ = gBase a μ
            rw [diffVarSection_zero]
            simp
          have h0 : ‖gBase a‖ ≤ ‖g a 0‖ := by rw [hg0]
          have h1 : ‖g a 0‖ ≤ ‖g a‖ := norm_le_pi_norm (g a) 0
          calc
            ‖a‖ ≤ ‖gBase a‖ := hhead
            _ ≤ ‖g a 0‖ := h0
            _ ≤ ‖g a‖ := h1
            _ ≤ 1 * (1 + ‖g a‖) ^ (1 : ℕ) := by
                simp [pow_one]
        -- Build G := f ∘ g as Schwartz map.
        let G : SchwartzMap (Fin (m + 1) → ℝ) ℂ :=
          SchwartzMap.compCLM ℂ (g := g) hg_temp hg_upper f
        have hG_apply : ∀ a, G a = f (g a) := by
          intro a
          rfl
        -- G is integrable on (Fin (m+1) → ℝ).
        have hG_int :
            MeasureTheory.Integrable
              (fun a : Fin (m + 1) → ℝ => G a)
              (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (m + 1) → ℝ)) := by
          simpa using
            (SchwartzMap.integrable
              (μ := (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (m + 1) → ℝ))) G)
        -- Transfer via piFinSuccAbove to ℝ × (Fin m → ℝ).
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
        have hmp :
            MeasureTheory.MeasurePreserving e
              (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (m + 1) → ℝ))
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
                (MeasureTheory.volume :
                  MeasureTheory.Measure (Fin m → ℝ))) := by
          simpa [e] using
            (MeasureTheory.volume_preserving_piFinSuccAbove
              (fun _ : Fin (m + 1) => ℝ) 0)
        have hpair_int :
            MeasureTheory.Integrable
              (fun p : ℝ × (Fin m → ℝ) => G (Fin.cons p.1 p.2))
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
                (MeasureTheory.volume :
                  MeasureTheory.Measure (Fin m → ℝ))) := by
          have hiff :=
            hmp.symm.integrable_comp_emb e.symm.measurableEmbedding
              (g := fun a : Fin (m + 1) → ℝ => G a)
          simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hiff.2 hG_int
        -- The target measure Measure.pi equals volume on Fin m → ℝ.
        have hint0 :
            MeasureTheory.Integrable
              (fun p : ℝ × (Fin m → ℝ) => G (Fin.cons p.1 p.2))
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
                (MeasureTheory.Measure.pi fun _ : Fin m =>
                  (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := hpair_int
        -- Congr to the actual integrand.
        refine hint0.congr ?_
        refine Filter.Eventually.of_forall ?_
        intro z
        show G (Fin.cons z.1 z.2) = _
        rw [hG_apply]
        show f (g (Fin.cons z.1 z.2)) = _
        rfl
      have integ := MeasureTheory.integral_prod _ hint
      exact integ.symm.trans hFubini

private lemma integrateHeadBlock_flattenBasepointDiff_aux
    (d : ℕ) [NeZero d] (n : ℕ)
    (f : SchwartzNPointSpace d (n + 1))
    (u : Fin (n * (d + 1)) → ℝ) :
    integrateHeadBlock (m := d + 1) (n := n * (d + 1))
      (flattenBasepointDiffSchwartz d n f) u =
    ∫ a : Fin (d + 1) → ℝ,
      f (fun k μ => a μ + diffVarSection d n ((flattenDiffCLE d n).symm u) k μ) := by
  have hm : d + 1 ≤ d + 1 := le_refl _
  have hab_eq : n * (d + 1) = (d + 1 - (d + 1)) + n * (d + 1) := by omega
  have hreix : (d + 1) + n * (d + 1) =
      (d + 1) + ((d + 1 - (d + 1)) + n * (d + 1)) := by omega
  -- Cast u up to aux_m's shape.
  let u' : Fin ((d + 1 - (d + 1)) + n * (d + 1)) → ℝ := castFinCLE hab_eq u
  -- Inline naturality for integrateHeadBlock w.r.t. tail reindex.
  have hnat_m : ∀ (p : ℕ) (a b : ℕ) (hab0 : a = b) (h : p + a = p + b)
      (F : SchwartzMap (Fin (p + a) → ℝ) ℂ) (y : Fin b → ℝ),
      integrateHeadBlock (m := p) (n := b) (reindexSchwartzFin h F) y =
        integrateHeadBlock (m := p) (n := a) F ((castFinCLE hab0).symm y) := by
    intro p
    induction p with
    | zero =>
        intro a b hab0 h F y
        simp only [integrateHeadBlock, reindexSchwartzFin_apply]
        apply congrArg F
        ext i
        simp only [castFinCLE_symm_apply]
        apply congrArg y
        apply Fin.ext
        rfl
    | succ k ihk =>
        intro a b hab0 h F y
        show integrateHeadBlock (m := k) (n := b)
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add k b)
                (reindexSchwartzFin h F))) y =
            integrateHeadBlock (m := k) (n := a)
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add k a) F))
              ((castFinCLE hab0).symm y)
        have h' : k + a = k + b := by omega
        have hs :
            sliceIntegral (reindexSchwartzFin (Nat.succ_add k b)
              (reindexSchwartzFin h F)) =
            reindexSchwartzFin h'
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add k a) F)) := by
          apply SchwartzMap.ext
          intro z
          simp only [reindexSchwartzFin_apply, sliceIntegral_apply, sliceIntegralRaw]
          congr 1
          funext tt
          apply congrArg F
          ext i
          rcases i with ⟨iv, hiv⟩
          cases iv with
          | zero =>
              simp only [castFinCLE_symm_apply, Fin.cons]
              rfl
          | succ iv' =>
              simp only [castFinCLE_symm_apply, Fin.cons]
              rfl
        rw [hs]
        exact ihk a b hab0 h' _ y
  -- Apply aux_m and naturality.
  have haux := integrateHeadBlock_flattenBasepointDiff_aux_m d n (d + 1) hm f u'
  have hLHS := hnat_m (d + 1) _ _ hab_eq hreix
    (flattenBasepointDiffSchwartz d n f) u'
  have hu'_symm : (castFinCLE hab_eq).symm u' = u := by
    ext i
    simp [u']
  rw [hu'_symm] at hLHS
  rw [← hLHS, haux]
  -- Simplify splitLast.
  have hsL : splitLast (d + 1 - (d + 1)) (n * (d + 1)) u' = u := by
    ext j
    show u' (Fin.natAdd (d + 1 - (d + 1)) j) = u j
    simp only [u', castFinCLE_apply_local]
    apply congrArg u
    apply Fin.ext
    simp [Fin.val_natAdd]
  simp_rw [hsL]
  -- Simplify basepointAssemble at m = d+1: it equals aHead ∘ Fin.rev.
  have hba : ∀ (aHead : Fin (d + 1) → ℝ),
      basepointAssemble d (d + 1) hm aHead
        (splitFirst (d + 1 - (d + 1)) (n * (d + 1)) u') =
      fun μ => aHead (Fin.rev μ) := by
    intro aHead
    ext μ
    show basepointAssemble d (d + 1) hm aHead
        (splitFirst (d + 1 - (d + 1)) (n * (d + 1)) u') μ = aHead (Fin.rev μ)
    simp only [basepointAssemble, castFinCLE_apply_local]
    set j := (finCongr (Nat.add_sub_of_le hm)).symm μ with hj_def
    have hj_val : j.val = μ.val := by simp [hj_def]
    have hj_lt : j.val < d + 1 := by
      have := μ.isLt; omega
    have hj_cast : j = Fin.castAdd (d + 1 - (d + 1)) ⟨j.val, hj_lt⟩ := by
      apply Fin.ext
      simp [Fin.val_castAdd]
    rw [hj_cast, Fin.addCases_left]
    apply congrArg aHead
    apply Fin.ext
    simp [hj_val]
  simp_rw [hba]
  -- Change of variable via (piCongrLeft Fin.revPerm).symm (aHead ↦ aHead ∘ Fin.rev).
  let ψ : (Fin (d + 1) → ℝ) ≃ᵐ (Fin (d + 1) → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) => ℝ) Fin.revPerm).symm
  have hmp : MeasureTheory.MeasurePreserving ψ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (d + 1) → ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (d + 1) → ℝ)) :=
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin (d + 1) => ℝ) Fin.revPerm).symm _
  -- ψ aHead μ = aHead (Fin.rev μ) via piCongrLeft_symm_apply.
  have hψ_apply : ∀ (aHead : Fin (d + 1) → ℝ) (μ : Fin (d + 1)),
      ψ aHead μ = aHead (Fin.rev μ) := by
    intro aHead μ
    show (Equiv.piCongrLeft (fun _ : Fin (d + 1) => ℝ) Fin.revPerm).symm aHead μ
      = aHead (Fin.rev μ)
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  -- Change variable: ∫ aHead, integrand (ψ aHead) = ∫ a, integrand a
  rw [show
      (∫ aHead : Fin (d + 1) → ℝ,
        f (fun k μ =>
          aHead (Fin.rev μ) +
          diffVarSection d n ((flattenDiffCLE d n).symm u) k μ))
      =
      (∫ aHead : Fin (d + 1) → ℝ,
        (fun a : Fin (d + 1) → ℝ =>
          f (fun k μ =>
            a μ +
            diffVarSection d n ((flattenDiffCLE d n).symm u) k μ)) (ψ aHead))
      from by
        refine MeasureTheory.integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro aHead
        simp only [hψ_apply]]
  exact hmp.integral_comp' (g := fun a : Fin (d + 1) → ℝ =>
    f (fun k μ =>
      a μ +
      diffVarSection d n ((flattenDiffCLE d n).symm u) k μ))

private lemma integrateHeadBlock_transport_eq_diffVarReduction
    (d : ℕ) [NeZero d] (n : ℕ)
    (f : SchwartzNPointSpace d (n + 1)) :
    integrateHeadBlock (m := d + 1) (n := n * (d + 1))
      (flattenBasepointDiffSchwartz d n f) =
    flattenSchwartzNPoint (d := d) (diffVarReduction d n f) := by
  ext u
  simpa [diffVarReduction] using
    integrateHeadBlock_flattenBasepointDiff_aux d n f u

/-- The kernel theorem isolated in the blueprint: a diagonal-translation
invariant tempered distribution vanishes on the kernel of
`diffVarReduction`. The preferred proof route is the head-block transport
argument recorded in the blueprint. -/
private lemma translationInvariant_vanishesOn_diffVarReduction_kernel
    (d : ℕ) [NeZero d]
    (n : ℕ)
    {W : SchwartzNPointSpace d (n + 1) → ℂ}
    (hW_cont : Continuous W)
    (hW_lin : IsLinearMap ℂ W)
    (hW_transl : ∀ (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d (n + 1)),
      (∀ x : NPointSpacetime d (n + 1),
        g.toFun x = f.toFun (fun i => x i + a)) →
      W f = W g) :
    ∀ f : SchwartzNPointSpace d (n + 1),
      diffVarReduction d n f = 0 → W f = 0 := by
  intro f hf
  let T := transportedWHeadBlockCLM d n W hW_cont hW_lin
  let F := flattenBasepointDiffSchwartz d n f
  have hT :
      IsHeadBlockTranslationInvariantSchwartzCLM
        (m := d + 1) (n := n * (d + 1)) T :=
    transportedWHeadBlockInvariant d n hW_cont hW_lin hW_transl
  have hIntF :
      integrateHeadBlock (m := d + 1) (n := n * (d + 1)) F = 0 := by
    simpa [F, hf] using integrateHeadBlock_transport_eq_diffVarReduction d n f
  have hmap :
      T F = T 0 := by
    exact map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant
      (m := d + 1) (n := n * (d + 1)) T hT F 0 (by
        have h0 : integrateHeadBlock (m := d + 1) (n := n * (d + 1)) 0 = 0 := by
          have h := integrateHeadBlock_sub (m := d + 1) (n := n * (d + 1)) F F
          simp [sub_self] at h; exact h
        rw [hIntF, h0])
  have hzeroT : T 0 = 0 := by
    have hW0 : W (0 : SchwartzNPointSpace d (n + 1)) = 0 := by
      simpa using (hW_lin.map_smul (0 : ℂ) (0 : SchwartzNPointSpace d (n + 1)))
    simpa [T, transportedWHeadBlockCLM, unflattenBasepointDiffSchwartz] using hW0
  calc
    W f = T F := by
      simp [T, F, transportedWHeadBlockCLM,
        unflatten_flattenBasepointDiffSchwartz]
    _ = T 0 := hmap
    _ = 0 := hzeroT

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
  let φ₀ : SchwartzMap (BasepointSpace d) ℂ := normalizedBasepointBump d
  have hφ₀_int : ∫ a : BasepointSpace d, φ₀ a = 1 := by
    simpa [φ₀] using integral_normalizedBasepointBump d
  let φSect : SchwartzNPointSpace d n →L[ℂ] SchwartzNPointSpace d (n + 1) :=
    sectionOfCLM d n φ₀
  have hsection_right_inv :
      ∀ g : SchwartzNPointSpace d n, diffVarReduction d n (φSect g) = g := by
    intro g
    simpa [φSect, sectionOfCLM_apply] using
      diffVarReduction_sectionOf d n φ₀ hφ₀_int g
  have hker :
      ∀ f : SchwartzNPointSpace d (n + 1),
        diffVarReduction d n f = 0 → W (n + 1) f = 0 := by
    intro f hf
    exact translationInvariant_vanishesOn_diffVarReduction_kernel d n
      (hW_cont := hW_tempered (n + 1))
      (hW_lin := hW_linear (n + 1))
      (hW_transl := hW_transl (n + 1))
      f hf
  let w : SchwartzNPointSpace d n → ℂ := fun g => W (n + 1) (φSect g)
  have hw_cont : Continuous w := by
    exact (hW_tempered (n + 1)).comp φSect.continuous
  have hw_lin : IsLinearMap ℂ w := by
    refine { map_add := ?_, map_smul := ?_ }
    · intro g h
      show W (n + 1) (sectionOfCLM d n φ₀ (g + h)) =
          W (n + 1) (sectionOfCLM d n φ₀ g) + W (n + 1) (sectionOfCLM d n φ₀ h)
      rw [(sectionOfCLM d n φ₀).map_add, (hW_linear (n + 1)).map_add]
    · intro c g
      show W (n + 1) (sectionOfCLM d n φ₀ (c • g)) = c • W (n + 1) (sectionOfCLM d n φ₀ g)
      rw [(sectionOfCLM d n φ₀).map_smul, (hW_linear (n + 1)).map_smul]
  have hw_det :
      ∀ f : SchwartzNPointSpace d (n + 1), W (n + 1) f = w (diffVarReduction d n f) := by
    intro f
    have hred :
        diffVarReduction d n
          (f - φSect (diffVarReduction d n f)) = 0 := by
      simpa [φSect, sectionOfCLM_apply] using
        diffVarReduction_sub_sectionOf_eq_zero d n φ₀ hφ₀_int f
    have hzero :
        W (n + 1) (f - φSect (diffVarReduction d n f)) = 0 := hker _ hred
    have hlin := hW_linear (n + 1)
    rw [hlin.map_sub, sub_eq_zero] at hzero
    simpa [w] using hzero
  exact ⟨w, hw_cont, hw_lin, hw_det⟩

variable (d) in
/-- Deferred forward-direction helper: lift `F` from `ProductForwardTube` to
`ForwardTube`.

This helper is not used by the current main theorem
`spectralConditionDistribution_of_forwardTubeAnalyticity`; it is retained only
as scaffolding for a possible future reverse direction under a different
analytic growth surface. -/
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
      (∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ z, z ∈ ForwardTube d (n + 1) → ‖W_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N) ∧
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
  · -- Growth + boundary values
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
  classical
  let z₀ : Fin (d + 1) → ℂ := fun μ => if μ = 0 then Complex.I else 0
  have hz₀ : InOpenForwardCone d (fun μ => (z₀ μ).im) := by
    constructor
    · simp [z₀]
    · rw [MinkowskiSpace.minkowskiNormSq_decomp]
      simp [z₀, MinkowskiSpace.spatialNormSq]
  let F : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun ζ => W_analytic (fun k μ => z₀ μ + complexDiffVarSection d n ζ k μ)
  have hF_holo : DifferentiableOn ℂ F (ProductForwardTube d n) := by
    intro ζ hζ
    have hsec :
        (fun k μ => z₀ μ + complexDiffVarSection d n ζ k μ) ∈ ForwardTube d (n + 1) := by
      exact shifted_section_maps_productTube_to_forwardTube (d := d) n z₀ hz₀ ζ hζ
    have hmaps :
        Set.MapsTo
          (fun ζ : Fin n → Fin (d + 1) → ℂ =>
            fun k μ => z₀ μ + complexDiffVarSection d n ζ k μ)
          (ProductForwardTube d n) (ForwardTube d (n + 1)) := by
      intro ξ hξ
      exact shifted_section_maps_productTube_to_forwardTube (d := d) n z₀ hz₀ ξ hξ
    have hsec_diff :
        DifferentiableAt ℂ
          (fun ζ : Fin n → Fin (d + 1) → ℂ =>
            fun k μ => z₀ μ + complexDiffVarSection d n ζ k μ) ζ := by
      let c : Fin (n + 1) → Fin (d + 1) → ℂ := fun k μ => z₀ μ
      have hderiv :
          HasFDerivAt
            (fun ζ' : Fin n → Fin (d + 1) → ℂ => complexDiffVarSection d n ζ' + c)
            ((complexDiffVarSection d n).toContinuousLinearMap) ζ := by
        simpa [c] using ((complexDiffVarSection d n).toContinuousLinearMap.hasFDerivAt).add_const c
      simpa [c, Pi.add_apply] using hderiv.differentiableAt
    exact (hWa_holo _ hsec).comp ζ hsec_diff.differentiableWithinAt hmaps
  have hF_bv :
      ∀ (φ : SchwartzNPointSpace d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k : Fin n, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d n,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (φ x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (w φ)) := by
    intro φ η hη
    let φ₀ : SchwartzMap (BasepointSpace d) ℂ := normalizedBasepointBump d
    have hφ₀_int : ∫ a : BasepointSpace d, φ₀ a = 1 := by
      simpa [φ₀] using integral_normalizedBasepointBump d
    let fφ : SchwartzNPointSpace d (n + 1) := sectionOf d n φ₀ φ
    have hfφ_red : diffVarReduction d n fφ = φ := by
      simpa [fφ, φ₀] using
        diffVarReduction_sectionOf d n φ₀ hφ₀_int φ
    let η' : Fin (n + 1) → Fin (d + 1) → ℝ :=
      fun k μ =>
        Fin.cases
          ((z₀ μ).im)
          (fun i => (z₀ μ).im + ∑ j : Fin (i.val + 1), η ⟨j.val, by omega⟩ μ) k
    have hη'_succ :
        ∀ (i : Fin n) (μ : Fin (d + 1)),
          η' i.succ μ - η' i.castSucc μ = η i μ := by
      cases n with
      | zero =>
          intro i
          exact Fin.elim0 i
      | succ n =>
          intro i μ
          refine Fin.cases ?_ ?_ i
          · change
              ((z₀ μ).im + ∑ j : Fin (0 + 1), η ⟨j.val, by omega⟩ μ) - (z₀ μ).im =
                η 0 μ
            simp
          · intro j
            change
              ((z₀ μ).im + ∑ x : Fin (j.val + 2), η ⟨x.val, by omega⟩ μ) -
                  ((z₀ μ).im + ∑ x : Fin (j.val + 1), η ⟨x.val, by omega⟩ μ) =
                η j.succ μ
            have hsplit :
                (∑ x : Fin (j.val + 2), η ⟨x.val, by omega⟩ μ) =
                  (∑ x : Fin (j.val + 1), η ⟨x.val, by omega⟩ μ) + η j.succ μ := by
              simpa [Fin.val_castSucc, Fin.val_last] using
                (Fin.sum_univ_castSucc
                  (f := fun x : Fin (j.val + 2) => η ⟨x.val, by omega⟩ μ))
            linarith
    have hη' : InForwardCone d (n + 1) η' := by
      intro k
      refine Fin.cases ?_ ?_ k
      · simpa [η', z₀]
      · intro i
        convert hη i using 1
        ext μ
        exact hη'_succ i μ
    have hbase := hWa_bv fφ η' hη'
    have hchange :
        ∀ ε : ℝ,
          ∫ x : NPointSpacetime d (n + 1),
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η' k μ) * Complex.I) * (fφ x)
          =
          ∫ ξ : NPointSpacetime d n,
            F (fun k μ => ↑(ξ k μ) + ε * ↑(η k μ) * Complex.I) * (φ ξ) := by
      intro ε
      sorry
    have hbase' :
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d (n + 1),
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η' k μ) * Complex.I) * (fφ x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (w φ)) := by
      simpa [F, fφ, hw_det, hfφ_red] using hbase
    convert hbase' using 1
    funext ε
    exact (hchange ε).symm
  exact ⟨F, hF_holo, hF_bv⟩

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
/-- Deferred zero-point forward-direction helper.

This is not used by the current one-way main theorem. -/
lemma forwardTubeAnalyticity_zero
    {W : (n : ℕ) → SchwartzNPointSpace d n → ℂ}
    (hW_tempered : ∀ n, Continuous (W n))
    (hW_linear : ∀ n, IsLinearMap ℂ (W n)) :
    ∃ (W_analytic : (Fin 0 → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d 0) ∧
      (∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ z, z ∈ ForwardTube d 0 → ‖W_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N) ∧
      (∀ (f : SchwartzNPointSpace d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
        InForwardCone d 0 η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointSpacetime d 0,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W 0 f))) := by
  let e := schwartzConstOne d
  refine ⟨fun _ => W 0 e, differentiableOn_const _, ?_, ?_⟩
  · refine ⟨‖W 0 e‖ + 1, 0, by positivity, ?_⟩
    intro z hz
    simp only [pow_zero, mul_one]
    exact le_of_lt (lt_add_of_pos_right _ zero_lt_one)
  intro f η _
  have h_integral : ∫ x : NPointSpacetime d 0, W 0 e * f x = W 0 f := by
    rw [volume_nPointSpacetime_zero_eq_dirac, MeasureTheory.integral_dirac]
    have hf_eq := schwartz_zero_eq_smul d f
    conv_rhs => rw [hf_eq, (hW_linear 0).map_smul, smul_eq_mul]
    ring
  refine Filter.Tendsto.congr (fun ε => ?_) tendsto_const_nhds
  change W 0 f = ∫ x : NPointSpacetime d 0, W 0 e * f x
  exact h_integral.symm

/-! ### Main One-Way Theorem -/

variable (d) in
/-- **Spectral condition from forward tube analyticity** (one-way direction).

    `ForwardTubeAnalyticity d W → SpectralConditionDistribution d W`.

    Uses the converse Paley-Wiener-Schwartz tube theorem (Vladimirov §26): a
    holomorphic function on the forward tube with global polynomial-growth
    bound and tempered boundary values comes from a tempered distribution whose
    Fourier transform has support in the product forward momentum cone.

    Only this direction is needed for the GNS spectral-condition bridge
    (`wfn_spectralConditionDistribution` in `GNSHilbertSpace.lean`).

    The converse direction `SpectralConditionDistribution → ForwardTubeAnalyticity`
    under the global polynomial-growth hypothesis is deferred: Fourier-Laplace
    transforms of cone-supported tempered distributions generically have
    Vladimirov slow growth (boundary blow-up indexed by distance to `∂V₊`), not a
    uniform `(1 + ‖z‖)^N` bound on the whole tube.

    Ref: Streater-Wightman, Theorem 3-5; Reed-Simon Vol. II, §IX.3. -/
theorem spectralConditionDistribution_of_forwardTubeAnalyticity
    {W : (n : ℕ) → SchwartzNPointSpace d n → ℂ}
    (hW_tempered : ∀ n, Continuous (W n))
    (hW_linear : ∀ n, IsLinearMap ℂ (W n))
    (hW_transl : ∀ (n : ℕ) (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d n),
      (∀ x : NPointSpacetime d n, g.toFun x = f.toFun (fun i => x i + a)) →
      W n f = W n g)
    (hFTA : ForwardTubeAnalyticity d W) :
    SpectralConditionDistribution d W := by
  intro n
  obtain ⟨W_analytic, hWa_holo, hWa_growth, hWa_bv⟩ := hFTA (n + 1)
  obtain ⟨w, hw_cont, hw_lin, hw_det⟩ :=
    exists_diffVar_distribution d hW_tempered hW_linear hW_transl n
  refine ⟨w, hw_cont, hw_lin, hw_det, ?_⟩
  obtain ⟨F, hF_holo, hF_bv⟩ :=
    productTube_function_of_forwardTube d
      hW_tempered hW_linear hW_transl w hw_cont hw_lin hw_det
      W_analytic hWa_holo hWa_bv
  exact converse_paleyWiener_tube d n F hF_holo w hw_cont hw_lin hF_bv
