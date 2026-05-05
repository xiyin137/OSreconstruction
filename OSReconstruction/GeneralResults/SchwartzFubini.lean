/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OSReconstruction.GeneralResults.FinProductIntegral
import OSReconstruction.SCV.SchwartzPrependField

/-!
# Fubini Exchange for Schwartz-Valued Integrals

A continuous linear functional on Schwartz space commutes with
parameter integrals of Schwartz-valued families.

## Main result

`schwartz_clm_fubini_exchange`: For T : S(ℝᵐ) →L[ℂ] ℂ and a
continuous family g : ℝᵐ → S(ℝᵐ) with polynomial seminorm growth,
there exists a Schwartz function Φ such that
  Φ(ξ) = ∫ g(x)(ξ) f(x) dx  and  T(Φ) = ∫ T(g(x)) f(x) dx.

## Mathematical content

This combines two facts:
1. The Schwartz-valued integral Φ = ∫ g(x) f(x) dx is well-defined
   as a Schwartz function (polynomial growth of seminorms × rapid
   decay of f gives convergent Schwartz-valued integral).
2. T is continuous linear, so T(∫ ...) = ∫ T(...) (CLM exchange).

Both follow from the nuclearity/Fréchet structure of Schwartz space.

## References

- Hörmander, "The Analysis of Linear PDOs I", Ch. 5
- Reed-Simon I, §V.3
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory
noncomputable section

variable {m : ℕ}

-- **Axiom: CLM-integral exchange for Schwartz-valued families.**
--
-- Given:
-- - T : continuous linear functional on Schwartz space
-- - g : continuous Schwartz-valued family with polynomial seminorm growth
-- - f : Schwartz test function
--
-- Conclusion: there exists a Schwartz function Φ (the Schwartz-valued integral)
-- such that Φ(ξ) = ∫ g(x)(ξ) f(x) dx pointwise, and T(Φ) = ∫ T(g(x)) f(x) dx.
--
-- The axiom constructs Φ rather than taking it as input, to avoid redundancy
-- and ensure coherence. The continuity hypothesis on g (in Schwartz topology)
-- ensures the Bochner integral is well-defined.
axiom schwartz_clm_fubini_exchange {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    -- Continuity of the Schwartz-valued family (ensures Bochner integrability)
    (hg_cont : Continuous g)
    -- Uniform seminorm bound (polynomial growth in x)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x : Fin m → ℝ),
        SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ξ : Fin m → ℝ, Φ ξ = ∫ x : Fin m → ℝ, g x ξ * f x) ∧
      (T Φ = ∫ x : Fin m → ℝ, T (g x) * f x)

private def clmOfContinuousIsLinear
    {V : Type*} [AddCommMonoid V] [Module ℂ V] [TopologicalSpace V]
    (w : V → ℂ) (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w) :
    V →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := w
      map_add' := fun x y => hw_lin.map_add x y
      map_smul' := fun c x => hw_lin.map_smul c x }
  cont := hw_cont

private noncomputable def finiteDimCoordCLE
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

private abbrev castFinCLE {a b : ℕ} (h : a = b) :
    (Fin a → ℝ) ≃L[ℝ] (Fin b → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin b => ℝ) (finCongr h)

@[simp] private lemma castFinCLE_apply {a b : ℕ} (h : a = b)
    (x : Fin a → ℝ) (i : Fin b) :
    castFinCLE h x i = x ((finCongr h).symm i) := rfl

@[simp] private lemma castFinCLE_symm_apply {a b : ℕ} (h : a = b)
    (x : Fin b → ℝ) (i : Fin a) :
    (castFinCLE h).symm x i = x ((finCongr h) i) := rfl

private noncomputable def toCoordSchwartz
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    SchwartzMap E ℂ →L[ℂ] SchwartzMap (Fin (Module.finrank ℝ E) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finiteDimCoordCLE E).symm

private noncomputable def fromCoordSchwartz
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    SchwartzMap (Fin (Module.finrank ℝ E) → ℝ) ℂ →L[ℂ] SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finiteDimCoordCLE E)

@[simp] private lemma toCoordSchwartz_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap E ℂ) (x : Fin (Module.finrank ℝ E) → ℝ) :
    toCoordSchwartz E f x = f ((finiteDimCoordCLE E).symm x) := rfl

@[simp] private lemma fromCoordSchwartz_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap (Fin (Module.finrank ℝ E) → ℝ) ℂ) (x : E) :
    fromCoordSchwartz E f x = f ((finiteDimCoordCLE E) x) := rfl

private lemma seminorm_clm_family_poly_bound
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : SchwartzMap A ℂ →L[ℂ] SchwartzMap B ℂ)
    (F : ℝ → SchwartzMap A ℂ)
    (hF_poly : ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (F t) ≤ C * (1 + ‖t‖) ^ N) :
    ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (L (F t)) ≤ C * (1 + ‖t‖) ^ N := by
  intro k j
  let Lreal : SchwartzMap A ℂ →ₗ[ℝ] SchwartzMap B ℂ :=
    { toFun := fun f => L f
      map_add' := fun f g => L.map_add f g
      map_smul' := by
        intro r f
        change L ((r : ℂ) • f) = (r : ℂ) • L f
        exact L.map_smul (r : ℂ) f }
  let qkj : Seminorm ℝ (SchwartzMap A ℂ) :=
    (schwartzSeminormFamily ℝ B ℂ (k, j)).comp Lreal
  have hqkj_cont : Continuous ⇑qkj :=
    ((schwartz_withSeminorms ℝ B ℂ).continuous_seminorm (k, j)).comp L.continuous
  obtain ⟨s, C₀, _, hbound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℝ A ℂ) qkj hqkj_cont
  let Ds : ℕ × ℕ → ℝ := fun i => (hF_poly i.1 i.2).choose
  let Ns : ℕ × ℕ → ℕ := fun i => (hF_poly i.1 i.2).choose_spec.choose
  have hDs_pos : ∀ i, 0 < Ds i :=
    fun i => (hF_poly i.1 i.2).choose_spec.choose_spec.1
  have hDs_nonneg : ∀ i, 0 ≤ Ds i := fun i => (hDs_pos i).le
  have hDs_bound : ∀ (i : ℕ × ℕ) t,
      SchwartzMap.seminorm ℝ i.1 i.2 (F t) ≤
        Ds i * (1 + ‖t‖) ^ Ns i := by
    intro i t
    exact (hF_poly i.1 i.2).choose_spec.choose_spec.2 t
  let Nmax : ℕ := s.sup Ns
  let Cbase : ℝ := (C₀ : ℝ) * ∑ i ∈ s, Ds i
  have hCbase_nonneg : 0 ≤ Cbase :=
    mul_nonneg C₀.prop (Finset.sum_nonneg (fun i _ => hDs_nonneg i))
  refine ⟨Cbase + 1, Nmax, by linarith, fun t => ?_⟩
  have hq_eq :
      qkj (F t) = SchwartzMap.seminorm ℝ k j (L (F t)) := rfl
  rw [← hq_eq]
  have h1 : qkj (F t) ≤
      (C₀ : ℝ) *
        (s.sup (schwartzSeminormFamily ℝ A ℂ)) (F t) := by
    have h := hbound (F t)
    simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h
    linarith
  have h2 : (s.sup (schwartzSeminormFamily ℝ A ℂ)) (F t) ≤
      ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ Ns i := by
    apply Seminorm.finset_sup_apply_le
      (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (hDs_nonneg i) (pow_nonneg (by linarith [norm_nonneg t]) _)))
    intro ⟨p, q⟩ hi
    simp only [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hDs_bound (p, q) t).trans
      (Finset.single_le_sum
        (fun i _ => mul_nonneg (hDs_nonneg i)
          (pow_nonneg (by linarith [norm_nonneg t]) _)) hi)
  have h3 : ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ Ns i ≤
      (∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ Nmax := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hDs_nonneg i)
    exact pow_le_pow_right₀ (by linarith [norm_nonneg t])
      (Finset.le_sup (f := Ns) hi)
  calc
    qkj (F t)
        ≤ (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ A ℂ)) (F t) := h1
    _ ≤ (C₀ : ℝ) * ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ Ns i :=
        mul_le_mul_of_nonneg_left h2 C₀.prop
    _ ≤ (C₀ : ℝ) * ((∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ Nmax) :=
        mul_le_mul_of_nonneg_left h3 C₀.prop
    _ = Cbase * (1 + ‖t‖) ^ Nmax := by ring
    _ ≤ (Cbase + 1) * (1 + ‖t‖) ^ Nmax := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (pow_nonneg (by linarith [norm_nonneg t]) _)

private noncomputable def normedUnitBumpSchwartzReal : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => ((b.normed MeasureTheory.volume x : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

private lemma integral_normedUnitBumpSchwartzReal :
    ∫ x : ℝ, normedUnitBumpSchwartzReal x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have happly :
      (fun x : ℝ => normedUnitBumpSchwartzReal x) =
        fun x : ℝ => ((b.normed MeasureTheory.volume x : ℝ) : ℂ) := by
    funext x
    have hf_smooth : ContDiff ℝ (⊤ : ENat)
        (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) := by
      exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
    have hf_compact :
        HasCompactSupport (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) :=
      b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
    simpa [normedUnitBumpSchwartzReal, b] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x)
  rw [happly, integral_complex_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.integral_normed (μ := MeasureTheory.volume))

private theorem integral_finSucc_cons_eq_complex
    {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℂ) :
    (∫ z : ℝ × (Fin m → ℝ), f (Fin.cons z.1 z.2)
        ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.Measure.pi fun _ : Fin m =>
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)))) =
      (∫ x : Fin (m + 1) → ℝ, f x
        ∂(MeasureTheory.Measure.pi fun _ : Fin (m + 1) =>
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := by
  have h :=
    ((MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ => (MeasureTheory.volume : MeasureTheory.Measure ℝ)) 0).symm).integral_comp'
      (g := f)
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Fin.cons_zero] using h

private noncomputable def normedUnitBumpSchwartzFin : ∀ n : ℕ,
    SchwartzMap (Fin n → ℝ) ℂ
  | 0 => by
      let f : (Fin 0 → ℝ) → ℂ := fun _ => 1
      have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
        simpa [f] using
          (contDiff_const : ContDiff ℝ (⊤ : ENat) (fun _ : Fin 0 → ℝ => (1 : ℂ)))
      have hf_compact : HasCompactSupport f := by
        simpa [HasCompactSupport, tsupport, Function.support, f] using
          (show IsCompact (Set.univ : Set (Fin 0 → ℝ)) from isCompact_univ)
      exact hf_compact.toSchwartzMap hf_smooth
  | n + 1 => SCV.prependField normedUnitBumpSchwartzReal (normedUnitBumpSchwartzFin n)

private lemma integral_normedUnitBumpSchwartzFin :
    ∀ n : ℕ, ∫ x : Fin n → ℝ, normedUnitBumpSchwartzFin n x = 1
  | 0 => by
      have happly :
          (fun x : Fin 0 → ℝ => normedUnitBumpSchwartzFin 0 x) =
            fun _ : Fin 0 → ℝ => (1 : ℂ) := by
        funext x
        simp [normedUnitBumpSchwartzFin]
      rw [happly]
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
            MeasureTheory.Measure.dirac default := by
        simpa using
          (MeasureTheory.Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => ℝ) (x := default))
      simpa [hvol] using
        (MeasureTheory.integral_dirac (a := default) (f := fun _ : Fin 0 → ℝ => (1 : ℂ)))
  | n + 1 => by
      calc
        ∫ x : Fin (n + 1) → ℝ, normedUnitBumpSchwartzFin (n + 1) x
            =
          ∫ z : ℝ × (Fin n → ℝ), normedUnitBumpSchwartzFin (n + 1) (Fin.cons z.1 z.2) := by
              simpa using
                (integral_finSucc_cons_eq_complex
                  (f := fun x : Fin (n + 1) → ℝ => normedUnitBumpSchwartzFin (n + 1) x)).symm
        _ = ∫ z : ℝ × (Fin n → ℝ),
              normedUnitBumpSchwartzReal z.1 * normedUnitBumpSchwartzFin n z.2 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              simp [normedUnitBumpSchwartzFin, SCV.prependField_apply]
        _ = (∫ x : ℝ, normedUnitBumpSchwartzReal x) *
              (∫ y : Fin n → ℝ, normedUnitBumpSchwartzFin n y) := by
              simpa using
                (MeasureTheory.integral_prod_mul
                  (f := fun x : ℝ => normedUnitBumpSchwartzReal x)
                  (g := fun y : Fin n → ℝ => normedUnitBumpSchwartzFin n y))
        _ = 1 := by
              rw [integral_normedUnitBumpSchwartzReal, integral_normedUnitBumpSchwartzFin n]
              ring

private lemma padded_integral_collapse_point
    {n : ℕ}
    (H : ℝ → ℂ)
    (φ : SchwartzMap ℝ ℂ)
    (ρ : SchwartzMap (Fin n → ℝ) ℂ)
    (hρ : ∫ u : Fin n → ℝ, ρ u = 1) :
    (∫ x : Fin (n + 1) → ℝ,
        H (x 0) * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ))) =
      ∫ t : ℝ, H t * (φ : ℝ → ℂ) t := by
  calc
    ∫ x : Fin (n + 1) → ℝ,
        H (x 0) * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ))
        =
      ∫ z : ℝ × (Fin n → ℝ),
        H z.1 * ((φ : ℝ → ℂ) z.1 * ρ z.2) := by
        simpa using
          (integral_finSucc_cons_eq_complex
            (m := n)
            (f := fun x : Fin (n + 1) → ℝ =>
              H (x 0) * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ)))).symm
    _ = ∫ z : ℝ × (Fin n → ℝ),
        (H z.1 * (φ : ℝ → ℂ) z.1) * ρ z.2 := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        ring
    _ = (∫ t : ℝ, H t * (φ : ℝ → ℂ) t) *
        (∫ u : Fin n → ℝ, ρ u) := by
        simpa using
          (MeasureTheory.integral_prod_mul
            (μ := MeasureTheory.volume)
            (ν := MeasureTheory.volume)
            (f := fun t : ℝ => H t * (φ : ℝ → ℂ) t)
            (g := fun u : Fin n → ℝ => ρ u))
    _ = ∫ t : ℝ, H t * (φ : ℝ → ℂ) t := by
        rw [hρ, mul_one]

/-- **Finite-dimensional real-parameter CLM exchange.**

This is the finite-dimensional mixed-domain form needed by the GNS
spectral-condition argument.  The parameter space is one-dimensional (`ℝ`),
while the Schwartz functions live on a finite-dimensional real normed space
`E`; in the current downstream uses, `E` is an `NPointSpacetime` finite product
of real coordinates.

Given a continuous ℂ-linear functional `w` on `SchwartzMap E ℂ`, a continuous
Schwartz-valued family `G : ℝ → SchwartzMap E ℂ` with polynomial seminorm
growth in the real parameter, and a one-variable Schwartz test function `φ`,
the pointwise integral

`Θ ξ = ∫ t, φ t * G t ξ`

defines a Schwartz function on `E`, and `w` commutes with this integral.

This theorem is intentionally narrower than the previous arbitrary-domain
surface: finite dimensionality and positive real dimension are the exact setting
required by the current GNS uses, and this is the setting in which the result
reduces to the existing same-domain axiom `schwartz_clm_fubini_exchange`.

Lean-facing reduction plan from `schwartz_clm_fubini_exchange`:

1. Choose a continuous linear equivalence `E ≃L[ℝ] (Fin N → ℝ)` and transport
   `w` and `G t` to Schwartz functions on `Fin N → ℝ`.
2. Split `Fin N → ℝ` as `ℝ × (Fin (N - 1) → ℝ)`.
3. Choose a fixed Schwartz bump `ρ` on the tail coordinates with
   `∫ u, ρ u = 1`.
4. Apply `schwartz_clm_fubini_exchange` in dimension `N` to the padded data
   `x ↦ G (x₀)` and `x ↦ φ x₀ * ρ x_tail`.
5. Use finite-product Fubini and the normalization of `ρ` to collapse the
   `Fin N → ℝ` integral back to the real-parameter integral above.
6. Transport the resulting Schwartz function back along the chosen coordinate
   equivalence.

The remaining formal work is this coordinate-transport/padding/Fubini package;
the mathematical content is the same Schwartz-valued integral exchange as the
existing axiom, but with different finite-dimensional parameter and target
domains. -/
theorem schwartz_clm_fubini_exchange_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (w : SchwartzMap E ℂ → ℂ) (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (G : ℝ → SchwartzMap E ℂ) (hG_cont : Continuous G)
    (hG_poly : ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (G t) ≤ C * (1 + ‖t‖) ^ N)
    (hEpos : 0 < Module.finrank ℝ E)
    (φ : SchwartzMap ℝ ℂ) :
    ∃ Θ : SchwartzMap E ℂ,
      (∀ ξ : E, Θ ξ = ∫ t : ℝ, (φ : ℝ → ℂ) t * G t ξ) ∧
      w Θ = ∫ t : ℝ, w (G t) * (φ : ℝ → ℂ) t := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hEpos)
  have hn' : Module.finrank ℝ E = n + 1 := by
    simpa using hn
  let Lto : SchwartzMap E ℂ →L[ℂ] SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (castFinCLE hn').symm).comp
      (toCoordSchwartz E)
  let Lfrom : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] SchwartzMap E ℂ :=
    (fromCoordSchwartz E).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (castFinCLE hn'))
  let wCLM : SchwartzMap E ℂ →L[ℂ] ℂ :=
    clmOfContinuousIsLinear w hw_cont hw_lin
  let T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ := wCLM.comp Lfrom
  let ρ : SchwartzMap (Fin n → ℝ) ℂ := normedUnitBumpSchwartzFin n
  let fpad : SchwartzMap (Fin (n + 1) → ℝ) ℂ := SCV.prependField φ ρ
  let Gcoord : ℝ → SchwartzMap (Fin (n + 1) → ℝ) ℂ := fun t => Lto (G t)
  let g : (Fin (n + 1) → ℝ) → SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    fun x => Gcoord (x 0)
  have hGcoord_cont : Continuous Gcoord := Lto.continuous.comp hG_cont
  have hg_cont : Continuous g := hGcoord_cont.comp (continuous_apply 0)
  have hGcoord_poly :
      ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (Gcoord t) ≤ C * (1 + ‖t‖) ^ N := by
    simpa [Gcoord] using seminorm_clm_family_poly_bound Lto G hG_poly
  have hg_bound :
      ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧
        ∀ x : Fin (n + 1) → ℝ,
          SchwartzMap.seminorm ℝ k j (g x) ≤ C * (1 + ‖x‖) ^ N := by
    intro k j
    obtain ⟨C, N, hC, hCbound⟩ := hGcoord_poly k j
    refine ⟨C, N, hC, fun x => ?_⟩
    have hx : ‖x 0‖ ≤ ‖x‖ := norm_le_pi_norm x 0
    have hpow : (1 + ‖x 0‖) ^ N ≤ (1 + ‖x‖) ^ N :=
      pow_le_pow_left₀ (by linarith [norm_nonneg (x 0)])
        (by linarith) N
    exact (hCbound (x 0)).trans (mul_le_mul_of_nonneg_left hpow hC.le)
  obtain ⟨Φ, hΦ_point, hΦ_T⟩ :=
    schwartz_clm_fubini_exchange (m := n + 1) T g fpad hg_cont hg_bound
  refine ⟨Lfrom Φ, ?_, ?_⟩
  · intro ξ
    let ξc : Fin (n + 1) → ℝ := by
      exact castFinCLE hn' ((finiteDimCoordCLE E) ξ)
    have hLfrom_apply : Lfrom Φ ξ = Φ ξc := by
      simp [Lfrom, ξc, fromCoordSchwartz]
    calc
      Lfrom Φ ξ = Φ ξc := hLfrom_apply
      _ = ∫ x : Fin (n + 1) → ℝ, g x ξc * fpad x := hΦ_point ξc
      _ = ∫ x : Fin (n + 1) → ℝ,
          G (x 0) ξ * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp [g, Gcoord, Lto, fpad, ρ, ξc, toCoordSchwartz, SCV.prependField_apply]
      _ = ∫ t : ℝ, G t ξ * (φ : ℝ → ℂ) t := by
          exact padded_integral_collapse_point
            (H := fun t : ℝ => G t ξ) φ ρ
            (integral_normedUnitBumpSchwartzFin n)
      _ = ∫ t : ℝ, (φ : ℝ → ℂ) t * G t ξ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          ring
  · have h_from_to : ∀ F : SchwartzMap E ℂ, Lfrom (Lto F) = F := by
      intro F
      ext ξ
      simp [Lfrom, Lto, fromCoordSchwartz, toCoordSchwartz]
    calc
      w (Lfrom Φ)
          = ∫ x : Fin (n + 1) → ℝ, T (g x) * fpad x := by
          simpa [T, wCLM] using hΦ_T
      _ = ∫ x : Fin (n + 1) → ℝ,
          w (G (x 0)) * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp [T, wCLM, clmOfContinuousIsLinear, g, Gcoord, fpad, ρ, h_from_to,
            SCV.prependField_apply]
      _ = ∫ t : ℝ, w (G t) * (φ : ℝ → ℂ) t := by
          exact padded_integral_collapse_point
            (H := fun t : ℝ => w (G t)) φ ρ
            (integral_normedUnitBumpSchwartzFin n)

end
