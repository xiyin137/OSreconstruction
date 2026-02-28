/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import OSReconstruction.Wightman.NuclearSpaces.BochnerMinlos
import OSReconstruction.Wightman.NuclearSpaces.GaussianFieldBridge
import OSReconstruction.Wightman.NuclearSpaces.SchwartzNuclear

/-!
# Euclidean Field Theory Measures via Minlos' Theorem

This file connects the nuclear space / Minlos infrastructure to the Osterwalder-Schrader
reconstruction theorem, providing the measure-theoretic foundation for Euclidean QFT.

## Main Definitions

* `freeFieldForm` - The quadratic form Q(f) = ∫ |f̂(k)|² / (|k|² + m²) dk, defined
  concretely using the Fourier transform.
* `freeFieldCharacteristic` - C(f) = exp(-½ Q(f)), the free field characteristic functional.
* `euclideanMeasure_exists` - Existence of the Gaussian probability measure on S'(ℝᵈ).
* `schwingerTwoPoint` - Schwinger functions as moments of the Euclidean measure.

## Mathematical Background

### The Free Scalar Field Measure

For a free scalar field of mass m > 0 in d Euclidean dimensions, the **Euclidean
measure** is a Gaussian probability measure μ on the space of tempered distributions
S'(ℝᵈ). It is uniquely characterized by its characteristic functional:

  C(f) = ∫_{S'} exp(i φ(f)) dμ(φ) = exp(-½ ⟨f, (-Δ + m²)⁻¹ f⟩_{L²})

where:
- f ∈ S(ℝᵈ) is a Schwartz test function
- φ ∈ S'(ℝᵈ) is a tempered distribution (the "field configuration")
- (-Δ + m²)⁻¹ is the Green's function/propagator
- The quadratic form is computed in Fourier space as ∫ |f̂(k)|² / (|k|² + m²) dk

### Connection to Osterwalder-Schrader

The **Schwinger functions** (Euclidean Green's functions) are the moments:
  Sₙ(x₁, ..., xₙ) = ∫_{S'} φ(x₁) · · · φ(xₙ) dμ(φ)

For the free field:
  S₂(x, y) = (-Δ + m²)⁻¹(x, y) = ∫ exp(ik·(x-y)) / (|k|² + m²) dk/(2π)ᵈ

These Schwinger functions satisfy the Osterwalder-Schrader axioms (E0'-E4) as
defined in `Reconstruction.lean`, and the OS reconstruction theorem produces the
corresponding Wightman QFT.

### Why Nuclearity is Essential

The measure μ lives on S'(ℝᵈ), which is the **dual** of the nuclear space S(ℝᵈ).
Without nuclearity, Minlos' theorem would not apply and we could not construct μ
from the characteristic functional C. This is why:
- S(ℝᵈ) being nuclear (SchwartzNuclear.lean) is essential
- The Minlos theorem (BochnerMinlos.lean) provides the measure
- The nuclear operator theory (NuclearOperator.lean) and nuclear space definition
  (NuclearSpace.lean) provide the foundational infrastructure

## References

* Glimm-Jaffe, "Quantum Physics" (1987), Ch. 6 (Euclidean field theory)
* Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory" (1974)
* Osterwalder-Schrader, "Axioms for Euclidean Green's Functions" (1973)
* Nelson, "Construction of quantum fields from Markoff fields" (1973)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex SchwartzMap
open scoped SchwartzMap FourierTransform

variable (d : ℕ) (m : ℝ)

/-! ### The Free Field Quadratic Form -/

/-- The **propagator weight function**: `w(k) = 1 / (‖k‖² + m²)`.

    This is the Fourier-space representation of the Green's function
    `(-Δ + m²)⁻¹` for the Klein-Gordon operator. -/
def propagatorWeight (d : ℕ) (m : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun k => 1 / (‖k‖ ^ 2 + m ^ 2)

/-- The propagator weight is non-negative when m ≥ 0. -/
theorem propagatorWeight_nonneg (_hm : 0 ≤ m) (k : EuclideanSpace ℝ (Fin d)) :
    0 ≤ propagatorWeight d m k := by
  unfold propagatorWeight
  apply div_nonneg one_pos.le
  positivity

/-- The propagator weight is bounded above by 1/m² when m > 0. -/
theorem propagatorWeight_le (hm : 0 < m) (k : EuclideanSpace ℝ (Fin d)) :
    propagatorWeight d m k ≤ 1 / m ^ 2 := by
  unfold propagatorWeight
  apply div_le_div_of_nonneg_left one_pos.le
  · positivity
  · linarith [sq_nonneg ‖k‖]

/-- The free field quadratic form on Schwartz space, defined concretely via
    Fourier transform:

    `Q(f) = ∫ₖ |f̂(k)|² / (‖k‖² + m²) dk`

    where `f̂ = 𝓕 f` is the Fourier transform of f (viewed as a ℂ-valued function).
    This integral is the Fourier-space representation of `⟨f, (-Δ + m²)⁻¹ f⟩_{L²}`. -/
def freeFieldForm (d : ℕ) (m : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) : ℝ :=
  ∫ k : EuclideanSpace ℝ (Fin d),
    ‖𝓕 (fun x => (f x : ℂ)) k‖ ^ 2 * propagatorWeight d m k

/-- The associated bilinear form: B(f,g) = ¼[Q(f+g) - Q(f-g)].

    For the free field, this equals `⟨f, (-Δ+m²)⁻¹ g⟩_{L²}`, i.e.,
    the inner product weighted by the propagator. -/
def freeFieldBilinearForm (d : ℕ) (m : ℝ)
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) : ℝ :=
  (freeFieldForm d m (f + g) - freeFieldForm d m (f - g)) / 4

/-! ### Properties of the Free Field Quadratic Form -/

/-- The free field quadratic form is non-negative: Q(f) ≥ 0.
    The integrand |f̂(k)|² / (‖k‖² + m²) is pointwise non-negative. -/
theorem freeFieldForm_nonneg (hm : 0 ≤ m)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    0 ≤ freeFieldForm d m f := by
  unfold freeFieldForm
  apply integral_nonneg
  intro k
  apply mul_nonneg
  · exact sq_nonneg _
  · exact propagatorWeight_nonneg d m hm k

/-- The Fourier transform of the zero function is zero (helper for freeFieldForm). -/
private theorem fourier_zero_eq (d : ℕ) :
    𝓕 (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℂ)) =
    fun _ => 0 := by
  ext w
  show VectorFourier.fourierIntegral 𝐞 volume (innerₗ _) (fun _ => 0) w = 0
  simp [VectorFourier.fourierIntegral, smul_zero]

/-- The free field quadratic form at 0 is 0.
    Proof: 0̂ = 0 (Fourier transform of zero), so the integrand vanishes pointwise. -/
theorem freeFieldForm_zero : freeFieldForm d m 0 = 0 := by
  unfold freeFieldForm
  simp only [SchwartzMap.coe_zero, Pi.zero_apply, Complex.ofReal_zero, fourier_zero_eq, norm_zero]
  simp [zero_pow (two_ne_zero)]

/-- The Fourier transform commutes with scalar multiplication by a complex constant
    (helper for function spaces, derived from the integral definition). -/
private theorem fourier_const_mul (d : ℕ) (c : ℂ)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) :
    𝓕 (fun x => c * g x) = fun k => c * 𝓕 g k := by
  have : (fun x => c * g x) = c • g := by ext x; simp [Pi.smul_apply, smul_eq_mul]
  rw [this]
  show VectorFourier.fourierIntegral 𝐞 volume (innerₗ _) (c • g) =
    c • VectorFourier.fourierIntegral 𝐞 volume (innerₗ _) g
  exact VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ _) g c

/-- The free field quadratic form is homogeneous of degree 2: Q(αf) = α² Q(f).
    This follows from linearity of the Fourier transform: (αf)^ = α f̂. -/
theorem freeFieldForm_smul (α : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    freeFieldForm d m (α • f) = α ^ 2 * freeFieldForm d m f := by
  unfold freeFieldForm
  -- (α • f) x = α * f x, cast to ℂ gives (α : ℂ) * (f x : ℂ)
  have h_smul : (fun x : EuclideanSpace ℝ (Fin d) => ((α • f) x : ℂ)) =
      fun x => (α : ℂ) * (f x : ℂ) := by
    ext x; simp [SchwartzMap.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [h_smul, fourier_const_mul]
  -- ‖(α : ℂ) * z‖ = ‖(α : ℂ)‖ * ‖z‖ and ‖(α : ℂ)‖^2 = α^2
  simp_rw [norm_mul, Complex.norm_real, mul_pow]
  rw [show ‖α‖ ^ 2 = α ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

/-- Lift a real-valued Schwartz function to a complex-valued one via Complex.ofRealCLM. -/
private def toComplexSchwartz
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    𝓢(EuclideanSpace ℝ (Fin d), ℂ) where
  toFun x := Complex.ofRealCLM (f x)
  smooth' := Complex.ofRealCLM.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    exact ⟨C, fun x => by
      -- ofRealLI is a linear isometry, so it preserves norms of iterated derivatives
      have heq : (fun x => Complex.ofRealCLM (f x)) = Complex.ofRealLI ∘ ⇑f := rfl
      rw [heq, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
        (f.smooth ⊤).contDiffAt (mod_cast le_top)]
      exact hC x⟩

/-- The lifting from real to complex Schwartz space as a continuous linear map.
    Since `Complex.ofRealLI` is a linear isometry, it preserves all Schwartz seminorms. -/
private def toComplexSchwartzCLM :
    𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  SchwartzMap.mkCLM (𝕜 := ℝ) (𝕜' := ℝ)
    (fun f x => Complex.ofRealCLM (f x))
    (fun f g x => by simp [map_add])
    (fun a f x => by simp only [smul_apply, map_smul, RingHom.id_apply])
    (fun f => Complex.ofRealCLM.contDiff.comp f.smooth')
    (fun ⟨k, n⟩ => ⟨{(k, n)}, 1, zero_le_one, fun f x => by
      simp only [Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul]
      have : (fun x => Complex.ofRealCLM (f x)) = Complex.ofRealLI ∘ ⇑f := rfl
      rw [this, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
        (f.smooth ⊤).contDiffAt (mod_cast le_top)]
      exact SchwartzMap.le_seminorm ℝ k n f x⟩)

/-- Integrability of the quadratic Fourier integrand for Schwartz functions.
    The key ingredients are: (1) Fourier transform of Schwartz functions is Schwartz,
    (2) Schwartz functions are in L², so ‖𝓕 f̃‖² is integrable,
    (3) propagatorWeight is bounded by 1/m² when m > 0. -/
private theorem quadIntegrable (hm : 0 < m)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    Integrable (fun k => ‖𝓕 (fun x => ((f x : ℝ) : ℂ)) k‖ ^ 2 *
      propagatorWeight d m k) := by
  set V := EuclideanSpace ℝ (Fin d)
  -- Lift f to complex Schwartz function g
  set g : 𝓢(V, ℂ) := toComplexSchwartz d f
  -- The Fourier transform of g is a Schwartz map
  set Fg : 𝓢(V, ℂ) := 𝓕 g
  -- Key: Fg's coercion equals the raw Fourier transform of (fun x => (f x : ℂ))
  have hFg_eq : ∀ k : V, (Fg : V → ℂ) k = 𝓕 (fun x => ((f x : ℝ) : ℂ)) k := by
    intro k; rfl
  -- Schwartz function Fg is bounded
  set C := SchwartzMap.seminorm ℝ 0 0 Fg
  have hC_nn : 0 ≤ C := apply_nonneg _ _
  have hFg_bound : ∀ k : V, ‖(Fg : V → ℂ) k‖ ≤ C :=
    fun k => SchwartzMap.norm_le_seminorm ℝ Fg k
  -- Schwartz function Fg is integrable
  have hFg_int : Integrable (Fg : V → ℂ) := Fg.integrable
  -- Propagator weight bounds
  have hpw_bound : ∀ k : V, propagatorWeight d m k ≤ 1 / m ^ 2 :=
    propagatorWeight_le d m hm
  have hpw_nn : ∀ k : V, 0 ≤ propagatorWeight d m k :=
    propagatorWeight_nonneg d m hm.le
  -- Bound the integrand: ‖Fg k‖² * w(k) ≤ (C/m²) * ‖Fg k‖
  have hbound : ∀ k : V,
      ‖𝓕 (fun x => ((f x : ℝ) : ℂ)) k‖ ^ 2 * propagatorWeight d m k ≤
      (C / m ^ 2) * ‖(Fg : V → ℂ) k‖ := by
    intro k
    rw [show ‖𝓕 (fun x => ((f x : ℝ) : ℂ)) k‖ = ‖(Fg : V → ℂ) k‖ from by rw [hFg_eq]]
    calc ‖(Fg : V → ℂ) k‖ ^ 2 * propagatorWeight d m k
        = ‖(Fg : V → ℂ) k‖ * (‖(Fg : V → ℂ) k‖ * propagatorWeight d m k) := by
          rw [sq]; ring
      _ ≤ C * (‖(Fg : V → ℂ) k‖ * (1 / m ^ 2)) :=
          mul_le_mul (hFg_bound k)
            (mul_le_mul_of_nonneg_left (hpw_bound k) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (hpw_nn k)) hC_nn
      _ = (C / m ^ 2) * ‖(Fg : V → ℂ) k‖ := by ring
  -- The dominating function is integrable
  have hdom : Integrable (fun k => (C / m ^ 2) * ‖(Fg : V → ℂ) k‖) :=
    hFg_int.norm.const_mul (C / m ^ 2)
  -- The integrand is non-negative
  have hnn : ∀ k, 0 ≤ ‖𝓕 (fun x => ((f x : ℝ) : ℂ)) k‖ ^ 2 * propagatorWeight d m k :=
    fun k => mul_nonneg (sq_nonneg _) (hpw_nn k)
  -- Measurability: Fg is continuous (Schwartz), so the integrand is measurable
  have hFg_cont : Continuous (Fg : V → ℂ) := Fg.continuous
  have hmeas : AEStronglyMeasurable
      (fun k => ‖𝓕 (fun x => ((f x : ℝ) : ℂ)) k‖ ^ 2 * propagatorWeight d m k)
      volume := by
    have heq : (fun k => ‖𝓕 (fun x => ((f x : ℝ) : ℂ)) k‖ ^ 2 * propagatorWeight d m k) =
        (fun k => ‖(Fg : V → ℂ) k‖ ^ 2 * propagatorWeight d m k) := by
      ext k; rw [hFg_eq]
    rw [heq]
    exact ((continuous_pow 2 |>.comp (continuous_norm.comp hFg_cont)).mul
      (continuous_const.div
        ((continuous_pow 2 |>.comp continuous_norm).add continuous_const)
        (fun k => ne_of_gt (by show 0 < ‖k‖ ^ 2 + m ^ 2; linarith [sq_nonneg ‖k‖, sq_pos_of_pos hm])))).aestronglyMeasurable
  -- Non-negativity of the dominating function
  have hdom_nn : ∀ k, 0 ≤ (C / m ^ 2) * ‖(Fg : V → ℂ) k‖ :=
    fun k => mul_nonneg (div_nonneg hC_nn (sq_nonneg m)) (norm_nonneg _)
  -- Conclude by comparison
  exact Integrable.mono hdom hmeas
    (Filter.Eventually.of_forall fun k => by
      rw [Real.norm_of_nonneg (hnn k), Real.norm_of_nonneg (hdom_nn k)]
      exact hbound k)

/-- The free field quadratic form satisfies the parallelogram law. -/
theorem freeFieldForm_parallelogram (hm : 0 < m)
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    freeFieldForm d m (f + g) + freeFieldForm d m (f - g) =
    2 * freeFieldForm d m f + 2 * freeFieldForm d m g := by
  simp only [freeFieldForm]
  set V := EuclideanSpace ℝ (Fin d)
  set F : V → ℂ := fun x => (f x : ℂ) with hF_def
  set G : V → ℂ := fun x => (g x : ℂ) with hG_def
  set w := propagatorWeight d m with hw_def
  -- Cast (f ± g) x to ℂ
  have h_add : (fun x : V => (((f + g) x : ℝ) : ℂ)) = F + G := by
    ext x; simp [F, G, Complex.ofReal_add]
  have h_sub : (fun x : V => (((f - g) x : ℝ) : ℂ)) = F - G := by
    ext x; simp [F, G, Complex.ofReal_sub]
  rw [h_add, h_sub]
  -- Integrability of F and G (for Fourier additivity)
  have hF_int : Integrable F := Complex.ofRealCLM.integrable_comp f.integrable
  have hG_int : Integrable G := Complex.ofRealCLM.integrable_comp g.integrable
  -- Fourier transform additivity: 𝓕(F + G) = 𝓕 F + 𝓕 G
  have four_add : ∀ k, 𝓕 (F + G) k = 𝓕 F k + 𝓕 G k := by
    intro k
    show (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) (F + G)) k =
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) F) k +
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) G) k
    rw [VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner hF_int hG_int]
    rfl
  -- Fourier transform subtraction: 𝓕(F - G) = 𝓕 F - 𝓕 G
  have four_sub : ∀ k, 𝓕 (F - G) k = 𝓕 F k - 𝓕 G k := by
    intro k
    have hsub : F - G = F + ((-1 : ℂ) • G) := by
      ext x; simp [F, G, sub_eq_add_neg]
    rw [hsub]
    show (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) (F + (-1 : ℂ) • G)) k =
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) F) k -
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) G) k
    rw [VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner hF_int
      (hG_int.smul (-1 : ℂ)),
      VectorFourier.fourierIntegral_const_smul]
    simp [Pi.add_apply, sub_eq_add_neg]
  -- Integrability of all quadratic integrands
  have h_int_1 : Integrable (fun k => ‖𝓕 (F + G) k‖ ^ 2 * w k) := by
    rw [show F + G = (fun x => (((f + g) x : ℝ) : ℂ)) from h_add.symm]; exact quadIntegrable d m hm (f + g)
  have h_int_2 : Integrable (fun k => ‖𝓕 (F - G) k‖ ^ 2 * w k) := by
    rw [show F - G = (fun x => (((f - g) x : ℝ) : ℂ)) from h_sub.symm]; exact quadIntegrable d m hm (f - g)
  have h_int_f : Integrable (fun k => ‖𝓕 F k‖ ^ 2 * w k) := quadIntegrable d m hm f
  have h_int_g : Integrable (fun k => ‖𝓕 G k‖ ^ 2 * w k) := quadIntegrable d m hm g
  -- Combine LHS integrals
  rw [← integral_add h_int_1 h_int_2]
  -- Rewrite RHS: 2 * ∫ = ∫ (2 * ·)
  rw [show (2 : ℝ) * ∫ k, ‖𝓕 F k‖ ^ 2 * w k =
    ∫ k, 2 * (‖𝓕 F k‖ ^ 2 * w k) from (integral_const_mul _ _).symm,
    show (2 : ℝ) * ∫ k, ‖𝓕 G k‖ ^ 2 * w k =
    ∫ k, 2 * (‖𝓕 G k‖ ^ 2 * w k) from (integral_const_mul _ _).symm]
  rw [← integral_add (h_int_f.const_mul 2) (h_int_g.const_mul 2)]
  -- Reduce to pointwise identity
  congr 1; ext k
  -- Apply the parallelogram law for norms in ℂ (inner product space over ℝ)
  simp only [four_add, four_sub]
  have par := parallelogram_law_with_norm ℝ (𝓕 F k) (𝓕 G k)
  -- par : ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ = 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖)
  have key : ‖𝓕 F k + 𝓕 G k‖ ^ 2 + ‖𝓕 F k - 𝓕 G k‖ ^ 2 =
      2 * ‖𝓕 F k‖ ^ 2 + 2 * ‖𝓕 G k‖ ^ 2 := by
    simp only [sq]; linarith
  -- Multiply key by w k
  calc ‖𝓕 F k + 𝓕 G k‖ ^ 2 * w k + ‖𝓕 F k - 𝓕 G k‖ ^ 2 * w k
      = (‖𝓕 F k + 𝓕 G k‖ ^ 2 + ‖𝓕 F k - 𝓕 G k‖ ^ 2) * w k := by ring
    _ = (2 * ‖𝓕 F k‖ ^ 2 + 2 * ‖𝓕 G k‖ ^ 2) * w k := by rw [key]
    _ = 2 * (‖𝓕 F k‖ ^ 2 * w k) + 2 * (‖𝓕 G k‖ ^ 2 * w k) := by ring

/-- The free field quadratic form is continuous on Schwartz space.
    This follows from:
    1. The Fourier transform is continuous on Schwartz space
    2. The L² norm squared is continuous
    3. The propagator weight 1/(|k|²+m²) is bounded -/
private lemma seminorm_finset_sum_apply
    (s : Finset (ℕ × ℕ)) (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    (s.sum (fun kl : ℕ × ℕ => SchwartzMap.seminorm ℝ kl.1 kl.2)) g =
    s.sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 g) := by
  induction s using Finset.cons_induction with
  | empty => simp [Seminorm.zero_apply]
  | cons a s has ih => rw [Finset.sum_cons, Finset.sum_cons, Seminorm.add_apply, ih]

theorem freeFieldForm_continuous (hm : 0 < m) :
    Continuous (freeFieldForm d m) := by
  set V := EuclideanSpace ℝ (Fin d) with hV
  rw [continuous_iff_continuousAt]
  intro f₀
  set Ψ : 𝓢(V, ℝ) →L[ℝ] 𝓢(V, ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ).comp (toComplexSchwartzCLM d) with hΨ
  set N := d + 1 with hN
  set SN : 𝓢(V, ℂ) → ℝ := fun g =>
    (Finset.Iic ((N : ℕ), (0 : ℕ))).sum
      (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 g) with hSN_def
  set M := SN (Ψ f₀) + 1 with hM_def
  set C₀ := (2 ^ N * M) ^ 2 / m ^ 2 with hC₀_def
  have hSN_Ψ_cont : Continuous (fun f => SN (Ψ f)) := by
    simp only [hSN_def]
    apply continuous_finset_sum
    intro kl _
    exact ((schwartz_withSeminorms ℝ V ℂ).continuous_seminorm kl).comp Ψ.continuous
  have hSN_near : ∀ᶠ f in nhds f₀, SN (Ψ f) ≤ M := by
    have hlt : SN (Ψ f₀) < M := by simp only [hM_def]; linarith
    exact (hSN_Ψ_cont.continuousAt.eventually (gt_mem_nhds hlt)).mono fun f hf => le_of_lt hf
  apply continuousAt_of_dominated
    (bound := fun k => C₀ * (1 + ‖k‖) ^ (-(2 * (N : ℝ))))
  · -- Condition 1: AE measurability
    filter_upwards with f
    exact (quadIntegrable d m hm f).aestronglyMeasurable
  · -- Condition 2: Norm bound near f₀
    filter_upwards [hSN_near] with f hf
    filter_upwards with k
    have hnn : 0 ≤ ‖𝓕 (fun x => ((f x : ℝ) : ℂ)) k‖ ^ 2 * propagatorWeight d m k :=
      mul_nonneg (sq_nonneg _) (propagatorWeight_nonneg d m hm.le k)
    rw [Real.norm_of_nonneg hnn]
    have hΨ_eq : (Ψ f : V → ℂ) k = 𝓕 (fun x => ((f x : ℝ) : ℂ)) k := rfl
    rw [← hΨ_eq]
    have h1k_pos : (0 : ℝ) < 1 + ‖k‖ := by linarith [norm_nonneg k]
    have h1k_nn : (0 : ℝ) ≤ 1 + ‖k‖ := le_of_lt h1k_pos
    have h1kN_pos : (0 : ℝ) < (1 + ‖k‖) ^ N := pow_pos h1k_pos N
    -- Schwartz decay from one_add_le_sup_seminorm_apply
    have hbound := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0))
      (le_refl N) (le_refl 0) (Ψ f) k
    rw [norm_iteratedFDeriv_zero] at hbound
    -- Weaken: lattice sup ≤ sum
    have hsup_le : ((Finset.Iic (N, (0 : ℕ))).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) (Ψ f) ≤ SN (Ψ f) := by
      have h := Seminorm.le_def.mp
        (Seminorm.finset_sup_le_sum (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
          (Finset.Iic (N, 0))) (Ψ f)
      rwa [seminorm_finset_sum_apply] at h
    -- Combined: ‖(Ψ f) k‖ ≤ 2^N * M / (1+‖k‖)^N
    have hpt : ‖(Ψ f : V → ℂ) k‖ ≤ 2 ^ N * M / (1 + ‖k‖) ^ N := by
      rw [le_div_iff₀ h1kN_pos, mul_comm]
      calc (1 + ‖k‖) ^ N * ‖(Ψ f : V → ℂ) k‖
          ≤ 2 ^ N * ((Finset.Iic (N, (0 : ℕ))).sup
              (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) (Ψ f) := hbound
        _ ≤ 2 ^ N * SN (Ψ f) :=
            mul_le_mul_of_nonneg_left hsup_le (by positivity)
        _ ≤ 2 ^ N * M :=
            mul_le_mul_of_nonneg_left hf (by positivity)
    -- Square the bound
    have hpt2 : ‖(Ψ f : V → ℂ) k‖ ^ 2 ≤ (2 ^ N * M / (1 + ‖k‖) ^ N) ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg ((Ψ f : V → ℂ) k)]) hpt
    -- Combine with propagator weight bound
    calc ‖(Ψ f : V → ℂ) k‖ ^ 2 * propagatorWeight d m k
        ≤ (2 ^ N * M / (1 + ‖k‖) ^ N) ^ 2 * (1 / m ^ 2) :=
          mul_le_mul hpt2 (propagatorWeight_le d m hm k)
            (propagatorWeight_nonneg d m hm.le k) (sq_nonneg _)
      _ = C₀ * (1 / (1 + ‖k‖) ^ (2 * N)) := by
          simp only [hC₀_def, div_pow, ← pow_mul]; ring
      _ = C₀ * (1 + ‖k‖) ^ (-(2 * (N : ℝ))) := by
          congr 1; rw [one_div]
          rw [show (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) from by push_cast; ring]
          rw [← Real.rpow_natCast (1 + ‖k‖) (2 * N), ← Real.rpow_neg h1k_nn]
  · -- Condition 3: Bound integrability
    exact (integrable_one_add_norm (by
      rw [finrank_euclideanSpace_fin]; simp only [hN]; push_cast; linarith)).const_mul C₀
  · -- Condition 4: Pointwise continuity
    filter_upwards with k
    show ContinuousAt (fun f => ‖(Ψ f : V → ℂ) k‖ ^ 2 * propagatorWeight d m k) f₀
    -- Evaluation at k is continuous on Schwartz space
    have heval_cont : Continuous (fun g : 𝓢(V, ℂ) => (g : V → ℂ) k) := by
      let eval_lm : 𝓢(V, ℂ) →ₗ[ℝ] ℂ :=
        { toFun := fun g => (g : V → ℂ) k
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      apply Seminorm.cont_withSeminorms_normedSpace ℂ
        (schwartz_withSeminorms ℝ V ℂ) eval_lm
      exact ⟨{(0, 0)}, 1, fun g => by
        simp only [eval_lm, Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton,
          schwartzSeminormFamily_apply,
          one_smul, LinearMap.coe_mk, AddHom.coe_mk]
        exact SchwartzMap.norm_le_seminorm ℝ g k⟩
    -- The composition f ↦ (Ψ f)(k) is continuous
    have hcomp : Continuous (fun f : 𝓢(V, ℝ) => (Ψ f : V → ℂ) k) :=
      heval_cont.comp Ψ.continuous
    apply ContinuousAt.mul
    · exact (hcomp.norm.pow 2).continuousAt
    · exact continuousAt_const

/-! ### Free Field Characteristic Functional -/

/-- The free field characteristic functional:
    C(f) = exp(-½ Q(f)) where Q is the free field quadratic form.

    This is a continuous positive-definite functional with C(0) = 1,
    so by Minlos' theorem (applied to the nuclear space S(ℝᵈ)),
    it determines a unique probability measure on S'(ℝᵈ). -/
def freeFieldCharacteristic (d : ℕ) (m : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) : ℂ :=
  exp (-(1/2 : ℂ) * ↑(freeFieldForm d m f))

/-- The free field characteristic functional at 0 equals 1. -/
theorem freeFieldCharacteristic_zero :
    freeFieldCharacteristic d m 0 = 1 := by
  simp only [freeFieldCharacteristic, freeFieldForm_zero]
  simp

/-- The free field characteristic functional is continuous. -/
theorem freeFieldCharacteristic_continuous (hm : 0 < m) :
    Continuous (freeFieldCharacteristic d m) := by
  apply Continuous.cexp
  apply Continuous.mul continuous_const
  exact continuous_ofReal.comp (freeFieldForm_continuous d m hm)

/-- Algebraic PSD: ∑_ij aᵢ aⱼ (‖zᵢ + zⱼ‖² - ‖zᵢ‖² - ‖zⱼ‖²)/2 = ‖∑ᵢ aᵢ zᵢ‖² ≥ 0. -/
private lemma polarization_psd {n : ℕ} (a : Fin n → ℝ) (z : Fin n → ℂ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      a i * a j * ((‖z i + z j‖ ^ 2 - ‖z i‖ ^ 2 - ‖z j‖ ^ 2) / 2) := by
  have eq_inner : ∀ i j : Fin n,
      (‖z i + z j‖ ^ 2 - ‖z i‖ ^ 2 - ‖z j‖ ^ 2) / 2 =
      @inner ℝ ℂ _ (z i) (z j) := by
    intro i j; linarith [norm_add_sq_real (z i) (z j)]
  simp_rw [eq_inner]
  calc ∑ i, ∑ j, a i * a j * @inner ℝ ℂ _ (z i) (z j)
      = @inner ℝ ℂ _ (∑ i, (a i) • z i) (∑ j, (a j) • z j) := by
        simp_rw [sum_inner (𝕜 := ℝ), inner_sum (𝕜 := ℝ),
                 real_inner_smul_left, real_inner_smul_right]
        congr 1; ext i; congr 1; ext j; ring
    _ = ‖∑ i, (a i) • z i‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ ≥ 0 := sq_nonneg _

/-- The bilinear form as integral of ℝ-inner product weighted by propagator. -/
private lemma bilinear_as_integral (hm : 0 < m)
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    quadraticBilinearForm (freeFieldForm d m) f g =
    ∫ k : EuclideanSpace ℝ (Fin d),
      @inner ℝ ℂ _ (𝓕 (fun v => (f v : ℂ)) k) (𝓕 (fun v => (g v : ℂ)) k) *
      propagatorWeight d m k := by
  simp only [quadraticBilinearForm, freeFieldForm]
  set V := EuclideanSpace ℝ (Fin d)
  set F : V → ℂ := fun v => (f v : ℂ) with hF_def
  set G : V → ℂ := fun v => (g v : ℂ) with hG_def
  set w := propagatorWeight d m with hw_def
  have h_add : (fun v : V => (((f + g) v : ℝ) : ℂ)) = F + G := by
    ext v; simp [F, G, Complex.ofReal_add]
  rw [h_add]
  have hF_int : Integrable F := Complex.ofRealCLM.integrable_comp f.integrable
  have hG_int : Integrable G := Complex.ofRealCLM.integrable_comp g.integrable
  have four_add : ∀ k, 𝓕 (F + G) k = 𝓕 F k + 𝓕 G k := by
    intro k
    show (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) (F + G)) k =
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) F) k +
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) G) k
    rw [VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner
        hF_int hG_int]
    rfl
  have h_int_fg : Integrable (fun k => ‖𝓕 (F + G) k‖ ^ 2 * w k) := by
    rw [show F + G = (fun v => (((f + g) v : ℝ) : ℂ)) from h_add.symm]
    exact quadIntegrable d m hm (f + g)
  have h_int_f : Integrable (fun k => ‖𝓕 F k‖ ^ 2 * w k) := quadIntegrable d m hm f
  have h_int_g : Integrable (fun k => ‖𝓕 G k‖ ^ 2 * w k) := quadIntegrable d m hm g
  -- Combine three separate integrals into one using integral_sub twice
  have h_combined : (∫ k, ‖𝓕 (F + G) k‖ ^ 2 * w k) -
      (∫ k, ‖𝓕 F k‖ ^ 2 * w k) - (∫ k, ‖𝓕 G k‖ ^ 2 * w k) =
      ∫ k, (‖𝓕 (F + G) k‖ ^ 2 * w k - ‖𝓕 F k‖ ^ 2 * w k - ‖𝓕 G k‖ ^ 2 * w k) := by
    rw [← integral_sub h_int_fg h_int_f]
    exact (integral_sub (h_int_fg.sub h_int_f) h_int_g).symm
  rw [h_combined, ← integral_div]
  congr 1; ext k; simp only [four_add]
  have hfact : ‖𝓕 F k + 𝓕 G k‖ ^ 2 * w k - ‖𝓕 F k‖ ^ 2 * w k -
      ‖𝓕 G k‖ ^ 2 * w k =
      (‖𝓕 F k + 𝓕 G k‖ ^ 2 - ‖𝓕 F k‖ ^ 2 - ‖𝓕 G k‖ ^ 2) * w k := by ring
  have key : ‖𝓕 F k + 𝓕 G k‖ ^ 2 - ‖𝓕 F k‖ ^ 2 - ‖𝓕 G k‖ ^ 2 =
      2 * @inner ℝ ℂ _ (𝓕 F k) (𝓕 G k) := by
    linarith [norm_add_sq_real (𝓕 F k) (𝓕 G k)]
  rw [hfact, key]; ring

/-- Integrability of the inner product integrand. -/
private lemma inner_integrand_integrable (hm : 0 < m)
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    Integrable (fun k : EuclideanSpace ℝ (Fin d) =>
      @inner ℝ ℂ _ (𝓕 (fun v => (f v : ℂ)) k) (𝓕 (fun v => (g v : ℂ)) k) *
      propagatorWeight d m k) := by
  set V := EuclideanSpace ℝ (Fin d)
  set F : V → ℂ := fun v => (f v : ℂ)
  set G : V → ℂ := fun v => (g v : ℂ)
  set w := propagatorWeight d m
  -- ⟪z₁, z₂⟫ * w = ((‖z₁+z₂‖² - ‖z₁‖² - ‖z₂‖²)/2) * w
  have h_eq : ∀ k, @inner ℝ ℂ _ (𝓕 F k) (𝓕 G k) * w k =
      ((‖𝓕 F k + 𝓕 G k‖ ^ 2 - ‖𝓕 F k‖ ^ 2 - ‖𝓕 G k‖ ^ 2) / 2) * w k := by
    intro k
    congr 1
    linarith [norm_add_sq_real (𝓕 F k) (𝓕 G k)]
  simp_rw [h_eq]
  have hF_int : Integrable F := Complex.ofRealCLM.integrable_comp f.integrable
  have hG_int : Integrable G := Complex.ofRealCLM.integrable_comp g.integrable
  have h_add : (fun v : V => (((f + g) v : ℝ) : ℂ)) = F + G := by
    ext v; simp [F, G, Complex.ofReal_add]
  have four_add : ∀ k, 𝓕 (F + G) k = 𝓕 F k + 𝓕 G k := by
    intro k
    show (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) (F + G)) k =
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) F) k +
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) G) k
    rw [VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner
        hF_int hG_int]
    rfl
  have h_norm_eq : (fun k => ‖𝓕 F k + 𝓕 G k‖ ^ 2 * w k) =
      (fun k => ‖𝓕 (F + G) k‖ ^ 2 * w k) := by ext k; rw [four_add]
  have h_int_fg : Integrable (fun k => ‖𝓕 F k + 𝓕 G k‖ ^ 2 * w k) := by
    rw [h_norm_eq, show F + G = (fun v => (((f + g) v : ℝ) : ℂ)) from h_add.symm]
    exact quadIntegrable d m hm (f + g)
  have h_int_f : Integrable (fun k => ‖𝓕 F k‖ ^ 2 * w k) := quadIntegrable d m hm f
  have h_int_g : Integrable (fun k => ‖𝓕 G k‖ ^ 2 * w k) := quadIntegrable d m hm g
  have h1 : Integrable (fun k => (‖𝓕 F k + 𝓕 G k‖ ^ 2 * w k -
      ‖𝓕 F k‖ ^ 2 * w k - ‖𝓕 G k‖ ^ 2 * w k) / 2) :=
    ((h_int_fg.sub h_int_f).sub h_int_g).div_const 2
  convert h1 using 1; ext k; ring

/-- The bilinear form `B(f,g) = (Q(f+g) - Q(f) - Q(g))/2` of the free field quadratic form
    is positive semi-definite: for any finite set of Schwartz functions, the matrix
    `B(fᵢ, fⱼ)` is PSD. This is because B(f,g) = ∫ Re⟨𝓕f̃(k), 𝓕g̃(k)⟩ · w(k) dk,
    which is a weighted inner product and hence PSD. -/
private theorem freeFieldBilinearForm_psd (hm : 0 < m) (n : ℕ)
    (x : Fin n → 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    IsRealPSDKernel (fun i j =>
      quadraticBilinearForm (freeFieldForm d m) (x i) (x j)) := by
  constructor
  · -- Symmetry: B(f,g) = B(g,f)
    intro i j
    simp only [quadraticBilinearForm]
    rw [show x i + x j = x j + x i from add_comm (x i) (x j)]
    ring
  · -- PSD: ∑_ij a_i a_j B(f_i, f_j) ≥ 0
    intro a
    -- Abbreviations
    let V := EuclideanSpace ℝ (Fin d)
    let w := propagatorWeight d m
    let Z : Fin n → V → ℂ := fun i k => 𝓕 (fun v => ((x i) v : ℂ)) k
    -- Rewrite each B(x_i, x_j) as an integral of inner product
    have h_rw : ∀ i j, quadraticBilinearForm (freeFieldForm d m) (x i) (x j) =
        ∫ k : V, @inner ℝ ℂ _ (Z i k) (Z j k) * w k :=
      fun i j => bilinear_as_integral d m hm (x i) (x j)
    simp_rw [h_rw]
    -- Pull constants into integrals
    have h_const : ∀ i j, a i * a j *
        ∫ k : V, @inner ℝ ℂ _ (Z i k) (Z j k) * w k =
        ∫ k : V, a i * a j * (@inner ℝ ℂ _ (Z i k) (Z j k) * w k) := by
      intro i j; rw [← integral_const_mul]
    simp_rw [h_const]
    -- Integrability of each term (for sum-integral exchange)
    have h_int_ij : ∀ i j, Integrable (fun k : V =>
        a i * a j * (@inner ℝ ℂ _ (Z i k) (Z j k) * w k)) := by
      intro i j
      exact (inner_integrand_integrable d m hm (x i) (x j)).const_mul _
    -- Exchange inner sum with integral
    have h_inner_sum : ∀ i, ∑ j, ∫ k : V,
        a i * a j * (@inner ℝ ℂ _ (Z i k) (Z j k) * w k) =
        ∫ k : V, ∑ j, a i * a j * (@inner ℝ ℂ _ (Z i k) (Z j k) * w k) := by
      intro i
      rw [← integral_finset_sum]
      intro j _; exact h_int_ij i j
    simp_rw [h_inner_sum]
    -- Exchange outer sum with integral
    have h_outer_int : ∀ i, Integrable (fun k : V =>
        ∑ j, a i * a j * (@inner ℝ ℂ _ (Z i k) (Z j k) * w k)) := by
      intro i; exact integrable_finset_sum _ (fun j _ => h_int_ij i j)
    rw [← integral_finset_sum _ (fun i _ => h_outer_int i)]
    -- Apply integral_nonneg with pointwise bound
    apply integral_nonneg
    intro k; simp only [Pi.zero_apply]
    -- Factor out w k from the sum
    have h_factor : ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (@inner ℝ ℂ _ (Z i k) (Z j k) * w k) =
        (∑ i, ∑ j, a i * a j *
          ((‖Z i k + Z j k‖ ^ 2 - ‖Z i k‖ ^ 2 - ‖Z j k‖ ^ 2) / 2)) * w k := by
      simp_rw [show ∀ i j, @inner ℝ ℂ _ (Z i k) (Z j k) =
        (‖Z i k + Z j k‖ ^ 2 - ‖Z i k‖ ^ 2 - ‖Z j k‖ ^ 2) / 2 from
        fun i j => by linarith [norm_add_sq_real (Z i k) (Z j k)]]
      rw [Finset.sum_mul]; congr 1; ext i
      rw [Finset.sum_mul]; congr 1; ext j; ring
    rw [h_factor]
    exact mul_nonneg (polarization_psd a (fun i => Z i k))
      (propagatorWeight_nonneg d m hm.le k)

set_option maxHeartbeats 800000 in
/-- The free field characteristic functional is positive-definite.

    This follows from the fact that exp(-½ Q(f)) where Q is a positive quadratic
    form is positive-definite. The kernel K(f,g) = exp(-½ Q(f-g)) is positive-definite
    because Q is a positive quadratic form, so exp(-½ Q) is a positive-definite function
    (this uses the Schur product theorem and the Taylor expansion of exp). -/
theorem freeFieldCharacteristic_posdef (hm : 0 < m) :
    IsPositiveDefiniteFn (freeFieldCharacteristic d m) := by
  intro n x c
  -- Convert complex exp to real exp: exp(-(1/2 : ℂ) * ↑r) = ↑(Real.exp(-(1/2) * r))
  have hconv : ∀ f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ),
      freeFieldCharacteristic d m f =
      ↑(Real.exp (-(1/2 : ℝ) * freeFieldForm d m f)) := by
    intro f
    simp only [freeFieldCharacteristic]
    rw [show -(1/2 : ℂ) * ↑(freeFieldForm d m f) =
        ↑(-(1/2 : ℝ) * freeFieldForm d m f) from by push_cast; ring]
    exact (Complex.ofReal_exp _).symm
  simp_rw [hconv]
  -- Apply the general quadratic form PSD theorem
  -- Note: freeFieldForm_parallelogram gives Q(f+g) + Q(f-g) = 2Q(f) + 2Q(g)
  -- but quadratic_exp_kernel_posdef expects Q(f-g) + Q(f+g) = 2Q(f) + 2Q(g)
  have hpar : ∀ f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ),
      freeFieldForm d m (f - g) + freeFieldForm d m (f + g) =
      2 * freeFieldForm d m f + 2 * freeFieldForm d m g := by
    intro f g; linarith [freeFieldForm_parallelogram d m hm f g]
  exact quadratic_exp_kernel_posdef (freeFieldForm d m) hpar x c
    (freeFieldBilinearForm_psd d m hm n x)

/-- The free field characteristic functional is a `CharacteristicFunctional`. -/
def freeFieldCharacteristicFunctional (hm : 0 < m) :
    CharacteristicFunctional (𝓢(EuclideanSpace ℝ (Fin d), ℝ)) where
  toFun := freeFieldCharacteristic d m
  continuous_toFun := freeFieldCharacteristic_continuous d m hm
  positive_definite := freeFieldCharacteristic_posdef d m hm
  eval_zero := freeFieldCharacteristic_zero d m

/-! ### Euclidean Measure via Minlos -/

/-- The **Euclidean field theory measure** for the free scalar field.

    By Minlos' theorem applied to the nuclear space S(ℝᵈ) and the
    free field characteristic functional, there exists a unique probability
    measure μ on the dual space S'(ℝᵈ) (= tempered distributions) such that:

    C(f) = ∫_{S'(ℝᵈ)} exp(i φ(f)) dμ(φ) = exp(-½ Q(f))

    This is a Gaussian measure (the "Euclidean free field measure").

    In constructive QFT, this provides the starting point for:
    1. Defining Schwinger functions as moments of μ
    2. Verifying the OS axioms E0'-E4
    3. Applying the OS reconstruction theorem to get a Wightman QFT -/
theorem euclideanMeasure_exists (hm : 0 < m)
    [inst : MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ)] :
    ∃ (μ : Measure (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ)),
      IsProbabilityMeasure μ ∧
      ∀ (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)),
        freeFieldCharacteristic d m f =
        ∫ ω, exp (↑(ω f) * I) ∂μ := by
  haveI : NuclearSpace (𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :=
    SchwartzMap.instNuclearSpace d
  exact minlos_theorem (freeFieldCharacteristicFunctional d m hm)

/-! ### Schwinger Functions from the Euclidean Measure -/

/-- The two-point Schwinger function (Euclidean propagator) defined as
    the second moment of the Euclidean measure:
    S₂(x, y) = ∫_{S'} φ(x) φ(y) dμ(φ)

    For the free field, this equals the Green's function:
    S₂(x, y) = (-Δ + m²)⁻¹(x, y) -/
def schwingerTwoPoint
    [MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ)]
    (μ : Measure (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ))
    (δ_x δ_y : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) : ℂ :=
  ∫ ω : (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ),
    (↑(ω δ_x) : ℂ) * ↑(ω δ_y) ∂μ

/-! ### Helper Lemmas for Gaussian Moment Identification -/

variable {d : ℕ} {m : ℝ}

-- Abbreviation to reduce repetition in type signatures
private abbrev S' (d : ℕ) := 𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ

/-- The characteristic function identity applied to `t • h` gives a Gaussian-type identity:
    `C(t • h) = exp(-t² Q(h) / 2)` and equals `∫ exp(i t ω(h)) dμ(ω)`. -/
private lemma charFun_scaled
    [MeasurableSpace (S' d)]
    (μ : Measure (S' d))
    (hchar : ∀ f, freeFieldCharacteristic d m f =
      ∫ ω : S' d, exp (↑(ω f) * I) ∂μ)
    (h : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (t : ℝ) :
    exp (-(1/2 : ℂ) * ↑(t ^ 2 * freeFieldForm d m h)) =
    ∫ ω : S' d, exp (↑(t * ω h) * I) ∂μ := by
  have h1 := hchar (t • h)
  simp only [freeFieldCharacteristic, freeFieldForm_smul] at h1
  simp_rw [ContinuousLinearMap.map_smul, smul_eq_mul] at h1
  exact h1

/-- The pushforward of μ by evaluation at h equals `gaussianReal 0 (Q(h).toNNReal)`.
    Uses Levy's uniqueness via `Measure.ext_of_charFun`. -/
private lemma pushforward_eq_gaussian (hm : 0 ≤ m)
    [MeasurableSpace (S' d)]
    (μ : Measure (S' d))
    (hμ : IsProbabilityMeasure μ)
    (hchar : ∀ f, freeFieldCharacteristic d m f =
      ∫ ω : S' d, exp (↑(ω f) * I) ∂μ)
    (h : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (hmeas : Measurable (fun ω : S' d => ω h)) :
    μ.map (fun ω => ω h) =
      gaussianReal 0 (freeFieldForm d m h).toNNReal := by
  haveI : IsProbabilityMeasure (μ.map (fun ω => ω h)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real]
  rw [integral_map hmeas.aemeasurable]
  · simp_rw [show ∀ ω : S' d,
        ↑t * ↑(ω h) * I = ↑(t * ω h) * I from fun ω => by push_cast; ring]
    rw [← charFun_scaled μ hchar h t]
    rw [charFun_gaussianReal]
    congr 1
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
    rw [Real.coe_toNNReal _ (freeFieldForm_nonneg d m hm h)]
    push_cast; ring
  · exact (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable

/-- The pairing ω(h) is in Lp for the Euclidean measure (Fernique-type). -/
private lemma pairing_memLp_schwinger (hm : 0 ≤ m)
    [MeasurableSpace (S' d)]
    (μ : Measure (S' d))
    (hμ : IsProbabilityMeasure μ)
    (hchar : ∀ f, freeFieldCharacteristic d m f =
      ∫ ω : S' d, exp (↑(ω f) * I) ∂μ)
    (h : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (hmeas : Measurable (fun ω : S' d => ω h))
    (p : ℝ≥0) :
    MemLp (fun ω : S' d => ω h) p μ := by
  have hgauss := pushforward_eq_gaussian hm μ hμ hchar h hmeas
  have hid : MemLp id p (gaussianReal 0 (freeFieldForm d m h).toNNReal) :=
    memLp_id_gaussianReal p
  rw [← hgauss] at hid
  rwa [memLp_map_measure_iff hid.aestronglyMeasurable hmeas.aemeasurable] at hid

/-- The measure is centered: E[ω(h)] = 0 for the Euclidean measure. -/
private lemma measure_centered_schwinger (hm : 0 ≤ m)
    [MeasurableSpace (S' d)]
    (μ : Measure (S' d))
    (hμ : IsProbabilityMeasure μ)
    (hchar : ∀ f, freeFieldCharacteristic d m f =
      ∫ ω : S' d, exp (↑(ω f) * I) ∂μ)
    (h : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (hmeas : Measurable (fun ω : S' d => ω h)) :
    ∫ ω : S' d, ω h ∂μ = 0 := by
  have hgauss := pushforward_eq_gaussian hm μ hμ hchar h hmeas
  have h_map := integral_map hmeas.aemeasurable
    (measurable_id.aestronglyMeasurable
      (μ := μ.map (fun ω : S' d => ω h)))
  simp only [id] at h_map
  rw [h_map.symm, hgauss, integral_id_gaussianReal]

/-- Second moment identity: `E[(ω h)²] = Q(h)` for the Euclidean measure. -/
private lemma second_moment_eq_form (hm : 0 ≤ m)
    [MeasurableSpace (S' d)]
    (μ : Measure (S' d))
    (hμ : IsProbabilityMeasure μ)
    (hchar : ∀ f, freeFieldCharacteristic d m f =
      ∫ ω : S' d, exp (↑(ω f) * I) ∂μ)
    (h : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (hmeas : Measurable (fun ω : S' d => ω h)) :
    ∫ ω : S' d, (ω h) ^ 2 ∂μ = freeFieldForm d m h := by
  set σ := (freeFieldForm d m h).toNNReal with hσ_def
  have hgauss := pushforward_eq_gaussian hm μ hμ hchar h hmeas
  have h_var : Var[fun ω : S' d => ω h; μ] = ∫ ω, (ω h) ^ 2 ∂μ :=
    variance_of_integral_eq_zero hmeas.aemeasurable
      (measure_centered_schwinger hm μ hμ hchar h hmeas)
  have h_var2 : Var[fun ω : S' d => ω h; μ] = σ := by
    have hv : Var[fun x : ℝ => x; μ.map (fun ω : S' d => ω h)] =
        Var[fun ω : S' d => ω h; μ] :=
      variance_map aemeasurable_id hmeas.aemeasurable
    rw [← hv, hgauss, variance_fun_id_gaussianReal]
  rw [← h_var, h_var2, hσ_def]
  exact Real.coe_toNNReal _ (freeFieldForm_nonneg d m hm h)

/-- Cross-moment identity via polarization:
    E[ω(f)·ω(g)] = (Q(f+g) - Q(f-g))/4 = B(f,g). -/
private lemma cross_moment_eq_bilinear (hm : 0 ≤ m)
    [MeasurableSpace (S' d)]
    (μ : Measure (S' d))
    (hμ : IsProbabilityMeasure μ)
    (hchar : ∀ f, freeFieldCharacteristic d m f =
      ∫ ω : S' d, exp (↑(ω f) * I) ∂μ)
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (hmeas : ∀ h : 𝓢(EuclideanSpace ℝ (Fin d), ℝ),
      Measurable (fun ω : S' d => ω h)) :
    ∫ ω : S' d, ω f * ω g ∂μ = freeFieldBilinearForm d m f g := by
  -- Polarization: 4 fg = (f+g)² - (f-g)²
  have h_polar : ∀ ω : S' d,
      (ω (f + g)) ^ 2 - (ω (f - g)) ^ 2 = 4 * (ω f * ω g) := by
    intro ω; rw [map_add, map_sub]; ring
  have hfg_sq : Integrable (fun ω : S' d => (ω (f + g)) ^ 2) μ :=
    (pairing_memLp_schwinger hm μ hμ hchar (f + g) (hmeas (f + g)) 2).integrable_sq
  have hfmg_sq : Integrable (fun ω : S' d => (ω (f - g)) ^ 2) μ :=
    (pairing_memLp_schwinger hm μ hμ hchar (f - g) (hmeas (f - g)) 2).integrable_sq
  have h_int_polar :
      ∫ ω : S' d, ω f * ω g ∂μ =
      (1/4) * (∫ ω, (ω (f + g)) ^ 2 ∂μ - ∫ ω, (ω (f - g)) ^ 2 ∂μ) := by
    rw [← integral_sub hfg_sq hfmg_sq]
    simp_rw [h_polar]
    rw [integral_const_mul]; ring
  rw [h_int_polar,
      second_moment_eq_form hm μ hμ hchar (f + g) (hmeas (f + g)),
      second_moment_eq_form hm μ hμ hchar (f - g) (hmeas (f - g))]
  simp only [freeFieldBilinearForm]; ring

variable (d : ℕ) (m : ℝ)

/-- The two-point Schwinger function equals the bilinear form of the propagator.
    S₂(f, g) = B(f, g) where B is the polarized bilinear form of Q.

    This is the key identity connecting the Euclidean measure (from Minlos' theorem)
    to the propagator (Green's function of the Klein-Gordon operator).
    The proof proceeds via Gaussian moment identification:
    1. The characteristic function hypothesis identifies the pushforward as Gaussian
    2. The second moment of a centered Gaussian gives the quadratic form
    3. Polarization gives the bilinear form

    Note: The proof assumes evaluation maps ω ↦ ω(f) are measurable in the given
    σ-algebra on S'(ℝᵈ). This holds for the cylinder σ-algebra from Minlos' theorem. -/
theorem schwingerTwoPoint_eq_bilinear
    [MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ)]
    (μ : Measure (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ))
    (_hμ : IsProbabilityMeasure μ)
    (_hchar : ∀ f, freeFieldCharacteristic d m f =
      ∫ ω : (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ), exp (↑(ω f) * I) ∂μ)
    (hm : 0 ≤ m)
    (hmeas : ∀ h : 𝓢(EuclideanSpace ℝ (Fin d), ℝ),
      Measurable (fun ω : S' d => ω h))
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    schwingerTwoPoint d μ f g = ↑(freeFieldBilinearForm d m f g) := by
  -- The Schwinger two-point function is the complex integral ∫ (ω f : ℂ) * (ω g : ℂ) dμ
  -- which equals ↑(∫ ω f * ω g dμ) since the integrand is real-valued cast to ℂ.
  simp only [schwingerTwoPoint]
  -- Rewrite complex multiplication of real casts: (↑a : ℂ) * (↑b : ℂ) = ↑(a * b)
  simp_rw [← Complex.ofReal_mul]
  -- Pull the ofReal cast out of the integral
  rw [integral_complex_ofReal]
  -- Now the goal is ↑(∫ ω, ω f * ω g ∂μ) = ↑(freeFieldBilinearForm d m f g)
  congr 1
  exact cross_moment_eq_bilinear hm μ _hμ _hchar f g hmeas

end
