import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported
import OSReconstruction.SCV.LaplaceHolomorphic
import OSReconstruction.vNA.Bochner.LaplaceBridge

/-!
# RMK Spectral Functional for Bounded Self-Adjoint Operators

This file constructs the diagonal scalar spectral measure for a bounded self-adjoint
operator directly on its compact real spectrum, using Mathlib's continuous functional
calculus and the Riesz-Markov-Kakutani theorem.

This is the bounded self-adjoint analogue of `SpectralFunctionalViaRMK.lean` for
unitary operators, but it avoids the Cayley-transform detour entirely.
-/

noncomputable section

open scoped ComplexConjugate CompactlySupported
open MeasureTheory Topology ContinuousMap CompactlySupportedContinuousMap
open scoped NNReal

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Mathlib 4.29 compatibility: provide instances that typeclass synthesis can't find
-- with the stricter backward.isDefEq.respectTransparency
set_option backward.isDefEq.respectTransparency false in
private instance : SMulCommClass ℂ ℝ H := inferInstance

set_option backward.isDefEq.respectTransparency false in
private instance : NonnegSpectrumClass ℝ (H →L[ℂ] H) :=
  CStarAlgebra.instNonnegSpectrumClass


omit [CompleteSpace H] in
/-- The polarization identity for a continuous linear map on a complex Hilbert space. -/
private theorem inner_polarization_clm_local (A : H →L[ℂ] H) (x y : H) :
    (1 / 4 : ℂ) * (@inner ℂ H _ (x + y) (A (x + y)) - @inner ℂ H _ (x - y) (A (x - y))
      - Complex.I * @inner ℂ H _ (x + Complex.I • y) (A (x + Complex.I • y))
      + Complex.I * @inner ℂ H _ (x - Complex.I • y) (A (x - Complex.I • y))) =
    @inner ℂ H _ x (A y) := by
  set a := @inner ℂ H _ x (A x)
  set b := @inner ℂ H _ x (A y)
  set c := @inner ℂ H _ y (A x)
  set d := @inner ℂ H _ y (A y)
  have h1 : @inner ℂ H _ (x + y) (A (x + y)) = a + b + c + d := by
    rw [map_add]
    simp only [inner_add_left, inner_add_right]
    ring
  have h2 : @inner ℂ H _ (x - y) (A (x - y)) = a - b - c + d := by
    rw [map_sub]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hI_sq : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  have h3 : @inner ℂ H _ (x + Complex.I • y) (A (x + Complex.I • y)) =
      a + Complex.I * b - Complex.I * c + d := by
    rw [map_add, map_smul]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I]
    ring_nf
    rw [hI_sq]
    ring
  have h4 : @inner ℂ H _ (x - Complex.I • y) (A (x - Complex.I • y)) =
      a - Complex.I * b + Complex.I * c + d := by
    rw [map_sub, map_smul]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
    ring_nf
    rw [hI_sq]
    ring
  rw [h1, h2, h3, h4]
  ring_nf
  rw [hI_sq]
  ring

/-- The scalar functional on the compact real spectrum of a bounded self-adjoint operator. -/
def selfAdjointSpectralFunctionalAux
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (f : C(spectrum ℝ A, ℝ)) : ℝ :=
  Complex.re (@inner ℂ H _ x ((cfcHom hA f) x))

/-- The scalar functional is real-linear in the test function. -/
def selfAdjointSpectralFunctionalLinear
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    C(spectrum ℝ A, ℝ) →ₗ[ℝ] ℝ where
  toFun := selfAdjointSpectralFunctionalAux A hA x
  map_add' := by
    intro f g
    simp [selfAdjointSpectralFunctionalAux, inner_add_right, Complex.add_re]
  map_smul' := by
    intro c f
    rw [selfAdjointSpectralFunctionalAux, map_smul, ContinuousLinearMap.smul_apply]
    have hsmul :
        @inner ℂ H _ x (c • (((cfcHom hA) f) x)) =
          c • @inner ℂ H _ x (((cfcHom hA) f) x) := by
      set_option backward.isDefEq.respectTransparency false in
      haveI : IsScalarTower ℝ ℂ H := inferInstance
      rw [show (c : ℝ) • (((cfcHom hA) f) x) = ((c : ℂ) : ℂ) • (((cfcHom hA) f) x) from
        (algebraMap_smul ℂ c _).symm]
      rw [inner_smul_right]
      simp [starRingEnd_apply, Complex.real_smul]
    rw [hsmul, Complex.smul_re]
    rfl

/-- Positivity of the scalar functional for nonnegative spectrum functions. -/
theorem selfAdjointSpectralFunctionalAux_nonneg
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (f : C(spectrum ℝ A, ℝ)) (hf : 0 ≤ f) :
    0 ≤ selfAdjointSpectralFunctionalAux A hA x f := by
  have hnonneg : (0 : H →L[ℂ] H) ≤ cfcHom hA f := by
    exact (cfcHom_nonneg_iff (a := A) hA).2 hf
  have hpos : (cfcHom hA f).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact hnonneg
  exact hpos.re_inner_nonneg_right x

/-- The compactly-supported positive functional on the real spectrum. -/
def selfAdjointSpectralFunctionalCc
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    C_c(spectrum ℝ A, ℝ) →ₚ[ℝ] ℝ := by
  refine PositiveLinearMap.mk₀ ?_ ?_
  · exact
      { toFun := fun f => selfAdjointSpectralFunctionalAux A hA x f.toContinuousMap
        map_add' := by
          intro f g
          rw [selfAdjointSpectralFunctionalAux]
          rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap by rfl]
          rw [map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
          rfl
        map_smul' := by
          intro c f
          rw [selfAdjointSpectralFunctionalAux,
            show (c • f).toContinuousMap = c • f.toContinuousMap by rfl]
          rw [map_smul, ContinuousLinearMap.smul_apply]
          have hsmul :
              @inner ℂ H _ x (c • (((cfcHom hA) f.toContinuousMap) x)) =
                c • @inner ℂ H _ x (((cfcHom hA) f.toContinuousMap) x) := by
            set_option backward.isDefEq.respectTransparency false in
            haveI : IsScalarTower ℝ ℂ H := inferInstance
            rw [show (c : ℝ) • (((cfcHom hA) f.toContinuousMap) x) =
              ((c : ℂ) : ℂ) • (((cfcHom hA) f.toContinuousMap) x) from
              (algebraMap_smul ℂ c _).symm]
            rw [inner_smul_right]
            simp [starRingEnd_apply, Complex.real_smul]
          rw [hsmul, Complex.smul_re]
          rfl }
  · intro f hf
    exact selfAdjointSpectralFunctionalAux_nonneg A hA x f.toContinuousMap hf

/-- The RMK diagonal spectral measure on the compact real spectrum. -/
def selfAdjointSpectralMeasureDiagonal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    Measure (spectrum ℝ A) :=
  RealRMK.rieszMeasure (selfAdjointSpectralFunctionalCc A hA x)

/-- The RMK measure represents the compactly-supported spectral functional. -/
theorem selfAdjointSpectralMeasureDiagonal_integral
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (f : C_c(spectrum ℝ A, ℝ)) :
    ∫ y, f y ∂(selfAdjointSpectralMeasureDiagonal A hA x) =
      (selfAdjointSpectralFunctionalCc A hA x) f :=
  RealRMK.integral_rieszMeasure (selfAdjointSpectralFunctionalCc A hA x) f

/-- The total mass of the diagonal spectral measure is `‖x‖²`. -/
theorem selfAdjointSpectralMeasureDiagonal_univ
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    (selfAdjointSpectralMeasureDiagonal A hA x Set.univ).toReal = ‖x‖ ^ 2 := by
  haveI : IsFiniteMeasure (selfAdjointSpectralMeasureDiagonal A hA x) := by
    unfold selfAdjointSpectralMeasureDiagonal
    infer_instance
  let oneCc : C_c(spectrum ℝ A, ℝ) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
  have hreal :
      (selfAdjointSpectralMeasureDiagonal A hA x Set.univ).toReal =
        (selfAdjointSpectralMeasureDiagonal A hA x).real Set.univ := rfl
  calc
    (selfAdjointSpectralMeasureDiagonal A hA x Set.univ).toReal
      = (selfAdjointSpectralMeasureDiagonal A hA x).real Set.univ := hreal
    _ = ∫ y, (1 : ℝ) ∂(selfAdjointSpectralMeasureDiagonal A hA x) := by
          symm
          have hconst :=
            MeasureTheory.integral_const (μ := selfAdjointSpectralMeasureDiagonal A hA x) (1 : ℝ)
          simp only [smul_eq_mul, mul_one] at hconst
          exact hconst
    _ = ∫ y, oneCc y ∂(selfAdjointSpectralMeasureDiagonal A hA x) := by rfl
    _ = (selfAdjointSpectralFunctionalCc A hA x) oneCc := by
          exact selfAdjointSpectralMeasureDiagonal_integral A hA x oneCc
    _ = Complex.re (@inner ℂ H _ x ((cfcHom hA oneCc.toContinuousMap) x)) := by rfl
    _ = Complex.re (@inner ℂ H _ x x) := by
          rw [show oneCc.toContinuousMap = (1 : C(spectrum ℝ A, ℝ)) by rfl]
          rw [map_one (cfcHom hA)]
          simp
    _ = ‖x‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]
          norm_cast

/-- The diagonal matrix element of `cfc g A` is represented by the RMK measure on the real
spectrum of the bounded self-adjoint operator `A`. -/
theorem re_inner_cfc_eq_integral_selfAdjointSpectralMeasureDiagonal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (g : ℝ → ℝ) (hg : ContinuousOn g (spectrum ℝ A)) :
    Complex.re (@inner ℂ H _ x ((cfc g A) x)) =
      ∫ y, g y ∂(selfAdjointSpectralMeasureDiagonal A hA x) := by
  let gSpec : C(spectrum ℝ A, ℝ) := ⟨(spectrum ℝ A).restrict g, hg.restrict⟩
  let gCc : C_c(spectrum ℝ A, ℝ) := ⟨gSpec, HasCompactSupport.of_compactSpace _⟩
  calc
    Complex.re (@inner ℂ H _ x ((cfc g A) x))
      = Complex.re (@inner ℂ H _ x ((cfcHom hA gSpec) x)) := by
          rw [cfc_apply g A hA hg]
    _ = Complex.re (@inner ℂ H _ x ((cfcHom hA gCc.toContinuousMap) x)) := by
          rfl
    _ = (selfAdjointSpectralFunctionalCc A hA x) gCc := by rfl
    _ = ∫ y, gCc y ∂(selfAdjointSpectralMeasureDiagonal A hA x) := by
          symm
          exact selfAdjointSpectralMeasureDiagonal_integral A hA x gCc
    _ = ∫ y, g y ∂(selfAdjointSpectralMeasureDiagonal A hA x) := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a bounded nonnegative self-adjoint operator, the diagonal matrix element of a positive
functional-calculus power is represented by the RMK measure on the real spectrum. -/
theorem re_inner_nnrpow_eq_integral_selfAdjointSpectralMeasureDiagonal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hA_nonneg : 0 ≤ A) (x : H)
    (t : ℝ≥0) (ht : 0 < t) :
    Complex.re (@inner ℂ H _ x ((CFC.nnrpow A t) x)) =
      ∫ y, (y : ℝ) ^ (t : ℝ) ∂(selfAdjointSpectralMeasureDiagonal A hA x) := by
  calc
    Complex.re (@inner ℂ H _ x ((CFC.nnrpow A t) x))
      = Complex.re (@inner ℂ H _ x ((cfc (fun y : ℝ => y ^ (t : ℝ)) A) x)) := by
          change Complex.re (@inner ℂ H _ x ((A ^ t) x)) =
            Complex.re (@inner ℂ H _ x ((cfc (fun y : ℝ => y ^ (t : ℝ)) A) x))
          rw [CFC.nnrpow_eq_rpow (A := H →L[ℂ] H) ht]
          rw [CFC.rpow_eq_cfc_real (A := H →L[ℂ] H) (a := A) (y := (t : ℝ)) hA_nonneg]
    _ = ∫ y, (y : ℝ) ^ (t : ℝ) ∂(selfAdjointSpectralMeasureDiagonal A hA x) := by
          exact re_inner_cfc_eq_integral_selfAdjointSpectralMeasureDiagonal
            A hA x (fun y : ℝ => y ^ (t : ℝ))
            (continuousOn_id.rpow_const fun _ _ => Or.inr (le_of_lt (show (0 : ℝ) < (t : ℝ) by
              exact_mod_cast ht)))

/-- The diagonal RMK spectral measure, pushed from the compact real spectrum to `ℝ`. -/
def selfAdjointSpectralMeasureDiagonalReal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) : Measure ℝ :=
  (selfAdjointSpectralMeasureDiagonal A hA x).map ((↑) : spectrum ℝ A → ℝ)

instance selfAdjointSpectralMeasureDiagonalReal_isFinite
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    IsFiniteMeasure (selfAdjointSpectralMeasureDiagonalReal A hA x) := by
  haveI : IsFiniteMeasure (selfAdjointSpectralMeasureDiagonal A hA x) := by
    unfold selfAdjointSpectralMeasureDiagonal
    infer_instance
  unfold selfAdjointSpectralMeasureDiagonalReal
  infer_instance

/-- The diagonal matrix element of a positive functional-calculus power, written over a measure
on the real line rather than the compact subtype spectrum. -/
theorem re_inner_nnrpow_eq_integral_selfAdjointSpectralMeasureDiagonalReal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hA_nonneg : 0 ≤ A) (x : H)
    (t : ℝ≥0) (ht : 0 < t) :
    Complex.re (@inner ℂ H _ x ((CFC.nnrpow A t) x)) =
      ∫ s, s ^ (t : ℝ) ∂(selfAdjointSpectralMeasureDiagonalReal A hA x) := by
  have hmeas :
      AEStronglyMeasurable (fun s : ℝ => s ^ (t : ℝ))
        (selfAdjointSpectralMeasureDiagonalReal A hA x) := by
    exact Continuous.aestronglyMeasurable
      (Real.continuous_rpow_const (show 0 ≤ (t : ℝ) by exact_mod_cast ht.le))
  rw [selfAdjointSpectralMeasureDiagonalReal]
  rw [MeasureTheory.integral_map
    ((by fun_prop : Measurable ((↑) : spectrum ℝ A → ℝ))).aemeasurable hmeas]
  simpa using
    (re_inner_nnrpow_eq_integral_selfAdjointSpectralMeasureDiagonal
      (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x) (t := t) ht)

/-- If `σ(A) ⊆ [0,1]`, the pushed-forward diagonal spectral measure has no negative mass. -/
theorem selfAdjointSpectralMeasureDiagonalReal_Iio_eq_zero_of_spectrum_subset_Icc
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1) :
    selfAdjointSpectralMeasureDiagonalReal A hA x (Set.Iio 0) = 0 := by
  rw [selfAdjointSpectralMeasureDiagonalReal]
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hpre : ((↑) : spectrum ℝ A → ℝ) ⁻¹' Set.Iio 0 = ∅ := by
    ext y
    constructor
    · intro hy
      have hyIcc : (y : ℝ) ∈ Set.Icc 0 1 := hspec y.2
      exact False.elim (not_lt_of_ge hyIcc.1 hy)
    · intro hy
      cases hy
  simp [hpre]

/-- If `σ(A) ⊆ [0,1]`, the pushed-forward diagonal spectral measure has no mass above `1`. -/
theorem selfAdjointSpectralMeasureDiagonalReal_Ioi_eq_zero_of_spectrum_subset_Icc
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1) :
    selfAdjointSpectralMeasureDiagonalReal A hA x (Set.Ioi 1) = 0 := by
  rw [selfAdjointSpectralMeasureDiagonalReal]
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
  have hpre : ((↑) : spectrum ℝ A → ℝ) ⁻¹' Set.Ioi 1 = ∅ := by
    ext y
    constructor
    · intro hy
      have hyIcc : (y : ℝ) ∈ Set.Icc 0 1 := hspec y.2
      exact False.elim (not_lt_of_ge hyIcc.2 hy)
    · intro hy
      cases hy
  simp [hpre]

/-- For a bounded nonnegative self-adjoint operator, the diagonal matrix element of a positive
functional-calculus power is the real spectral integral viewed inside `ℂ`. -/
theorem inner_nnrpow_eq_ofReal_integral_selfAdjointSpectralMeasureDiagonalReal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hA_nonneg : 0 ≤ A) (x : H)
    (t : ℝ≥0) (ht : 0 < t) :
    @inner ℂ H _ x ((CFC.nnrpow A t) x) =
      (((∫ s, s ^ (t : ℝ) ∂(selfAdjointSpectralMeasureDiagonalReal A hA x)) : ℝ) : ℂ) := by
  have hpow_nonneg : 0 ≤ CFC.nnrpow A t := by
    exact CFC.nnrpow_nonneg (a := A)
  have hpow_pos : IsPositive (CFC.nnrpow A t) := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact hpow_nonneg
  open ComplexOrder in
  have hinner_nonneg :
      0 ≤ @inner ℂ H _ x ((CFC.nnrpow A t) x) :=
    hpow_pos.inner_nonneg_right x
  apply Complex.ext
  · simpa using
      re_inner_nnrpow_eq_integral_selfAdjointSpectralMeasureDiagonalReal
        (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x) (t := t) ht
  · simpa using (Complex.nonneg_iff.mp hinner_nonneg).2.symm

/-- If `σ(A) ⊆ [0,1]`, the diagonal matrix element of a positive functional-calculus power is a
Laplace transform on `[0,∞)` after deleting the zero spectral atom. -/
theorem inner_nnrpow_eq_laplace_selfAdjointSpectralMeasureDiagonalReal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hA_nonneg : 0 ≤ A) (x : H)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (t : ℝ≥0) (ht : 0 < t) :
    @inner ℂ H _ x ((CFC.nnrpow A t) x) =
      (((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA x)) : ℝ) : ℂ) := by
  have hsupp_nonneg :
      selfAdjointSpectralMeasureDiagonalReal A hA x (Set.Iio 0) = 0 :=
    selfAdjointSpectralMeasureDiagonalReal_Iio_eq_zero_of_spectrum_subset_Icc
      (A := A) (hA := hA) (x := x) hspec
  have hsupp_le_one :
      selfAdjointSpectralMeasureDiagonalReal A hA x (Set.Ioi 1) = 0 :=
    selfAdjointSpectralMeasureDiagonalReal_Ioi_eq_zero_of_spectrum_subset_Icc
      (A := A) (hA := hA) (x := x) hspec
  have hpow_integrable :
      Integrable (fun s : ℝ => s ^ (t : ℝ))
        (selfAdjointSpectralMeasureDiagonalReal A hA x) := by
    have hmeas :
        AEStronglyMeasurable (fun s : ℝ => s ^ (t : ℝ))
          (selfAdjointSpectralMeasureDiagonalReal A hA x) := by
      exact Continuous.aestronglyMeasurable
        (Real.continuous_rpow_const (show 0 ≤ (t : ℝ) by exact_mod_cast ht.le))
    have hae_nonneg : ∀ᵐ s ∂(selfAdjointSpectralMeasureDiagonalReal A hA x), 0 ≤ s := by
      rw [ae_iff]
      simpa [Set.compl_setOf, not_le] using hsupp_nonneg
    have hae_le_one : ∀ᵐ s ∂(selfAdjointSpectralMeasureDiagonalReal A hA x), s ≤ 1 := by
      rw [ae_iff]
      simpa [Set.compl_setOf, not_le] using hsupp_le_one
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas ?_
    filter_upwards [hae_nonneg, hae_le_one] with s hs_nonneg hs_le_one
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hs_nonneg _)]
    exact Real.rpow_le_one hs_nonneg hs_le_one (show 0 ≤ (t : ℝ) by exact_mod_cast ht.le)
  have hpow_eq_laplace :
      ∫ s, s ^ (t : ℝ) ∂(selfAdjointSpectralMeasureDiagonalReal A hA x) =
        ∫ u, Real.exp (-((t : ℝ) * u)) ∂
          (BochnerLaplaceBridge.laplaceMeasurePos
            (selfAdjointSpectralMeasureDiagonalReal A hA x)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (BochnerLaplaceBridge.spectralIntegral_eq_laplace_restrictZero
        (μ := selfAdjointSpectralMeasureDiagonalReal A hA x)
        (hsupp_nonneg := hsupp_nonneg)
        (t := (t : ℝ))
        (by exact_mod_cast ht)
        hpow_integrable)
  calc
    @inner ℂ H _ x ((CFC.nnrpow A t) x)
      = (((∫ s, s ^ (t : ℝ) ∂(selfAdjointSpectralMeasureDiagonalReal A hA x)) : ℝ) : ℂ) := by
          exact inner_nnrpow_eq_ofReal_integral_selfAdjointSpectralMeasureDiagonalReal
            (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x) (t := t) ht
    _ = (((∫ u,
            Real.exp (-((t : ℝ) * u)) ∂
              BochnerLaplaceBridge.laplaceMeasurePos
                (selfAdjointSpectralMeasureDiagonalReal A hA x)) : ℝ) : ℂ) := by
          exact congrArg (fun r : ℝ => (r : ℂ)) hpow_eq_laplace

/-- Polarization upgrades the diagonal Laplace representation to off-diagonal matrix elements
for positive functional-calculus powers of a bounded nonnegative self-adjoint operator whose
spectrum lies in `[0,1]`. -/
theorem inner_nnrpow_eq_laplace_polarization
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (x y : H) (t : ℝ≥0) (ht : 0 < t) :
    @inner ℂ H _ x ((CFC.nnrpow A t) y) =
      (1 / 4 : ℂ) * ((((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA (x + y))) : ℝ) : ℂ) -
        (((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA (x - y))) : ℝ) : ℂ) -
        Complex.I * (((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA (x + Complex.I • y))) : ℝ) : ℂ) +
        Complex.I * (((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA (x - Complex.I • y))) : ℝ) : ℂ)) := by
  have hpol := inner_polarization_clm_local (A := CFC.nnrpow A t) x y
  calc
    @inner ℂ H _ x ((CFC.nnrpow A t) y)
      = (1 / 4 : ℂ) * (@inner ℂ H _ (x + y) ((CFC.nnrpow A t) (x + y)) -
          @inner ℂ H _ (x - y) ((CFC.nnrpow A t) (x - y)) -
          Complex.I * @inner ℂ H _ (x + Complex.I • y) ((CFC.nnrpow A t) (x + Complex.I • y)) +
          Complex.I * @inner ℂ H _ (x - Complex.I • y) ((CFC.nnrpow A t) (x - Complex.I • y))) := by
            exact hpol.symm
    _ = (1 / 4 : ℂ) * ((((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA (x + y))) : ℝ) : ℂ) -
        (((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA (x - y))) : ℝ) : ℂ) -
        Complex.I * (((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA (x + Complex.I • y))) : ℝ) : ℂ) +
        Complex.I * (((∫ u,
          Real.exp (-((t : ℝ) * u)) ∂
            BochnerLaplaceBridge.laplaceMeasurePos
              (selfAdjointSpectralMeasureDiagonalReal A hA (x - Complex.I • y))) : ℝ) : ℂ)) := by
            rw [ContinuousLinearMap.inner_nnrpow_eq_laplace_selfAdjointSpectralMeasureDiagonalReal
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x + y)
              (hspec := hspec) (t := t) ht]
            rw [ContinuousLinearMap.inner_nnrpow_eq_laplace_selfAdjointSpectralMeasureDiagonalReal
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x - y)
              (hspec := hspec) (t := t) ht]
            rw [ContinuousLinearMap.inner_nnrpow_eq_laplace_selfAdjointSpectralMeasureDiagonalReal
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x + Complex.I • y)
              (hspec := hspec) (t := t) ht]
            rw [ContinuousLinearMap.inner_nnrpow_eq_laplace_selfAdjointSpectralMeasureDiagonalReal
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x - Complex.I • y)
              (hspec := hspec) (t := t) ht]

/-- The complex Laplace transform of the diagonal scalar measure attached to a bounded
nonnegative self-adjoint operator. -/
def selfAdjointSpectralLaplaceDiagonal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) (z : ℂ) : ℂ :=
  ∫ u, Complex.exp (-(z * (u : ℂ))) ∂
    BochnerLaplaceBridge.laplaceMeasurePos
      (selfAdjointSpectralMeasureDiagonalReal A hA x)

/-- The polarized complex Laplace transform encoding off-diagonal matrix elements. -/
def selfAdjointSpectralLaplaceOffdiag
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x y : H) (z : ℂ) : ℂ :=
  (1 / 4 : ℂ) *
    (selfAdjointSpectralLaplaceDiagonal A hA (x + y) z -
      selfAdjointSpectralLaplaceDiagonal A hA (x - y) z -
      Complex.I * selfAdjointSpectralLaplaceDiagonal A hA (x + Complex.I • y) z +
      Complex.I * selfAdjointSpectralLaplaceDiagonal A hA (x - Complex.I • y) z)

/-- The diagonal scalar Laplace transform is holomorphic on the right half-plane once the
operator spectrum lies in `[0,1]`. -/
theorem differentiableOn_selfAdjointSpectralLaplaceDiagonal
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1) (x : H) :
    DifferentiableOn ℂ (selfAdjointSpectralLaplaceDiagonal A hA x) {z : ℂ | 0 < z.re} := by
  haveI : IsFiniteMeasure (selfAdjointSpectralMeasureDiagonalReal A hA x) := by
    infer_instance
  simpa [selfAdjointSpectralLaplaceDiagonal] using
    (SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport
      (μ := BochnerLaplaceBridge.laplaceMeasurePos
        (selfAdjointSpectralMeasureDiagonalReal A hA x))
      (hsupp := BochnerLaplaceBridge.laplaceMeasurePos_nonnegSupport
        (μ := selfAdjointSpectralMeasureDiagonalReal A hA x)
        (hsupp_le_one :=
          selfAdjointSpectralMeasureDiagonalReal_Ioi_eq_zero_of_spectrum_subset_Icc
            (A := A) (hA := hA) (x := x) hspec)))

/-- The polarized scalar Laplace transform is holomorphic on the right half-plane once the
operator spectrum lies in `[0,1]`. -/
theorem differentiableOn_selfAdjointSpectralLaplaceOffdiag
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1) (x y : H) :
    DifferentiableOn ℂ (selfAdjointSpectralLaplaceOffdiag A hA x y) {z : ℂ | 0 < z.re} := by
  have hxy := differentiableOn_selfAdjointSpectralLaplaceDiagonal
    (A := A) (hA := hA) (hspec := hspec) (x := x + y)
  have hmxy := differentiableOn_selfAdjointSpectralLaplaceDiagonal
    (A := A) (hA := hA) (hspec := hspec) (x := x - y)
  have hi1 := differentiableOn_selfAdjointSpectralLaplaceDiagonal
    (A := A) (hA := hA) (hspec := hspec) (x := x + Complex.I • y)
  have hi2 := differentiableOn_selfAdjointSpectralLaplaceDiagonal
    (A := A) (hA := hA) (hspec := hspec) (x := x - Complex.I • y)
  convert
    (DifferentiableOn.const_mul
      ((hxy.add (DifferentiableOn.const_mul hmxy (-1 : ℂ))).add
        ((DifferentiableOn.const_mul hi1 (-Complex.I)).add
          (DifferentiableOn.const_mul hi2 Complex.I)))
      (1 / 4 : ℂ)) using 1
  ext z
  simp [selfAdjointSpectralLaplaceOffdiag, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- At positive real points, the diagonal complex Laplace extension agrees with the
diagonal matrix element of the semigroup powers. -/
theorem selfAdjointSpectralLaplaceDiagonal_ofReal_eq_inner_nnrpow
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hA_nonneg : 0 ≤ A) (x : H)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (t : ℝ) (ht : 0 < t) :
    selfAdjointSpectralLaplaceDiagonal A hA x (t : ℂ) =
      @inner ℂ H _ x ((CFC.nnrpow A (Real.toNNReal t)) x) := by
  calc
    selfAdjointSpectralLaplaceDiagonal A hA x (t : ℂ)
      = (((∫ u, Real.exp (-t * u) ∂
          BochnerLaplaceBridge.laplaceMeasurePos
            (selfAdjointSpectralMeasureDiagonalReal A hA x)) : ℝ) : ℂ) := by
            rw [selfAdjointSpectralLaplaceDiagonal]
            calc
              ∫ u, Complex.exp (-((t : ℂ) * (u : ℂ))) ∂
                  BochnerLaplaceBridge.laplaceMeasurePos
                    (selfAdjointSpectralMeasureDiagonalReal A hA x)
                = ∫ u, ((Real.exp (-t * u) : ℝ) : ℂ) ∂
                    BochnerLaplaceBridge.laplaceMeasurePos
                      (selfAdjointSpectralMeasureDiagonalReal A hA x) := by
                        apply integral_congr_ae
                        filter_upwards with u
                        rw [show -((t : ℂ) * (u : ℂ)) = ((-t * u : ℝ) : ℂ) by simp]
                        rw [← Complex.ofReal_exp]
              _ = (((∫ u, Real.exp (-t * u) ∂
                    BochnerLaplaceBridge.laplaceMeasurePos
                      (selfAdjointSpectralMeasureDiagonalReal A hA x)) : ℝ) : ℂ) := by
                        rw [_root_.integral_complex_ofReal]
    _ = @inner ℂ H _ x ((CFC.nnrpow A (Real.toNNReal t)) x) := by
          simpa [Real.toNNReal_of_nonneg ht.le, mul_comm, mul_left_comm, mul_assoc] using
            (inner_nnrpow_eq_laplace_selfAdjointSpectralMeasureDiagonalReal
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x)
              (hspec := hspec) (t := Real.toNNReal t) (by simpa using ht)).symm

/-- At positive real points, the polarized complex Laplace extension agrees with the
off-diagonal matrix element of the semigroup powers. -/
theorem selfAdjointSpectralLaplaceOffdiag_ofReal_eq_inner_nnrpow
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (x y : H) (t : ℝ) (ht : 0 < t) :
    selfAdjointSpectralLaplaceOffdiag A hA x y (t : ℂ) =
      @inner ℂ H _ x ((CFC.nnrpow A (Real.toNNReal t)) y) := by
  calc
    selfAdjointSpectralLaplaceOffdiag A hA x y (t : ℂ)
      = (1 / 4 : ℂ) *
          (selfAdjointSpectralLaplaceDiagonal A hA (x + y) (t : ℂ) -
            selfAdjointSpectralLaplaceDiagonal A hA (x - y) (t : ℂ) -
            Complex.I * selfAdjointSpectralLaplaceDiagonal A hA (x + Complex.I • y) (t : ℂ) +
            Complex.I * selfAdjointSpectralLaplaceDiagonal A hA (x - Complex.I • y) (t : ℂ)) := by
            rfl
    _ = (1 / 4 : ℂ) *
          (@inner ℂ H _ (x + y) ((CFC.nnrpow A (Real.toNNReal t)) (x + y)) -
            @inner ℂ H _ (x - y) ((CFC.nnrpow A (Real.toNNReal t)) (x - y)) -
            Complex.I * @inner ℂ H _ (x + Complex.I • y)
              ((CFC.nnrpow A (Real.toNNReal t)) (x + Complex.I • y)) +
            Complex.I * @inner ℂ H _ (x - Complex.I • y)
              ((CFC.nnrpow A (Real.toNNReal t)) (x - Complex.I • y))) := by
            rw [selfAdjointSpectralLaplaceDiagonal_ofReal_eq_inner_nnrpow
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x + y)
              (hspec := hspec) (t := t) ht]
            rw [selfAdjointSpectralLaplaceDiagonal_ofReal_eq_inner_nnrpow
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x - y)
              (hspec := hspec) (t := t) ht]
            rw [selfAdjointSpectralLaplaceDiagonal_ofReal_eq_inner_nnrpow
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x + Complex.I • y)
              (hspec := hspec) (t := t) ht]
            rw [selfAdjointSpectralLaplaceDiagonal_ofReal_eq_inner_nnrpow
              (A := A) (hA := hA) (hA_nonneg := hA_nonneg) (x := x - Complex.I • y)
              (hspec := hspec) (t := t) ht]
    _ = @inner ℂ H _ x ((CFC.nnrpow A (Real.toNNReal t)) y) := by
          simpa [Real.toNNReal_of_nonneg ht.le] using
            (inner_polarization_clm_local (A := CFC.nnrpow A (Real.toNNReal t)) x y)

end ContinuousLinearMap
