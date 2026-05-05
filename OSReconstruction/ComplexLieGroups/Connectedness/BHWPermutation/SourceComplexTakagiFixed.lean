import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSmallFactor

/-!
# Fixed real form for conjugate-linear Takagi involutions

This file isolates the first general fixed-space facts used in the
Autonne-Takagi positive-eigenspace phase construction.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator ComplexOrder

namespace BHW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Real fixed submodule of a conjugate-linear isometric equivalence. -/
def conjugationFixedSubmodule
    (J : E ≃ₗᵢ⋆[ℂ] E) : Submodule ℝ E where
  carrier := {x | J x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    calc
      J (x + y) = J x + J y := map_add J x y
      _ = x + y := by rw [hx, hy]
  smul_mem' := by
    intro a x hx
    calc
      J (a • x) = J ((a : ℂ) • x) :=
        congrArg J (RCLike.real_smul_eq_coe_smul (K := ℂ) a x)
      _ = star (a : ℂ) • J x := map_smulₛₗ J (a : ℂ) x
      _ = (a : ℂ) • x := by
        have hstar : star (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
        rw [hstar, hx]
      _ = a • x := Complex.coe_smul a x

/-- The fixed real part `(x + Jx)/2`. -/
theorem conjugationFixed_realPart_mem
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ_sq : ∀ x, J (J x) = x) (x : E) :
    ((2 : ℝ)⁻¹ • (x + J x)) ∈ conjugationFixedSubmodule (E := E) J := by
  change J ((2 : ℝ)⁻¹ • (x + J x)) = (2 : ℝ)⁻¹ • (x + J x)
  calc
    J ((2 : ℝ)⁻¹ • (x + J x)) =
        J ((((2 : ℝ)⁻¹ : ℝ) : ℂ) • (x + J x)) :=
      congrArg J (RCLike.real_smul_eq_coe_smul (K := ℂ) ((2 : ℝ)⁻¹) (x + J x))
    _ = star ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) • J (x + J x) :=
      map_smulₛₗ J ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) (x + J x)
    _ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) • (x + J x) := by
      have hstar : star ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) =
          ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) :=
        Complex.conj_ofReal ((2 : ℝ)⁻¹)
      rw [hstar, map_add, hJ_sq x, add_comm]
    _ = (2 : ℝ)⁻¹ • (x + J x) := Complex.coe_smul ((2 : ℝ)⁻¹) (x + J x)

/-- The fixed imaginary-coordinate part `(Jx - x)/(2i)`, written as
`(1/2) * i * (Jx - x)` in scalar notation. -/
theorem conjugationFixed_imagPart_mem
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ_sq : ∀ x, J (J x) = x) (x : E) :
    ((2 : ℝ)⁻¹ • ((Complex.I : ℂ) • (J x - x))) ∈
      conjugationFixedSubmodule (E := E) J := by
  change J ((2 : ℝ)⁻¹ • ((Complex.I : ℂ) • (J x - x))) =
    (2 : ℝ)⁻¹ • ((Complex.I : ℂ) • (J x - x))
  calc
    J ((2 : ℝ)⁻¹ • ((Complex.I : ℂ) • (J x - x))) =
        J ((((2 : ℝ)⁻¹ : ℝ) : ℂ) • ((Complex.I : ℂ) • (J x - x))) :=
      congrArg J (RCLike.real_smul_eq_coe_smul (K := ℂ) ((2 : ℝ)⁻¹)
        ((Complex.I : ℂ) • (J x - x)))
    _ = star ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) •
        J ((Complex.I : ℂ) • (J x - x)) :=
      map_smulₛₗ J ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) ((Complex.I : ℂ) • (J x - x))
    _ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) • ((Complex.I : ℂ) • (J x - x)) := by
      have hstar : star ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) =
          ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) :=
        Complex.conj_ofReal ((2 : ℝ)⁻¹)
      have hI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
      rw [hstar, map_smulₛₗ, map_sub, hJ_sq x, hI]
      module
    _ = (2 : ℝ)⁻¹ • ((Complex.I : ℂ) • (J x - x)) :=
      Complex.coe_smul ((2 : ℝ)⁻¹) ((Complex.I : ℂ) • (J x - x))

/-- Bundled fixed real part of a vector. -/
def conjugationFixedRealPart
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ_sq : ∀ x, J (J x) = x) (x : E) :
    conjugationFixedSubmodule (E := E) J :=
  ⟨(2 : ℝ)⁻¹ • (x + J x), conjugationFixed_realPart_mem J hJ_sq x⟩

/-- Bundled fixed imaginary-coordinate part of a vector. -/
def conjugationFixedImagPart
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ_sq : ∀ x, J (J x) = x) (x : E) :
    conjugationFixedSubmodule (E := E) J :=
  ⟨(2 : ℝ)⁻¹ • ((Complex.I : ℂ) • (J x - x)),
    conjugationFixed_imagPart_mem J hJ_sq x⟩

/-- Every vector decomposes as a fixed vector plus `i` times a fixed vector. -/
theorem conjugationFixed_decomposition_apply
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ_sq : ∀ x, J (J x) = x) (x : E) :
    (conjugationFixedRealPart J hJ_sq x : E) +
        (Complex.I : ℂ) • (conjugationFixedImagPart J hJ_sq x : E) = x := by
  change (2 : ℝ)⁻¹ • (x + J x) +
      (Complex.I : ℂ) • ((2 : ℝ)⁻¹ • ((Complex.I : ℂ) • (J x - x))) = x
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) ((2 : ℝ)⁻¹) (x + J x)]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) ((2 : ℝ)⁻¹)
    ((Complex.I : ℂ) • (J x - x))]
  rw [smul_smul, smul_smul]
  change (((((2 : ℝ)⁻¹ : ℝ) : ℂ)) • (x + J x) +
      (Complex.I * ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) * Complex.I) • (J x - x) = x)
  have hscalar :
      (Complex.I * ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) * Complex.I) =
        -(((((2 : ℝ)⁻¹ : ℝ) : ℂ))) := by
    rw [mul_comm Complex.I ((((2 : ℝ)⁻¹ : ℝ) : ℂ)), mul_assoc, Complex.I_mul_I]
    ring
  rw [hscalar]
  norm_num
  module

theorem conjugationFixed_decomposition_surjective
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ_sq : ∀ x, J (J x) = x) :
    Function.Surjective
      (fun p : conjugationFixedSubmodule (E := E) J × conjugationFixedSubmodule (E := E) J =>
        (p.1 : E) + (Complex.I : ℂ) • (p.2 : E)) := by
  intro x
  refine ⟨(conjugationFixedRealPart J hJ_sq x, conjugationFixedImagPart J hJ_sq x), ?_⟩
  exact conjugationFixed_decomposition_apply J hJ_sq x

/-- The fixed real form gives a unique decomposition `x = p + i q`. -/
theorem conjugationFixed_decomposition_injective
    (J : E ≃ₗᵢ⋆[ℂ] E) :
    Function.Injective
      (fun p : conjugationFixedSubmodule (E := E) J × conjugationFixedSubmodule (E := E) J =>
        (p.1 : E) + (Complex.I : ℂ) • (p.2 : E)) := by
  intro p q hpq
  have hpq' :
      (p.1 : E) + (Complex.I : ℂ) • (p.2 : E) =
        (q.1 : E) + (Complex.I : ℂ) • (q.2 : E) := hpq
  ext
  · have hdiff : ((p.1 : E) - (q.1 : E)) +
        (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E)) = 0 := by
      calc
        ((p.1 : E) - (q.1 : E)) +
            (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E)) =
            ((p.1 : E) + (Complex.I : ℂ) • (p.2 : E)) -
              ((q.1 : E) + (Complex.I : ℂ) • (q.2 : E)) := by
          module
        _ = 0 := sub_eq_zero.mpr hpq'
    have hfix1 : J ((p.1 : E) - (q.1 : E)) = (p.1 : E) - (q.1 : E) := by
      rw [map_sub, p.1.2, q.1.2]
    have hfix2 : J ((p.2 : E) - (q.2 : E)) = (p.2 : E) - (q.2 : E) := by
      rw [map_sub, p.2.2, q.2.2]
    have hdiffJ : ((p.1 : E) - (q.1 : E)) -
        (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E)) = 0 := by
      have hJ := congrArg J hdiff
      rw [map_add, map_smulₛₗ, hfix1, hfix2] at hJ
      have hI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
      rw [hI] at hJ
      simpa [sub_eq_add_neg, neg_smul, add_comm, add_left_comm, add_assoc] using hJ
    have htwo : (2 : ℂ) • ((p.1 : E) - (q.1 : E)) = 0 := by
      calc
        (2 : ℂ) • ((p.1 : E) - (q.1 : E)) =
            (((p.1 : E) - (q.1 : E)) +
              (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E))) +
              (((p.1 : E) - (q.1 : E)) -
                (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E))) := by
          module
        _ = 0 := by rw [hdiff, hdiffJ]; simp
    have hzero : ((p.1 : E) - (q.1 : E)) = 0 := by
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact sub_eq_zero.mp hzero
  · have hdiff : ((p.1 : E) - (q.1 : E)) +
        (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E)) = 0 := by
      calc
        ((p.1 : E) - (q.1 : E)) +
            (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E)) =
            ((p.1 : E) + (Complex.I : ℂ) • (p.2 : E)) -
              ((q.1 : E) + (Complex.I : ℂ) • (q.2 : E)) := by
          module
        _ = 0 := sub_eq_zero.mpr hpq'
    have hfix1 : J ((p.1 : E) - (q.1 : E)) = (p.1 : E) - (q.1 : E) := by
      rw [map_sub, p.1.2, q.1.2]
    have hfix2 : J ((p.2 : E) - (q.2 : E)) = (p.2 : E) - (q.2 : E) := by
      rw [map_sub, p.2.2, q.2.2]
    have hdiffJ : ((p.1 : E) - (q.1 : E)) -
        (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E)) = 0 := by
      have hJ := congrArg J hdiff
      rw [map_add, map_smulₛₗ, hfix1, hfix2] at hJ
      have hI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
      rw [hI] at hJ
      simpa [sub_eq_add_neg, neg_smul, add_comm, add_left_comm, add_assoc] using hJ
    have hzero : ((p.2 : E) - (q.2 : E)) = 0 := by
      have hsub : (2 : ℂ) • ((Complex.I : ℂ) • ((p.2 : E) - (q.2 : E))) = 0 := by
        calc
          (2 : ℂ) • ((Complex.I : ℂ) • ((p.2 : E) - (q.2 : E))) =
              (((p.1 : E) - (q.1 : E)) +
                (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E))) -
                (((p.1 : E) - (q.1 : E)) -
                  (Complex.I : ℂ) • ((p.2 : E) - (q.2 : E))) := by
            module
          _ = 0 := by rw [hdiff, hdiffJ]; simp
      have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
      have hscalar_ne : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) hI_ne
      rw [smul_smul] at hsub
      exact (smul_eq_zero.mp hsub).resolve_left hscalar_ne
    exact sub_eq_zero.mp hzero

/-- The fixed-pair decomposition as a real-linear map. -/
def conjugationFixedPairToComplex
    (J : E ≃ₗᵢ⋆[ℂ] E) :
    (conjugationFixedSubmodule (E := E) J × conjugationFixedSubmodule (E := E) J) →ₗ[ℝ] E where
  toFun p := (p.1 : E) + (Complex.I : ℂ) • (p.2 : E)
  map_add' := by
    intro p q
    change ((p.1 : E) + (q.1 : E)) + (Complex.I : ℂ) • ((p.2 : E) + (q.2 : E)) =
      ((p.1 : E) + (Complex.I : ℂ) • (p.2 : E)) +
        ((q.1 : E) + (Complex.I : ℂ) • (q.2 : E))
    rw [smul_add]
    abel
  map_smul' := by
    intro a p
    change (a • (p.1 : E)) + (Complex.I : ℂ) • (a • (p.2 : E)) =
      a • ((p.1 : E) + (Complex.I : ℂ) • (p.2 : E))
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a (p.2 : E)]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a (p.1 : E)]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a
      ((p.1 : E) + (Complex.I : ℂ) • (p.2 : E))]
    rw [smul_add]
    module

/-- The fixed-pair decomposition as a real-linear equivalence. -/
def conjugationFixedPairLinearEquiv
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ_sq : ∀ x, J (J x) = x) :
    (conjugationFixedSubmodule (E := E) J × conjugationFixedSubmodule (E := E) J) ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (conjugationFixedPairToComplex J)
    ⟨conjugationFixed_decomposition_injective J,
      conjugationFixed_decomposition_surjective J hJ_sq⟩

/-- The fixed real form has real dimension equal to the original complex
dimension. -/
theorem conjugationFixedSubmodule_finrank
    [FiniteDimensional ℂ E]
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ_sq : ∀ x, J (J x) = x) :
    Module.finrank ℝ (conjugationFixedSubmodule (E := E) J) = Module.finrank ℂ E := by
  have hprod : Module.finrank ℝ
        (conjugationFixedSubmodule (E := E) J × conjugationFixedSubmodule (E := E) J) =
      Module.finrank ℝ E :=
    LinearEquiv.finrank_eq (conjugationFixedPairLinearEquiv J hJ_sq)
  rw [Module.finrank_prod] at hprod
  rw [finrank_real_of_complex E] at hprod
  omega

end BHW
