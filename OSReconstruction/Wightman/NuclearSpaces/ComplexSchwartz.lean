/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Topology.Algebra.Module.Equiv
import OSReconstruction.Wightman.NuclearSpaces.SchwartzNuclear

/-!
# Complex-Valued Schwartz Space as a Real Nuclear Space

This file packages the real/imaginary-part decomposition of complex-valued
Schwartz functions as continuous linear maps and continuous linear equivalences
over `ℝ`.

The main structural consequence is that once `𝓢(D, ℝ)` is known to be nuclear,
`𝓢(D, ℂ)` is nuclear as a real locally convex space by transport across
`𝓢(D, ℂ) ≃L[ℝ] 𝓢(D, ℝ) × 𝓢(D, ℝ)`.
-/

open scoped SchwartzMap

noncomputable section

namespace SchwartzMap

open SchwartzMap

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Real part as a continuous linear map on Schwartz spaces. -/
def realPartCLM : 𝓢(D, ℂ) →L[ℝ] 𝓢(D, ℝ) :=
  SchwartzMap.mkCLM (𝕜 := ℝ) (𝕜' := ℝ)
    (fun f x => Complex.reCLM (f x))
    (fun f g x => by simp)
    (fun a f x => by simp [RingHom.id_apply])
    (fun f => Complex.reCLM.contDiff.comp f.smooth')
    (fun ⟨k, n⟩ => ⟨{(k, n)}, 1, zero_le_one, fun f x => by
      simp only [Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul]
      calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Complex.reCLM ∘ ⇑f) x‖
            ≤ ‖x‖ ^ k * (‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ n f x‖) := by
                gcongr
                exact ContinuousLinearMap.norm_iteratedFDeriv_comp_left
                  (L := Complex.reCLM)
                  (f := ⇑f) (x := x)
                  ((f.smooth n).contDiffAt)
                  (n := n) le_rfl
        _ = ‖Complex.reCLM‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by ring
        _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by simp
        _ ≤ SchwartzMap.seminorm ℝ k n f := SchwartzMap.le_seminorm ℝ k n f x⟩)

@[simp] theorem realPartCLM_apply (f : 𝓢(D, ℂ)) (x : D) :
    realPartCLM f x = (f x).re := rfl

/-- Imaginary part as a continuous linear map on Schwartz spaces. -/
def imagPartCLM : 𝓢(D, ℂ) →L[ℝ] 𝓢(D, ℝ) :=
  SchwartzMap.mkCLM (𝕜 := ℝ) (𝕜' := ℝ)
    (fun f x => Complex.imCLM (f x))
    (fun f g x => by simp)
    (fun a f x => by simp [RingHom.id_apply])
    (fun f => Complex.imCLM.contDiff.comp f.smooth')
    (fun ⟨k, n⟩ => ⟨{(k, n)}, 1, zero_le_one, fun f x => by
      simp only [Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul]
      calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Complex.imCLM ∘ ⇑f) x‖
            ≤ ‖x‖ ^ k * (‖Complex.imCLM‖ * ‖iteratedFDeriv ℝ n f x‖) := by
                gcongr
                exact ContinuousLinearMap.norm_iteratedFDeriv_comp_left
                  (L := Complex.imCLM)
                  (f := ⇑f) (x := x)
                  ((f.smooth n).contDiffAt)
                  (n := n) le_rfl
        _ = ‖Complex.imCLM‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by ring
        _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by simp
        _ ≤ SchwartzMap.seminorm ℝ k n f := SchwartzMap.le_seminorm ℝ k n f x⟩)

@[simp] theorem imagPartCLM_apply (f : 𝓢(D, ℂ)) (x : D) :
    imagPartCLM f x = (f x).im := rfl

/-- Real-valued Schwartz functions lift to complex-valued ones. -/
def ofRealCLM : 𝓢(D, ℝ) →L[ℝ] 𝓢(D, ℂ) :=
  SchwartzMap.mkCLM (𝕜 := ℝ) (𝕜' := ℝ)
    (fun f x => Complex.ofRealCLM (f x))
    (fun f g x => by simp [map_add])
    (fun a f x => by
      show Complex.ofRealCLM ((a • f) x) = a • Complex.ofRealCLM (f x)
      simp only [SchwartzMap.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply,
        Complex.ofReal_mul, Complex.real_smul])
    (fun f => Complex.ofRealCLM.contDiff.comp f.smooth')
    (fun ⟨k, n⟩ => ⟨{(k, n)}, 1, zero_le_one, fun f x => by
      simp only [Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul]
      have hEq : (fun x => Complex.ofRealCLM (f x)) = Complex.ofRealLI ∘ ⇑f := rfl
      rw [hEq, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
        ((f.smooth n).contDiffAt) le_rfl]
      exact SchwartzMap.le_seminorm ℝ k n f x⟩)

@[simp] theorem ofRealCLM_apply (f : 𝓢(D, ℝ)) (x : D) :
    ofRealCLM f x = (f x : ℂ) := rfl

/-- The real and imaginary parts give a continuous linear map
`𝓢(D, ℂ) → 𝓢(D, ℝ) × 𝓢(D, ℝ)`. -/
def complexToRealProdCLM : 𝓢(D, ℂ) →L[ℝ] 𝓢(D, ℝ) × 𝓢(D, ℝ) where
  toLinearMap :=
    { toFun := fun f => (realPartCLM f, imagPartCLM f)
      map_add' := by
        intro f g
        ext <;> simp [realPartCLM, imagPartCLM]
      map_smul' := by
        intro a f
        ext <;> simp [realPartCLM, imagPartCLM] }
  cont := realPartCLM.continuous.prodMk imagPartCLM.continuous

/-- Recombination of real and imaginary Schwartz parts into a complex Schwartz function. -/
def realProdToComplexCLM : (𝓢(D, ℝ) × 𝓢(D, ℝ)) →L[ℝ] 𝓢(D, ℂ) where
  toLinearMap :=
    { toFun := fun fg => ofRealCLM fg.1 + (Complex.I : ℂ) • ofRealCLM fg.2
      map_add' := by
        intro f g
        ext x
        simp [add_assoc, add_left_comm, smul_add]
      map_smul' := by
        intro a f
        ext x
        simp only [RingHom.id_apply, SchwartzMap.smul_apply, Prod.smul_fst, Prod.smul_snd,
          SchwartzMap.add_apply, smul_add, ofRealCLM_apply]
        -- Goal: ↑(a • f.1 x) + I • ↑(a • f.2 x) = a • ↑(f.1 x) + a • (I • ↑(f.2 x))
        have h1 : (↑(a • f.1 x) : ℂ) = a • (↑(f.1 x) : ℂ) := by
          simp [smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
        have h2 : (↑(a • f.2 x) : ℂ) = a • (↑(f.2 x) : ℂ) := by
          simp [smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
        rw [h1, h2]
        congr 1
        exact (smul_comm a Complex.I (↑(f.2 x) : ℂ)).symm }
  cont := (ofRealCLM.continuous.comp continuous_fst).add
    (((Complex.I : ℂ) • ofRealCLM).continuous.comp continuous_snd)

/-- Complex-valued Schwartz space is the product of two real-valued Schwartz spaces
as a real locally convex space. -/
def complexDecomposeCLE : 𝓢(D, ℂ) ≃L[ℝ] (𝓢(D, ℝ) × 𝓢(D, ℝ)) :=
  ContinuousLinearEquiv.equivOfInverse
    complexToRealProdCLM realProdToComplexCLM
    (by
      intro f
      ext x
      simpa [complexToRealProdCLM, realProdToComplexCLM, mul_comm] using
        (Complex.re_add_im (f x)))
    (by
      intro fg
      apply Prod.ext
      · ext x
        simp [complexToRealProdCLM, realProdToComplexCLM]
      · ext x
        simp [complexToRealProdCLM, realProdToComplexCLM])

@[simp] theorem complexDecomposeCLE_fst_apply (f : 𝓢(D, ℂ)) (x : D) :
    (complexDecomposeCLE f).1 x = (f x).re := rfl

@[simp] theorem complexDecomposeCLE_snd_apply (f : 𝓢(D, ℂ)) (x : D) :
    (complexDecomposeCLE f).2 x = (f x).im := rfl

@[simp] theorem complexDecomposeCLE_symm_apply (fg : 𝓢(D, ℝ) × 𝓢(D, ℝ)) (x : D) :
    (complexDecomposeCLE.symm fg) x = (fg.1 x : ℂ) + (fg.2 x : ℂ) * Complex.I := by
  simp [complexDecomposeCLE, realProdToComplexCLM, mul_comm]

/-- If the real-valued Schwartz space is nuclear, then the complex-valued Schwartz space
is nuclear as a real locally convex space. -/
theorem nuclearSpaceComplex [NuclearSpace (𝓢(D, ℝ))] :
    NuclearSpace (𝓢(D, ℂ)) := by
  let ePi : ((i : Fin 2) → 𝓢(D, ℝ)) ≃L[ℝ] (𝓢(D, ℝ) × 𝓢(D, ℝ)) :=
    ContinuousLinearEquiv.piFinTwo ℝ (fun _ : Fin 2 => 𝓢(D, ℝ))
  have hPi : NuclearSpace ((i : Fin 2) → 𝓢(D, ℝ)) :=
    NuclearSpace.product_nuclear (Fin 2) (fun _ : Fin 2 => 𝓢(D, ℝ))
  have hProd : NuclearSpace (𝓢(D, ℝ) × 𝓢(D, ℝ)) := by
    letI := hPi
    exact NuclearSpace.of_continuousLinearEquiv ePi.symm
  letI := hProd
  exact NuclearSpace.of_continuousLinearEquiv (complexDecomposeCLE (D := D))

/-- The complex Schwartz space `S(ℝⁿ, ℂ)` is nuclear as a real locally convex space. -/
theorem instNuclearSpaceComplex (n : ℕ) :
    NuclearSpace (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) := by
  letI : NuclearSpace (𝓢(EuclideanSpace ℝ (Fin n), ℝ)) := SchwartzMap.instNuclearSpace n
  exact nuclearSpaceComplex

end SchwartzMap
