/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Complex-Valued Schwartz Functions as Real Pairs

This file gives the pure-SCV real/imaginary decomposition of complex-valued
Schwartz functions.  It intentionally uses `SCV.*` names rather than the
Wightman `SchwartzMap.*` names, so this infrastructure can be imported on the
theorem-2 SCV route without depending on or colliding with Wightman nuclear
space files.
-/

open scoped SchwartzMap

noncomputable section

namespace SCV

open SchwartzMap

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Real part as a continuous real-linear map on Schwartz spaces. -/
def schwartzRealPartCLM : 𝓢(D, ℂ) →L[ℝ] 𝓢(D, ℝ) :=
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

@[simp] theorem schwartzRealPartCLM_apply (f : 𝓢(D, ℂ)) (x : D) :
    schwartzRealPartCLM f x = (f x).re := rfl

/-- Imaginary part as a continuous real-linear map on Schwartz spaces. -/
def schwartzImagPartCLM : 𝓢(D, ℂ) →L[ℝ] 𝓢(D, ℝ) :=
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

@[simp] theorem schwartzImagPartCLM_apply (f : 𝓢(D, ℂ)) (x : D) :
    schwartzImagPartCLM f x = (f x).im := rfl

/-- Real-valued Schwartz functions embedded as complex-valued Schwartz functions. -/
def schwartzOfRealCLM : 𝓢(D, ℝ) →L[ℝ] 𝓢(D, ℂ) :=
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

@[simp] theorem schwartzOfRealCLM_apply (f : 𝓢(D, ℝ)) (x : D) :
    schwartzOfRealCLM f x = (f x : ℂ) := rfl

/-- The real and imaginary parts as a continuous real-linear product map. -/
def complexSchwartzToRealProdCLM :
    𝓢(D, ℂ) →L[ℝ] 𝓢(D, ℝ) × 𝓢(D, ℝ) where
  toLinearMap :=
    { toFun := fun f => (schwartzRealPartCLM f, schwartzImagPartCLM f)
      map_add' := by
        intro f g
        ext <;> simp [schwartzRealPartCLM, schwartzImagPartCLM]
      map_smul' := by
        intro a f
        ext <;> simp [schwartzRealPartCLM, schwartzImagPartCLM] }
  cont := schwartzRealPartCLM.continuous.prodMk schwartzImagPartCLM.continuous

/-- Recombination of real and imaginary Schwartz parts. -/
def realProdToComplexSchwartzCLM :
    (𝓢(D, ℝ) × 𝓢(D, ℝ)) →L[ℝ] 𝓢(D, ℂ) where
  toLinearMap :=
    { toFun := fun fg => schwartzOfRealCLM fg.1 + (Complex.I : ℂ) • schwartzOfRealCLM fg.2
      map_add' := by
        intro f g
        ext x
        simp [add_assoc, add_left_comm, smul_add]
      map_smul' := by
        intro a f
        ext x
        simp only [RingHom.id_apply, SchwartzMap.smul_apply, Prod.smul_fst, Prod.smul_snd,
          SchwartzMap.add_apply, smul_add, schwartzOfRealCLM_apply]
        have h1 : (↑(a • f.1 x) : ℂ) = a • (↑(f.1 x) : ℂ) := by
          simp [smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
        have h2 : (↑(a • f.2 x) : ℂ) = a • (↑(f.2 x) : ℂ) := by
          simp [smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
        rw [h1, h2]
        congr 1
        exact (smul_comm a Complex.I (↑(f.2 x) : ℂ)).symm }
  cont := (schwartzOfRealCLM.continuous.comp continuous_fst).add
    (((Complex.I : ℂ) • schwartzOfRealCLM).continuous.comp continuous_snd)

/-- Complex-valued Schwartz functions are real-linearly equivalent to pairs of
real-valued Schwartz functions. -/
def complexSchwartzDecomposeCLE :
    𝓢(D, ℂ) ≃L[ℝ] (𝓢(D, ℝ) × 𝓢(D, ℝ)) :=
  ContinuousLinearEquiv.equivOfInverse
    complexSchwartzToRealProdCLM realProdToComplexSchwartzCLM
    (by
      intro f
      ext x
      simpa [complexSchwartzToRealProdCLM, realProdToComplexSchwartzCLM, mul_comm] using
        (Complex.re_add_im (f x)))
    (by
      intro fg
      apply Prod.ext
      · ext x
        simp [complexSchwartzToRealProdCLM, realProdToComplexSchwartzCLM]
      · ext x
        simp [complexSchwartzToRealProdCLM, realProdToComplexSchwartzCLM])

@[simp] theorem complexSchwartzDecomposeCLE_fst_apply (f : 𝓢(D, ℂ)) (x : D) :
    (complexSchwartzDecomposeCLE f).1 x = (f x).re := rfl

@[simp] theorem complexSchwartzDecomposeCLE_snd_apply (f : 𝓢(D, ℂ)) (x : D) :
    (complexSchwartzDecomposeCLE f).2 x = (f x).im := rfl

@[simp] theorem complexSchwartzDecomposeCLE_symm_apply
    (fg : 𝓢(D, ℝ) × 𝓢(D, ℝ)) (x : D) :
    (complexSchwartzDecomposeCLE.symm fg) x =
      (fg.1 x : ℂ) + (fg.2 x : ℂ) * Complex.I := by
  simp [complexSchwartzDecomposeCLE, realProdToComplexSchwartzCLM, mul_comm]

end SCV
