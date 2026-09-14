/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Topology.Algebra.Module.Equiv
import Init
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import SchwartzNuclear
import GaussianField









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

end SchwartzMap
