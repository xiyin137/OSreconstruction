/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWSupport

/-!
# `dbar` Integration by Parts for Schwartz Tests

This file proves the global Schwartz-Schwartz integration-by-parts identities
used by the local distributional edge-of-the-wedge regularization route.  The
local holomorphic-factor theorem is deliberately left for the next cutoff
stage.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

variable {m : ℕ}

/-- Directional integration by parts for the SCV-owned directional derivative
operator. -/
theorem integral_mul_directionalDerivSchwartzCLM_right_eq_neg_left
    (f g : SchwartzMap (ComplexChartSpace m) ℂ) (v : ComplexChartSpace m) :
    (∫ z : ComplexChartSpace m,
        f z * (directionalDerivSchwartzCLM v g) z) =
      -∫ z : ComplexChartSpace m,
        (directionalDerivSchwartzCLM v f) z * g z := by
  simpa [directionalDerivSchwartzCLM] using
    (SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
      (D := ComplexChartSpace m) (𝕜 := ℂ) f g v)

/-- Integration by parts for the test-function `∂/∂bar z_j` operator on
Schwartz functions. -/
theorem integral_mul_dbarSchwartzCLM_right_eq_neg_left
    (f g : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
    (∫ z : ComplexChartSpace m,
        f z * (dbarSchwartzCLM j g) z) =
      -∫ z : ComplexChartSpace m,
        (dbarSchwartzCLM j f) z * g z := by
  let X := ComplexChartSpace m
  let I : SchwartzMap X ℂ →L[ℂ] ℂ := SchwartzMap.integralCLM ℂ volume
  let pair :=
    SchwartzMap.pairing (D := X) (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ)
  let pairR :=
    SchwartzMap.pairing (D := X) (𝕜 := ℂ)
      ((ContinuousLinearMap.mul ℂ ℂ).flip)
  let Lf : SchwartzMap X ℂ →L[ℂ] ℂ := I.comp (pair f)
  let Rg : SchwartzMap X ℂ →L[ℂ] ℂ := I.comp (pairR g)
  have hre :=
    integral_mul_directionalDerivSchwartzCLM_right_eq_neg_left
      (m := m) f g (complexRealDir j)
  have him :=
    integral_mul_directionalDerivSchwartzCLM_right_eq_neg_left
      (m := m) f g (complexImagDir j)
  change Lf (dbarSchwartzCLM j g) = -Rg (dbarSchwartzCLM j f)
  simp only [dbarSchwartzCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, map_smul, map_add]
  rw [show Lf ((directionalDerivSchwartzCLM (complexRealDir j)) g) =
      ∫ z : ComplexChartSpace m,
        f z * (directionalDerivSchwartzCLM (complexRealDir j) g) z by rfl]
  rw [show Rg ((directionalDerivSchwartzCLM (complexRealDir j)) f) =
      ∫ z : ComplexChartSpace m,
        (directionalDerivSchwartzCLM (complexRealDir j) f) z * g z by rfl]
  rw [show Lf ((directionalDerivSchwartzCLM (complexImagDir j)) g) =
      ∫ z : ComplexChartSpace m,
        f z * (directionalDerivSchwartzCLM (complexImagDir j) g) z by rfl]
  rw [show Rg ((directionalDerivSchwartzCLM (complexImagDir j)) f) =
      ∫ z : ComplexChartSpace m,
        (directionalDerivSchwartzCLM (complexImagDir j) f) z * g z by rfl]
  rw [hre, him]
  simp [smul_eq_mul]
  ring

/-- If the left Schwartz factor is `dbar`-closed in coordinate `j`, then its
pairing with a `dbar` test derivative is zero. -/
theorem integral_mul_dbarSchwartzCLM_right_eq_zero_of_dbar_eq_zero
    (f g : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m)
    (hf : dbarSchwartzCLM j f = 0) :
    (∫ z : ComplexChartSpace m,
        f z * (dbarSchwartzCLM j g) z) = 0 := by
  rw [integral_mul_dbarSchwartzCLM_right_eq_neg_left f g j, hf]
  simp

/-- Localize a holomorphic-looking left factor to a genuine Schwartz function
before applying the checked Schwartz-Schwartz `∂bar` integration by parts.

The hypotheses are intentionally local: `G` only has to agree with `F` on the
support of `∂bar φ`, and `∂bar G` only has to vanish on the support of `φ`.
The cutoff construction that produces such a `G` from a holomorphic `F` is the
next theorem. -/
theorem integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz
    (F : ComplexChartSpace m → ℂ)
    (G φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (j : Fin m)
    (hFG : ∀ z ∈ tsupport
        ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
          ComplexChartSpace m → ℂ), F z = G z)
    (hG_dbar_zero : ∀ z ∈ tsupport (φ : ComplexChartSpace m → ℂ),
      (dbarSchwartzCLM j G) z = 0) :
    (∫ z : ComplexChartSpace m, F z * (dbarSchwartzCLM j φ) z) = 0 := by
  have hFG_all : ∀ z : ComplexChartSpace m,
      F z * (dbarSchwartzCLM j φ) z =
        G z * (dbarSchwartzCLM j φ) z := by
    intro z
    by_cases hz : z ∈ tsupport
        ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
          ComplexChartSpace m → ℂ)
    · rw [hFG z hz]
    · have hzero : (dbarSchwartzCLM j φ) z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [hzero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hFG_all)]
  rw [integral_mul_dbarSchwartzCLM_right_eq_neg_left G φ j]
  have hzero_all : ∀ z : ComplexChartSpace m,
      (dbarSchwartzCLM j G) z * φ z = 0 := by
    intro z
    by_cases hz : z ∈ tsupport (φ : ComplexChartSpace m → ℂ)
    · simp [hG_dbar_zero z hz]
    · have hφzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hφzero]
  have hint_zero :
      (∫ z : ComplexChartSpace m, (dbarSchwartzCLM j G) z * φ z) = 0 := by
    simp [hzero_all]
  rw [hint_zero]
  simp

end SCV
