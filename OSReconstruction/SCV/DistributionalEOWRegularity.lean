/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWDbar
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Local Regularity Calculus for Distributional EOW

This file begins the pure-SCV regularity layer used by the local
distributional edge-of-the-wedge route.  It contains the checked
test-function `∂/∂z_j` operator, support preservation, and commutation of the
real coordinate derivatives, plus the coordinate-Laplacian identity that turns
distributional `∂bar`-holomorphy into distributional harmonicity.  The
localized Weyl/parametrix theorem remains the next analytic layer.
-/

noncomputable section

open Complex MeasureTheory
open LineDeriv

namespace SCV

variable {m : ℕ}

/-- The test-function Wirtinger operator `∂/∂z_j` on complex-chart Schwartz
space. -/
def dzSchwartzCLM {m : ℕ} (j : Fin m) :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ :=
  (1 / 2 : ℂ) •
    (directionalDerivSchwartzCLM (complexRealDir j) -
      Complex.I • directionalDerivSchwartzCLM (complexImagDir j))

/-- The test-function `∂/∂z_j` operator does not enlarge topological
support. -/
theorem dzSchwartzCLM_tsupport_subset
    (j : Fin m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    tsupport
      ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) ⊆
    tsupport (φ : ComplexChartSpace m → ℂ) := by
  let X := ComplexChartSpace m
  let dre : SchwartzMap X ℂ := directionalDerivSchwartzCLM (complexRealDir j) φ
  let dim : SchwartzMap X ℂ := directionalDerivSchwartzCLM (complexImagDir j) φ
  let idim : SchwartzMap X ℂ := Complex.I • dim
  let nidim : SchwartzMap X ℂ := -idim
  have hdre : tsupport (dre : X → ℂ) ⊆ tsupport (φ : X → ℂ) := by
    simpa [X, dre] using directionalDerivSchwartzCLM_tsupport_subset
      (m := m) (v := complexRealDir j) φ
  have hdim : tsupport (dim : X → ℂ) ⊆ tsupport (φ : X → ℂ) := by
    simpa [X, dim] using directionalDerivSchwartzCLM_tsupport_subset
      (m := m) (v := complexImagDir j) φ
  have hleft :
      tsupport (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (φ : X → ℂ) := by
    exact
      (tsupport_smul_subset_right (fun _ : X => (1 / 2 : ℂ))
        (dre : X → ℂ)).trans hdre
  have hI :
      tsupport ((idim : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (dim : X → ℂ) := by
    simpa using
      tsupport_smul_subset_right (fun _ : X => Complex.I) (dim : X → ℂ)
  have hnI :
      tsupport ((nidim : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (dim : X → ℂ) := by
    rw [show ((nidim : SchwartzMap X ℂ) : X → ℂ) =
        -((idim : SchwartzMap X ℂ) : X → ℂ) by rfl]
    rw [tsupport_neg]
    exact hI
  have hright :
      tsupport
          (((1 / 2 : ℂ) • nidim : SchwartzMap X ℂ) :
            X → ℂ) ⊆
        tsupport (φ : X → ℂ) := by
    exact
      (tsupport_smul_subset_right (fun _ : X => (1 / 2 : ℂ))
        ((nidim : SchwartzMap X ℂ) : X → ℂ)).trans
          (hnI.trans hdim)
  have hadd :
      tsupport
          ((((1 / 2 : ℂ) • dre +
            (1 / 2 : ℂ) • nidim) : SchwartzMap X ℂ) :
              X → ℂ) ⊆
        tsupport (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ) ∪
          tsupport
            (((1 / 2 : ℂ) • nidim : SchwartzMap X ℂ) :
              X → ℂ) := by
    simpa using
      tsupport_add (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ)
        (((1 / 2 : ℂ) • nidim : SchwartzMap X ℂ) : X → ℂ)
  intro x hx
  have hx' :
      x ∈
        tsupport
          ((((1 / 2 : ℂ) • dre +
            (1 / 2 : ℂ) • nidim) : SchwartzMap X ℂ) :
              X → ℂ) := by
    simpa [dzSchwartzCLM, X, dre, dim, idim, nidim, sub_eq_add_neg,
      smul_add] using hx
  rcases hadd hx' with hxleft | hxright
  · exact hleft hxleft
  · exact hright hxright

/-- The `∂/∂z_j` test operator preserves compact support inside the same open
chart set. -/
theorem SupportsInOpen.dz
    {U : Set (ComplexChartSpace m)}
    {φ : SchwartzMap (ComplexChartSpace m) ℂ}
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (j : Fin m) :
    SupportsInOpen
      ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) U := by
  constructor
  · exact hφ.1.mono'
      ((subset_tsupport _).trans (dzSchwartzCLM_tsupport_subset j φ))
  · exact (dzSchwartzCLM_tsupport_subset j φ).trans hφ.2

/-- Directional derivatives of complex-chart Schwartz functions commute. -/
theorem lineDerivOp_comm_complex {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (v w : ComplexChartSpace m) :
    ∂_{v} ((∂_{w} φ : SchwartzMap (ComplexChartSpace m) ℂ)) =
      ∂_{w} ((∂_{v} φ : SchwartzMap (ComplexChartSpace m) ℂ)) := by
  ext x
  have hsym :=
    (φ.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} φ : SchwartzMap (ComplexChartSpace m) ℂ))) x =
        (∂^{![v, w]} φ) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2
        (φ : ComplexChartSpace m → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := φ) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2
        (φ : ComplexChartSpace m → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} φ) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := φ) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} φ : SchwartzMap (ComplexChartSpace m) ℂ))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

/-- The SCV-owned directional derivative operator commutes in any two real
directions. -/
theorem directionalDerivSchwartzCLM_comm
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (v w : ComplexChartSpace m) :
    directionalDerivSchwartzCLM v (directionalDerivSchwartzCLM w φ) =
      directionalDerivSchwartzCLM w (directionalDerivSchwartzCLM v φ) := by
  simpa [directionalDerivSchwartzCLM] using
    lineDerivOp_comm_complex (m := m) φ v w

/-- The test-function `∂bar_j` and `∂z_j` operators commute. -/
theorem dbar_dzSchwartzCLM_comm
    (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    dbarSchwartzCLM j (dzSchwartzCLM j φ) =
      dzSchwartzCLM j (dbarSchwartzCLM j φ) := by
  let X := ComplexChartSpace m
  let R : SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
    directionalDerivSchwartzCLM (complexRealDir j)
  let Y : SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
    directionalDerivSchwartzCLM (complexImagDir j)
  have hRY : R (Y φ) = Y (R φ) := by
    simpa [X, R, Y] using directionalDerivSchwartzCLM_comm
      (m := m) φ (complexRealDir j) (complexImagDir j)
  ext z
  change (((1 / 2 : ℂ) • (R + Complex.I • Y))
      (((1 / 2 : ℂ) • (R - Complex.I • Y)) φ)) z =
    (((1 / 2 : ℂ) • (R - Complex.I • Y))
      (((1 / 2 : ℂ) • (R + Complex.I • Y)) φ)) z
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, map_smul, map_add, map_sub]
  rw [hRY]
  simp only [SchwartzMap.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.sub_apply, smul_eq_mul]
  ring_nf

/-- The coordinate real Laplacian on the complex chart:
`∑_j (D_{x_j}^2 + D_{y_j}^2)`.  This avoids imposing a fake inner-product
instance on the repo's plain Pi chart type; the later Weyl theorem will bridge
this coordinate operator to the standard Euclidean Laplacian by a linear
equivalence. -/
def complexChartLaplacianSchwartzCLM {m : ℕ} :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ :=
  ∑ j : Fin m,
    ((directionalDerivSchwartzCLM (complexRealDir j)).comp
        (directionalDerivSchwartzCLM (complexRealDir j)) +
      (directionalDerivSchwartzCLM (complexImagDir j)).comp
        (directionalDerivSchwartzCLM (complexImagDir j)))

/-- The coordinate Laplacian applied to a test is the finite sum of real and
imaginary coordinate second derivatives. -/
theorem complexChartLaplacianSchwartzCLM_apply
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    complexChartLaplacianSchwartzCLM φ =
      ∑ j : Fin m,
        (directionalDerivSchwartzCLM (complexRealDir j)
            (directionalDerivSchwartzCLM (complexRealDir j) φ) +
          directionalDerivSchwartzCLM (complexImagDir j)
            (directionalDerivSchwartzCLM (complexImagDir j) φ)) := by
  simp [complexChartLaplacianSchwartzCLM]

/-- In one complex coordinate, `4 ∂bar_j ∂z_j` is the real two-coordinate
second-derivative sum on tests. -/
theorem four_dbar_dzSchwartzCLM_eq_real_imag_second
    (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    (4 : ℂ) • dbarSchwartzCLM j (dzSchwartzCLM j φ) =
      directionalDerivSchwartzCLM (complexRealDir j)
          (directionalDerivSchwartzCLM (complexRealDir j) φ) +
        directionalDerivSchwartzCLM (complexImagDir j)
          (directionalDerivSchwartzCLM (complexImagDir j) φ) := by
  let X := ComplexChartSpace m
  let R : SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
    directionalDerivSchwartzCLM (complexRealDir j)
  let Y : SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
    directionalDerivSchwartzCLM (complexImagDir j)
  have hRY : R (Y φ) = Y (R φ) := by
    simpa [X, R, Y] using directionalDerivSchwartzCLM_comm
      (m := m) φ (complexRealDir j) (complexImagDir j)
  ext z
  change (((4 : ℂ) • (((1 / 2 : ℂ) • (R + Complex.I • Y))
      (((1 / 2 : ℂ) • (R - Complex.I • Y)) φ))) : SchwartzMap X ℂ) z =
    (R (R φ) + Y (Y φ)) z
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, map_smul, map_sub]
  rw [hRY]
  simp only [SchwartzMap.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.sub_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

/-- The coordinate real Laplacian is `4 ∑_j ∂bar_j ∂z_j` on complex-chart
Schwartz tests. -/
theorem complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    complexChartLaplacianSchwartzCLM φ =
      (4 : ℂ) •
        ∑ j : Fin m, dbarSchwartzCLM j (dzSchwartzCLM j φ) := by
  rw [complexChartLaplacianSchwartzCLM_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact (four_dbar_dzSchwartzCLM_eq_real_imag_second j φ).symm

/-- Distributional `∂bar`-holomorphy implies local harmonicity in the
distributional real-Laplacian sense. -/
theorem local_laplacian_zero_of_distributionalHolomorphic
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    {U0 : Set (ComplexChartSpace m)}
    (hCR : IsDistributionalHolomorphicOn Hdist U0)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0) :
    Hdist (complexChartLaplacianSchwartzCLM φ) = 0 := by
  rw [complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz]
  simp only [map_smul, map_sum]
  have hsum :
      ∑ j : Fin m, Hdist (dbarSchwartzCLM j (dzSchwartzCLM j φ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    exact hCR j (dzSchwartzCLM j φ) (hφ.dz j)
  simp [hsum]

/-- The pointwise `∂/∂bar z_j` expression for a real-differentiable function
on the complex chart. -/
def pointwiseDbar (j : Fin m) (H : ComplexChartSpace m → ℂ)
    (z : ComplexChartSpace m) : ℂ :=
  (1 / 2 : ℂ) *
    (fderiv ℝ H z (complexRealDir j) +
      Complex.I * fderiv ℝ H z (complexImagDir j))

/-- On a global Schwartz function, the test-function `∂bar` operator agrees
pointwise with the corresponding `fderiv` expression. -/
theorem dbarSchwartzCLM_apply_eq_pointwiseDbar
    (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (z : ComplexChartSpace m) :
    (dbarSchwartzCLM j φ) z =
      pointwiseDbar j (φ : ComplexChartSpace m → ℂ) z := by
  simp [pointwiseDbar, dbarSchwartzCLM, directionalDerivSchwartzCLM,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  ring

/-- Real-linear Euclidean coordinates for the complex chart, using the checked
real/imaginary flattening in `DistributionalEOWKernel`. -/
noncomputable def complexChartEuclideanCLE (m : ℕ) :
    ComplexChartSpace m ≃L[ℝ] EuclideanSpace ℝ (Fin (m * 2)) :=
  (complexChartRealFlattenCLE m).trans
    (EuclideanSpace.equiv (Fin (m * 2)) ℝ).symm

/-- Schwartz-space transport along `complexChartEuclideanCLE`. -/
noncomputable def complexChartEuclideanSchwartzCLE (m : ℕ) :
    SchwartzMap (ComplexChartSpace m) ℂ ≃L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ := by
  let e := complexChartEuclideanCLE m
  let toFwd :
      SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
        SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let toInv :
      SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ →L[ℂ]
        SchwartzMap (ComplexChartSpace m) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  exact
    { toLinearEquiv :=
        { toFun := toFwd
          map_add' := toFwd.map_add
          map_smul' := toFwd.map_smul
          invFun := toInv
          left_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e]
          right_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e] }
      continuous_toFun := toFwd.continuous
      continuous_invFun := toInv.continuous }

@[simp]
theorem complexChartEuclideanSchwartzCLE_apply
    (m : ℕ) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (x : EuclideanSpace ℝ (Fin (m * 2))) :
    complexChartEuclideanSchwartzCLE m φ x =
      φ ((complexChartEuclideanCLE m).symm x) := by
  simp [complexChartEuclideanSchwartzCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

@[simp]
theorem complexChartEuclideanSchwartzCLE_symm_apply
    (m : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ)
    (z : ComplexChartSpace m) :
    (complexChartEuclideanSchwartzCLE m).symm φ z =
      φ (complexChartEuclideanCLE m z) := by
  change
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (complexChartEuclideanCLE m) φ) z =
    φ (complexChartEuclideanCLE m z)
  rfl

/-- The real coordinate direction maps to the corresponding Euclidean basis
vector under the checked real/imaginary flattening. -/
theorem complexChartEuclideanCLE_realDir {m : ℕ} (j : Fin m) :
    complexChartEuclideanCLE m (complexRealDir j) =
      EuclideanSpace.single (finProdFinEquiv (j, (0 : Fin 2))) (1 : ℝ) := by
  ext k
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective k
  rcases p with ⟨i, b⟩
  fin_cases b
  · by_cases hij : i = j
    · subst hij
      simp [complexChartEuclideanCLE, complexRealDir]
    · simp [complexChartEuclideanCLE, complexRealDir, hij]
  · by_cases hij : i = j
    · subst hij
      simp [complexChartEuclideanCLE, complexRealDir]
    · simp [complexChartEuclideanCLE, complexRealDir, hij]

/-- The imaginary coordinate direction maps to the corresponding Euclidean
basis vector under the checked real/imaginary flattening. -/
theorem complexChartEuclideanCLE_imagDir {m : ℕ} (j : Fin m) :
    complexChartEuclideanCLE m (complexImagDir j) =
      EuclideanSpace.single (finProdFinEquiv (j, (1 : Fin 2))) (1 : ℝ) := by
  ext k
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective k
  rcases p with ⟨i, b⟩
  fin_cases b
  · by_cases hij : i = j
    · subst hij
      simp [complexChartEuclideanCLE, complexImagDir]
    · simp [complexChartEuclideanCLE, complexImagDir, hij]
  · by_cases hij : i = j
    · subst hij
      simp [complexChartEuclideanCLE, complexImagDir]
    · simp [complexChartEuclideanCLE, complexImagDir, hij]

/-- First real-coordinate derivatives commute with Euclidean chart transport. -/
theorem complexChartEuclidean_lineDeriv_realDir {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
    ∂_{EuclideanSpace.single (finProdFinEquiv (j, (0 : Fin 2))) (1 : ℝ)}
        (complexChartEuclideanSchwartzCLE m φ) =
      complexChartEuclideanSchwartzCLE m
        (directionalDerivSchwartzCLM (complexRealDir j) φ) := by
  simpa [complexChartEuclideanSchwartzCLE, directionalDerivSchwartzCLM,
    ← complexChartEuclideanCLE_realDir (m := m) j] using
    (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv (𝕜 := ℂ)
      (m := EuclideanSpace.single (finProdFinEquiv (j, (0 : Fin 2))) (1 : ℝ))
      (g := (complexChartEuclideanCLE m).symm)
      (f := φ))

/-- First imaginary-coordinate derivatives commute with Euclidean chart
transport. -/
theorem complexChartEuclidean_lineDeriv_imagDir {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
    ∂_{EuclideanSpace.single (finProdFinEquiv (j, (1 : Fin 2))) (1 : ℝ)}
        (complexChartEuclideanSchwartzCLE m φ) =
      complexChartEuclideanSchwartzCLE m
        (directionalDerivSchwartzCLM (complexImagDir j) φ) := by
  simpa [complexChartEuclideanSchwartzCLE, directionalDerivSchwartzCLM,
    ← complexChartEuclideanCLE_imagDir (m := m) j] using
    (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv (𝕜 := ℂ)
      (m := EuclideanSpace.single (finProdFinEquiv (j, (1 : Fin 2))) (1 : ℝ))
      (g := (complexChartEuclideanCLE m).symm)
      (f := φ))

/-- Second real-coordinate derivatives commute with Euclidean chart transport. -/
theorem complexChartEuclidean_secondLineDeriv_realDir {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
    ∂_{EuclideanSpace.single (finProdFinEquiv (j, (0 : Fin 2))) (1 : ℝ)}
        (∂_{EuclideanSpace.single (finProdFinEquiv (j, (0 : Fin 2))) (1 : ℝ)}
          (complexChartEuclideanSchwartzCLE m φ)) =
      complexChartEuclideanSchwartzCLE m
        (directionalDerivSchwartzCLM (complexRealDir j)
          (directionalDerivSchwartzCLM (complexRealDir j) φ)) := by
  rw [complexChartEuclidean_lineDeriv_realDir φ j]
  rw [complexChartEuclidean_lineDeriv_realDir
    (directionalDerivSchwartzCLM (complexRealDir j) φ) j]

/-- Second imaginary-coordinate derivatives commute with Euclidean chart
transport. -/
theorem complexChartEuclidean_secondLineDeriv_imagDir {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
    ∂_{EuclideanSpace.single (finProdFinEquiv (j, (1 : Fin 2))) (1 : ℝ)}
        (∂_{EuclideanSpace.single (finProdFinEquiv (j, (1 : Fin 2))) (1 : ℝ)}
          (complexChartEuclideanSchwartzCLE m φ)) =
      complexChartEuclideanSchwartzCLE m
        (directionalDerivSchwartzCLM (complexImagDir j)
          (directionalDerivSchwartzCLM (complexImagDir j) φ)) := by
  rw [complexChartEuclidean_lineDeriv_imagDir φ j]
  rw [complexChartEuclidean_lineDeriv_imagDir
    (directionalDerivSchwartzCLM (complexImagDir j) φ) j]

/-- The coordinate real Laplacian on a Euclidean chart, written with the
canonical coordinate basis. -/
noncomputable def euclideanCoordinateLaplacianSchwartzCLM
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
  ∑ k : ι,
    (LineDeriv.lineDerivOpCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
        (EuclideanSpace.single k (1 : ℝ))).comp
      (LineDeriv.lineDerivOpCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
        (EuclideanSpace.single k (1 : ℝ)))

/-- The explicit coordinate Laplacian is Mathlib's Euclidean Schwartz
Laplacian. -/
theorem euclideanCoordinateLaplacianSchwartzCLM_eq_laplacianCLM
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    euclideanCoordinateLaplacianSchwartzCLM φ =
      LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
        (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ := by
  rw [SchwartzMap.laplacianCLM_eq (𝕜 := ℝ)]
  calc
    euclideanCoordinateLaplacianSchwartzCLM φ =
        ∑ k : ι,
          ∂_{EuclideanSpace.single k (1 : ℝ)}
            (∂_{EuclideanSpace.single k (1 : ℝ)} φ) := by
      simp [euclideanCoordinateLaplacianSchwartzCLM]
    _ = Laplacian.laplacian φ := by
      simpa using
        (SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun ι ℝ) φ).symm

/-- Transporting the checked complex-chart coordinate Laplacian gives the
standard Euclidean Laplacian on the flattened chart. -/
theorem complexChartLaplacianSchwartzCLM_transport {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    complexChartEuclideanSchwartzCLE m
        (complexChartLaplacianSchwartzCLM φ) =
      LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ (Fin (m * 2)))
        (SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ)
        (complexChartEuclideanSchwartzCLE m φ) := by
  rw [← euclideanCoordinateLaplacianSchwartzCLM_eq_laplacianCLM]
  simp [euclideanCoordinateLaplacianSchwartzCLM,
    complexChartLaplacianSchwartzCLM_apply, map_sum, map_add,
    ← complexChartEuclidean_secondLineDeriv_realDir,
    ← complexChartEuclidean_secondLineDeriv_imagDir]
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

/-- Transport a complex-chart distribution to the Euclidean flattened chart. -/
noncomputable def transportedDistributionToEuclidean {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ →L[ℂ] ℂ :=
  T.comp
    ((complexChartEuclideanSchwartzCLE m).symm :
      SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ →L[ℂ]
        SchwartzMap (ComplexChartSpace m) ℂ)

@[simp]
theorem transportedDistributionToEuclidean_apply {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) :
    transportedDistributionToEuclidean T φ =
      T ((complexChartEuclideanSchwartzCLE m).symm φ) := rfl

/-- Compact support inside a transported Euclidean open set pulls back to
compact support inside the original complex chart open set. -/
theorem supportsInOpen_transport_to_euclidean {m : ℕ}
    {φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ}
    {U0 : Set (ComplexChartSpace m)}
    (hφ : SupportsInOpen
      (φ : EuclideanSpace ℝ (Fin (m * 2)) → ℂ)
      ((complexChartEuclideanCLE m) '' U0)) :
    SupportsInOpen
      (((complexChartEuclideanSchwartzCLE m).symm φ :
          SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) U0 := by
  let e := complexChartEuclideanCLE m
  constructor
  · change HasCompactSupport fun z : ComplexChartSpace m => φ (e z)
    exact hφ.1.comp_homeomorph e.toHomeomorph
  · have htsupport :
        tsupport
          (((complexChartEuclideanSchwartzCLE m).symm φ :
              SchwartzMap (ComplexChartSpace m) ℂ) :
            ComplexChartSpace m → ℂ) =
          e.toHomeomorph ⁻¹'
            tsupport (φ : EuclideanSpace ℝ (Fin (m * 2)) → ℂ) := by
      simpa [e, complexChartEuclideanSchwartzCLE_symm_apply] using
        (tsupport_comp_eq_preimage
          (g := (φ : EuclideanSpace ℝ (Fin (m * 2)) → ℂ)) e.toHomeomorph)
    intro z hz
    have hez :
        e z ∈ tsupport
          (φ : EuclideanSpace ℝ (Fin (m * 2)) → ℂ) := by
      simpa [htsupport] using hz
    rcases hφ.2 hez with ⟨z', hz'U, hz'eq⟩
    exact (e.injective hz'eq).symm ▸ hz'U

/-- Compact support inside a complex chart open set pushes forward to compact
support inside the transported Euclidean open set. -/
theorem supportsInOpen_transport_from_euclidean {m : ℕ}
    {φ : SchwartzMap (ComplexChartSpace m) ℂ}
    {U0 : Set (ComplexChartSpace m)}
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0) :
    SupportsInOpen
      ((complexChartEuclideanSchwartzCLE m φ :
          SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) :
        EuclideanSpace ℝ (Fin (m * 2)) → ℂ)
      ((complexChartEuclideanCLE m) '' U0) := by
  let e := complexChartEuclideanCLE m
  constructor
  · change HasCompactSupport fun x : EuclideanSpace ℝ (Fin (m * 2)) =>
      φ (e.symm x)
    exact hφ.1.comp_homeomorph e.toHomeomorph.symm
  · have htsupport :
        tsupport
          ((complexChartEuclideanSchwartzCLE m φ :
              SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) :
            EuclideanSpace ℝ (Fin (m * 2)) → ℂ) =
          e.toHomeomorph.symm ⁻¹'
            tsupport (φ : ComplexChartSpace m → ℂ) := by
      simpa [e, complexChartEuclideanSchwartzCLE_apply] using
        (tsupport_comp_eq_preimage
          (g := (φ : ComplexChartSpace m → ℂ)) e.toHomeomorph.symm)
    intro x hx
    have hex :
        e.symm x ∈ tsupport (φ : ComplexChartSpace m → ℂ) := by
      simpa [htsupport] using hx
    exact ⟨e.symm x, hφ.2 hex, by simp [e]⟩

/-- Measurable real-coordinate flattening in the same coordinate order as
`realBlockFlattenCLE`. -/
private def realBlockFlattenMeasurableEquiv (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃ᵐ (Fin (n * d) → ℝ) :=
  (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finProdFinEquiv)

@[simp]
private theorem realBlockFlattenMeasurableEquiv_apply (n d : ℕ)
    (f : Fin n → Fin d → ℝ) (k : Fin (n * d)) :
    realBlockFlattenMeasurableEquiv n d f k =
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [realBlockFlattenMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_curry_symm, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Function.uncurry]

private theorem volume_map_curry_symm_realBlock (n d : ℕ) :
    (volume : Measure (Fin n → Fin d → ℝ)).map
      (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm =
    (volume : Measure (Fin n × Fin d → ℝ)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply
    (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have h_preimage :
      (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm ⁻¹'
        (Set.univ.pi s) =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi,
      MeasurableEquiv.coe_curry_symm, Function.uncurry]
    exact ⟨fun h i j => h (i, j), fun h ⟨i, j⟩ => h i j⟩
  rw [h_preimage, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [← Finset.prod_product', ← Finset.univ_product_univ]

private theorem realBlockFlattenMeasurableEquiv_measurePreserving (n d : ℕ) :
    MeasurePreserving (realBlockFlattenMeasurableEquiv n d) := by
  have h_uncurry :
      MeasurePreserving
        (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm
        volume volume := by
    refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.measurable, ?_⟩
    exact volume_map_curry_symm_realBlock n d
  exact (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ => ℝ) finProdFinEquiv).comp h_uncurry

/-- Measurable coordinatewise real/imaginary chart. -/
private def complexChartRealBlockMeasurableEquiv (m : ℕ) :
    ComplexChartSpace m ≃ᵐ (Fin m → Fin 2 → ℝ) :=
  MeasurableEquiv.arrowCongr' (Equiv.refl (Fin m))
    Complex.measurableEquivPi

private theorem complexChartRealBlockMeasurableEquiv_measurePreserving
    (m : ℕ) :
    MeasurePreserving (complexChartRealBlockMeasurableEquiv m) := by
  exact MeasureTheory.volume_preserving_arrowCongr'
    (Equiv.refl (Fin m)) Complex.measurableEquivPi
    Complex.volume_preserving_equiv_pi

private def complexChartRealFlattenMeasurableEquiv (m : ℕ) :
    ComplexChartSpace m ≃ᵐ (Fin (m * 2) → ℝ) :=
  (complexChartRealBlockMeasurableEquiv m).trans
    (realBlockFlattenMeasurableEquiv m 2)

private theorem complexChartRealFlattenMeasurableEquiv_measurePreserving
    (m : ℕ) :
    MeasurePreserving (complexChartRealFlattenMeasurableEquiv m) :=
  (complexChartRealBlockMeasurableEquiv_measurePreserving m).trans
    (realBlockFlattenMeasurableEquiv_measurePreserving m 2)

/-- The measurable equivalence matching `complexChartEuclideanCLE`. -/
private def complexChartEuclideanMeasurableEquiv (m : ℕ) :
    ComplexChartSpace m ≃ᵐ EuclideanSpace ℝ (Fin (m * 2)) :=
  (complexChartRealFlattenMeasurableEquiv m).trans
    (MeasurableEquiv.toLp 2 (Fin (m * 2) → ℝ))

private theorem complexChartEuclideanMeasurableEquiv_apply (m : ℕ)
    (z : ComplexChartSpace m) :
    complexChartEuclideanMeasurableEquiv m z =
      complexChartEuclideanCLE m z := by
  ext k
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective k
  rcases p with ⟨i, b⟩
  fin_cases b <;>
    simp [complexChartEuclideanMeasurableEquiv,
      complexChartRealFlattenMeasurableEquiv,
      complexChartRealBlockMeasurableEquiv,
      MeasurableEquiv.arrowCongr', Equiv.arrowCongr',
      Equiv.arrowCongr, complexChartEuclideanCLE,
      complexChartRealFlattenCLE, complexChartRealBlockCLE,
      complexToFinTwoCLE]

/-- The complex-chart Euclidean flattening preserves Lebesgue/Haar volume. -/
theorem complexChartEuclideanCLE_volumePreserving (m : ℕ) :
    MeasurePreserving (complexChartEuclideanCLE m) := by
  have hmp : MeasurePreserving (complexChartEuclideanMeasurableEquiv m) :=
    (complexChartRealFlattenMeasurableEquiv_measurePreserving m).trans
      (by simpa using (PiLp.volume_preserving_toLp (Fin (m * 2))))
  exact hmp.congr (complexChartEuclideanCLE m).continuous.measurable (by
    filter_upwards with z
    exact complexChartEuclideanMeasurableEquiv_apply m z)

/-- Change of variables along the volume-preserving complex-chart Euclidean
flattening. -/
theorem integral_comp_complexChartEuclideanCLE (m : ℕ)
    (H : EuclideanSpace ℝ (Fin (m * 2)) → ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin (m * 2)),
        H x * (complexChartEuclideanSchwartzCLE m φ) x) =
      ∫ z : ComplexChartSpace m, H (complexChartEuclideanCLE m z) * φ z := by
  simp only [complexChartEuclideanSchwartzCLE_apply]
  let e := complexChartEuclideanCLE m
  let G : EuclideanSpace ℝ (Fin (m * 2)) → ℂ :=
    fun x => H x * φ (e.symm x)
  have hmp := complexChartEuclideanCLE_volumePreserving m
  change (∫ x : EuclideanSpace ℝ (Fin (m * 2)), G x) =
    ∫ z : ComplexChartSpace m, H (e z) * φ z
  have hright :
      (fun z : ComplexChartSpace m => H (e z) * φ z) =
        fun z : ComplexChartSpace m => G (e z) := by
    ext z
    simp [G, e]
  rw [hright]
  simpa [G, e] using
    (hmp.integral_comp e.toHomeomorph.measurableEmbedding G).symm

/-- A Euclidean function represents a Euclidean-chart distribution on tests
supported in `V`. -/
def RepresentsEuclideanDistributionOn
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (H : EuclideanSpace ℝ ι → ℂ)
    (V : Set (EuclideanSpace ℝ ι)) : Prop :=
  ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
    SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) V →
      T φ = ∫ x, H x * φ x

/-- Pull a Euclidean representative back through the volume-preserving complex
chart. -/
theorem representsDistributionOnComplexDomain_of_euclidean {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    {U0 : Set (ComplexChartSpace m)}
    (HE : EuclideanSpace ℝ (Fin (m * 2)) → ℂ)
    (hHE :
      RepresentsEuclideanDistributionOn
        (transportedDistributionToEuclidean T) HE
        ((complexChartEuclideanCLE m) '' U0)) :
    RepresentsDistributionOnComplexDomain T
      (fun z => HE (complexChartEuclideanCLE m z)) U0 := by
  intro φ hφ
  have hφE := supportsInOpen_transport_from_euclidean (m := m) hφ
  have hrep := hHE (complexChartEuclideanSchwartzCLE m φ) hφE
  calc
    T φ =
        transportedDistributionToEuclidean T
          (complexChartEuclideanSchwartzCLE m φ) := by
      simp [transportedDistributionToEuclidean]
    _ = ∫ x : EuclideanSpace ℝ (Fin (m * 2)),
        HE x * (complexChartEuclideanSchwartzCLE m φ) x := hrep
    _ = ∫ z : ComplexChartSpace m,
        HE (complexChartEuclideanCLE m z) * φ z := by
      exact integral_comp_complexChartEuclideanCLE m HE φ

end SCV
