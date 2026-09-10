/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.WickRotationBridge
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import Init
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
























noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal
open BigOperators Finset

variable {d : ℕ} [NeZero d]
/- Phase 3: analytic continuation from Euclidean to Minkowski.

    The definition below is a legacy repository-local coordinate domain.  It
    should not be identified with the Chapter V domains `C_N^k` of OS II.
    The latter continue the `k` time-gap variables while the spatial variables
    remain real distribution parameters.  By contrast, every successor region
    below is open in all complex spacetime coordinates; unconstrained spatial
    coordinates are therefore required to be entire variables.

    In particular, `AnalyticContinuationRegion d k 1` is strictly stronger
    than the OS-II Chapter V endpoint.  The active reconstruction route uses
    `OSIITimeContinuationStage` followed by a tempered boundary and
    Fourier-Laplace continuation, rather than trying to construct an entire
    complex-spatial kernel on this region. -/

/-- Legacy coordinatewise continuation region used by the older scalar-kernel
    assembly.

    C_k^(0) = {ξ ∈ ℝ^k : Im = 0, ξᵢ₀ > 0} (positive real Euclidean domain)
    C_k^(r+1) = {z ∈ ℂ^{k(d+1)} : Im(z_i,μ - z_{i-1,μ}) > 0 for all i, μ ≤ r}
      (open forward tube in the first r+1 spacetime directions; no constraint on μ > r).

    **Key property**: For r ≥ 1, C_k^(r) is an OPEN subset of ℂ^{k(d+1)}
    (strict positivity of imaginary parts ⟹ open). This ensures `DifferentiableOn ℂ`
    on C_k^(r) is genuine holomorphicity, not a vacuous condition.

    **Note**: C_k^(d+1) is the tube over a positive orthant in difference
    coordinates, not yet the Wightman forward tube. The active reconstruction
    chain must not infer this domain from the OS-II time-parametric theorem.

    The regions are monotone in the reverse direction for `r ≥ 1`:
      C_k^(r+1) ⊆ C_k^(r),
    since each step adds one more imaginary-positivity constraint. Also
    `C_k^(0)` is disjoint from `C_k^(r)` for r ≥ 1 (`C_k^(0)` has Im = 0,
    while `C_k^(r)` requires Im > 0 in at least one direction). -/
def AnalyticContinuationRegion (d k r : ℕ) [NeZero d] :
    Set (Fin k → Fin (d + 1) → ℂ) :=
  match r with
  | 0 => -- Base: positive Euclidean domain (all Im = 0, Euclidean times positive)
    { z | (∀ i : Fin k, ∀ μ : Fin (d + 1), (z i μ).im = 0) ∧
          (∀ i : Fin k, (z i 0).re > 0) }
  | r + 1 => -- Open forward tube in first r+1 spacetime directions;
    -- no constraint on remaining directions (μ > r), giving an open set.
    { z | ∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val ≤ r →
          let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
          (z i μ - prev μ).im > 0 }



/-- Extract one chronological spacetime-difference block from flattened
coordinates. -/
def flatDiffBlock {k d : ℕ}
    (z : Fin (k * (d + 1)) → ℂ) (i : Fin k) :
    Fin (d + 1) → ℂ :=
  fun μ => z (finProdFinEquiv (i, μ))

/-- Extracting one chronological displacement block is real-linear. -/
def flatDiffBlockRealLM {k d : ℕ}
    (i : Fin k) :
    (Fin (k * (d + 1)) → ℂ) →ₗ[ℝ] (Fin (d + 1) → ℂ) where
  toFun := fun z => flatDiffBlock z i
  map_add' := by
    intro z w
    rfl
  map_smul' := by
    intro c z
    rfl

@[simp] theorem flatDiffBlockRealLM_apply {k d : ℕ}
    (i : Fin k) (z : Fin (k * (d + 1)) → ℂ) :
    flatDiffBlockRealLM i z = flatDiffBlock z i :=
  rfl

