/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import SchwartzNuclear
import GaussianField
import OSReconstruction.Wightman.NuclearSpaces.NuclearSpace

/-!
# Bridge: GaussianField → OSReconstruction

This file imports results from the `gaussian-field` library and re-exports
them for use in the OS reconstruction project.

## What we get from gaussian-field

### SchwartzNuclear (all sorry-free)
- Hermite functions: definition, orthonormality, Schwartz membership
- Schwartz-Hermite expansion: `f = ∑ₙ cₙ(f) ψₙ` in Schwartz topology
- Tensor product Hermite basis for S(ℝⁿ)
- `GaussianField.DyninMityaginSpace (SchwartzMap D ℝ)` instance

### GaussianField (all sorry-free)
- Spectral theorem for compact self-adjoint operators
- Nuclear SVD: singular value decomposition for nuclear operators
- Gaussian measure construction on `WeakDual ℝ E`
- Characteristic functional: `∫ exp(i⟨ω,f⟩) dμ = exp(-½ ‖T(f)‖²)`
- Moment identities: E[ω(f)] = 0, E[ω(f)ω(g)] = ⟨Tf,Tg⟩
- Pietsch nuclear space definition and DM → Pietsch bridge

## Two NuclearSpace definitions

This project (OSReconstruction) defines `NuclearSpace` via the Pietsch
characterization (nuclear dominance by seminorms). The gaussian-field project
defines `GaussianField.DyninMityaginSpace` via the Dynin-Mityagin characterization
(Schauder basis with rapid decay) and `GaussianField.NuclearSpace`
via the Pietsch characterization.

The DM → Pietsch bridge is proved in gaussian-field
(`GaussianField.DyninMityaginSpace.toNuclearSpace`). This file provides
the final conversion from `GaussianField.NuclearSpace` to the
OSReconstruction `NuclearSpace`.

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4
- Pietsch, "Nuclear Locally Convex Spaces" (1972)
-/

noncomputable section

open GaussianField
open scoped NNReal

/-! ### Schwartz DyninMityaginSpace instance

The `schwartz_dyninMityaginSpace` instance from gaussian-field provides a
`GaussianField.DyninMityaginSpace` instance for `SchwartzMap D ℝ` whenever
`D` is a nontrivial finite-dimensional normed space with a Borel σ-algebra.

This instance is registered globally, so once this file is imported,
typeclass synthesis will automatically find it. -/

-- Verify the instance is available
example : GaussianField.DyninMityaginSpace (SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ) :=
  inferInstance

/-! ### Hermite function results

The gaussian-field library provides sorry-free proofs of the fundamental
properties of Hermite functions. These are at the top-level namespace. -/

/-- Hermite functions from gaussian-field. These are ψₙ(x) = cₙ · Hₙ(x√2) · exp(-x²/2)
    using probabilist Hermite polynomials. -/
abbrev gfHermiteFunction := hermiteFunction

/-- Hermite functions are in the Schwartz space (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_schwartz := hermiteFunction_schwartz

/-- Hermite functions are orthonormal in L²(ℝ) (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_orthonormal := hermiteFunction_orthonormal

/-- Hermite functions are complete in L² (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_complete := hermiteFunction_complete

/-- Seminorm bounds on Hermite functions (sorry-free from gaussian-field). -/
abbrev gfHermiteFunction_seminorm_bound := hermiteFunction_seminorm_bound

/-! ### Spectral theorem -/

/-- Spectral theorem for compact self-adjoint operators on a real Hilbert space.
    Sorry-free from gaussian-field.

    For a compact self-adjoint T ≠ 0, there exist eigenvectors forming a
    HilbertBasis, with eigenvalues μ and T(x) = ∑ μᵢ ⟨eᵢ, x⟩ eᵢ. -/
abbrev gfCompactSelfAdjointSpectral := @compact_selfAdjoint_spectral

/-! ### Gaussian measure construction -/

/-- The configuration space (space of distributions). -/
abbrev gfConfiguration := @Configuration

/-- The Gaussian measure on Configuration E with covariance ⟨T·, T·⟩. -/
abbrev gfMeasure := @GaussianField.measure

/-- Characteristic functional: ∫ exp(i⟨ω,f⟩) dμ = exp(-½ ‖T(f)‖²).
    Sorry-free from gaussian-field. -/
abbrev gfCharFun := @charFun

/-! ### Moment identities -/

/-- The Gaussian measure is centered: E[ω(f)] = 0 (sorry-free). -/
abbrev gfMeasureCentered := @measure_centered

/-- Cross-moment equals covariance: E[ω(f)ω(g)] = ⟨Tf, Tg⟩ (sorry-free). -/
abbrev gfCrossMomentEqCovariance := @cross_moment_eq_covariance

/-- The pairing ω(f) is Gaussian-distributed (sorry-free). -/
abbrev gfPairingIsGaussian := @pairing_is_gaussian

/-! ### Bridge: GaussianField.NuclearSpace → _root_.NuclearSpace

The two Pietsch definitions (`GaussianField.NuclearSpace` from gaussian-field
and `NuclearSpace` from OSReconstruction) have identical `nuclear_dominance`
fields. This trivial conversion connects them. -/

/-- Convert `GaussianField.NuclearSpace` to the OSReconstruction `NuclearSpace`.

The two definitions have identical `nuclear_dominance` fields, so the
conversion is just field extraction. -/
theorem GaussianField.NuclearSpace.toOSNuclearSpace_pietsch (E : Type*)
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [h : GaussianField.NuclearSpace E] : _root_.NuclearSpace E where
  nuclear_dominance := h.nuclear_dominance

/-- **Dynin-Mityagin implies OSReconstruction Pietsch nuclearity.**

Composes the gaussian-field bridge (`DyninMityaginSpace.toNuclearSpace`)
with the trivial conversion to the OSReconstruction `NuclearSpace`. -/
theorem GaussianField.DyninMityaginSpace.toOSNuclearSpace (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [GaussianField.DyninMityaginSpace E] : _root_.NuclearSpace E :=
  letI := GaussianField.DyninMityaginSpace.toNuclearSpace E
  GaussianField.NuclearSpace.toOSNuclearSpace_pietsch E

end
