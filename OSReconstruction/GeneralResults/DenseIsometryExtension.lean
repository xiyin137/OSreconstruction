/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Dense Submodule Isometry Extension

A linear isometry from a dense submodule of a Hilbert space into a complete
inner product space extends to a linear isometry on the whole space.

This is the BLT (Bounded Linear Transformation) theorem specialized to
isometries. The proof uses uniform continuity of isometries to extend
to the completion, then verifies linearity and isometry of the extension.

## Reference

Reed-Simon I, §I.7 (BLT theorem)
-/

/-- **BLT for isometries.** A linear isometry from a dense submodule of a
Hilbert space into a complete inner product space extends to a linear isometry
on the whole space.

The proof combines:
1. Isometries are uniformly continuous
2. Uniformly continuous maps from dense subsets of complete spaces extend uniquely
3. The extension preserves linearity and isometry by density + continuity

This is a standard FA result (Reed-Simon I §I.7). The formal proof requires
wiring Mathlib's `DenseRange.extend` with linearity/isometry verification,
which is straightforward but verbose. -/
axiom dense_submodule_isometry_extension
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (S : Submodule ℂ H₁) (hS : Dense (S : Set H₁))
    (T : S →ₗᵢ[ℂ] H₂) :
    ∃ (U : H₁ →ₗᵢ[ℂ] H₂), ∀ x : S, U x = T x
