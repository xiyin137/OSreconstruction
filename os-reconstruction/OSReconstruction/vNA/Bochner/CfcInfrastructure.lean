/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Init
import OSReconstruction.vNA.Unbounded.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm






























noncomputable section

open scoped InnerProduct ComplexConjugate Classical
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



instance : Algebra ℂ (H →L[ℂ] H) := by infer_instance













/- **Note on monotonicity:** Bump operators are NOT globally monotone in ε.

   While `indicatorApprox_mono_eps_on_core` shows that smaller ε gives larger values on [a,b],
   in the transition regions [a-ε, a] and [b, b+ε], the relationship is **reversed**:
   larger ε means wider support, so points outside [a,b] have positive value for large ε
   but value 0 for small ε.

   **Counterexample:** Take x with spectral measure concentrated near a - ε₁.
   Then for ε₂ > ε₁: bump_{ε₂}(a - ε₁) > 0 but bump_{ε₁}(a - ε₁) = 0.

   The Cauchy sequence proof for `bumpOperator_inner_cauchy` therefore uses **dominated
   convergence** for spectral measures instead of monotone convergence:
   - The bump functions bump_ε converge pointwise to χ_{(a,b)} ∪ {1/2 at boundaries}
   - All bump functions satisfy |bump_ε| ≤ 1
   - The spectral measure ⟨x, E(·) x⟩ is finite
   - By dominated convergence: ⟨x, P_ε x⟩ = ∫ bump_ε dμ_x converges -/



