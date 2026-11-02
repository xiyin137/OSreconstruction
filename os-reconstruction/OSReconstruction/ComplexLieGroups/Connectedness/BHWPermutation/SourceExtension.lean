/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.MatrixPolynomialAlgebra
public import Init
public import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Core
public import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Geometry
public import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Preconnected
public import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
public import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected
public import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
public import OSReconstruction.ComplexLieGroups.JostPoints
public import OSReconstruction.SCV.DistributionalUniqueness

@[expose] public section

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

variable {d n : ℕ}

/-- Complex Minkowski Gram matrix of an ordered tuple of complex spacetime
vectors.  This is the scalar-product coordinate used by Hall-Wightman. -/
def sourceMinkowskiGram (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j =>
    ∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) * x i μ * x j μ

/- The unresolved Hall-Wightman source existence theorem for this data is kept
in the proof docs until it has a checked proof or an explicitly approved source
import boundary.  This production module contains only checked source data and
support lemmas. -/

/- The scalar-overlap continuation theorem from adjacent real Gram seeds is
also deliberately not exposed as production Lean yet.  The checked theorem
above is the last local support lemma before that genuine Hall-Wightman source
obligation. -/

/- The PET branch law, PET extension theorem, and sector single-valuedness
corollary are likewise proof-doc obligations until the Hall-Wightman source
compatibility theorem is proved. -/

end BHW
