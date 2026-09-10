/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Init
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Core
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Geometry
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Preconnected
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
import OSReconstruction.ComplexLieGroups.JostPoints
import OSReconstruction.SCV.DistributionalUniqueness















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
