/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension











noncomputable section

open scoped Matrix.Norms.Operator

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Source Gram data enhanced by all ordered full-frame determinant
coordinates.  The determinant coordinates are indexed by embeddings of a
spacetime-size frame into the source labels.

This is an abbreviation for the product coordinate space so the oriented
source variety inherits the usual finite-dimensional complex normed vector
space structure needed by the later germ-holomorphic API. -/
abbrev SourceOrientedGramData (d n : ℕ) :=
  (Fin n → Fin n → ℂ) × ((Fin (d + 1) ↪ Fin n) → ℂ)

namespace SourceOrientedGramData

end SourceOrientedGramData

/-- Selected full-frame source matrix.  Rows are source labels and columns are
spacetime coordinates. -/
def sourceFullFrameMatrix (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun a μ => z (ι a) μ

/-- Determinant of a selected full-frame source matrix. -/
def sourceFullFrameDet (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) : ℂ :=
  (sourceFullFrameMatrix d n ι z).det

/-- The oriented source invariant: ordinary source Gram coordinates plus all
full-frame determinants. -/
def sourceOrientedMinkowskiInvariant (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    SourceOrientedGramData d n :=
  (sourceMinkowskiGram d n z, fun ι => sourceFullFrameDet d n ι z)

/-- The oriented Hall-Wightman source variety. -/
def sourceOrientedGramVariety (d n : ℕ) :
    Set (SourceOrientedGramData d n) :=
  Set.range (sourceOrientedMinkowskiInvariant d n)

/-- Relative openness in the oriented source variety. -/
def IsRelOpenInSourceOrientedGramVariety
    (d n : ℕ)
    (U : Set (SourceOrientedGramData d n)) : Prop :=
  ∃ U0 : Set (SourceOrientedGramData d n),
    IsOpen U0 ∧ U = U0 ∩ sourceOrientedGramVariety d n

/-- Germ-style holomorphicity on the oriented source variety.  The local
representative may differ from the global scalar function away from the
oriented source variety; equality is required only on the analytic variety
slice. -/
def SourceOrientedVarietyGermHolomorphicOn
    (d n : ℕ)
    (Φ : SourceOrientedGramData d n → ℂ)
    (U : Set (SourceOrientedGramData d n)) : Prop :=
  ∀ G ∈ U, ∃ U0 Ψ,
    IsOpen U0 ∧ G ∈ U0 ∧ DifferentiableOn ℂ Ψ U0 ∧
      Set.EqOn Φ Ψ (U0 ∩ sourceOrientedGramVariety d n) ∧
      U0 ∩ sourceOrientedGramVariety d n ⊆ U

end BHW
