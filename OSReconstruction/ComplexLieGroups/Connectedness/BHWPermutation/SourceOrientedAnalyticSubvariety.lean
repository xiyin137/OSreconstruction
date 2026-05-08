import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedExceptionalMinors
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameChart

/-!
# Analytic packaging for the oriented exceptional-rank locus

This file adds the first generic finite-dimensional analytic-subvariety
predicate needed by the oriented scalar descent route, then proves that the
oriented exceptional-rank locus is analytic relative to the oriented source
variety.  The proof consumes the checked maximal-minor equations; it does not
assert normality or any removable-singularity theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Relative openness of a subset of an ambient carrier `V`. -/
def IsRelOpenIn
    {E : Type*}
    [TopologicalSpace E]
    (V U : Set E) : Prop :=
  ∃ U0 : Set E, IsOpen U0 ∧ U = U0 ∩ V

/-- A finite-equation analytic subvariety of an ambient carrier `V`.

This is the elementary finite-dimensional form used by the current BHW route:
near every point of `V`, the subset `A` is cut out inside `V` by finitely many
ambient holomorphic equations. -/
def IsAnalyticSubvarietyIn
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E]
    (V A : Set E) : Prop :=
  A ⊆ V ∧
    ∀ x, x ∈ V →
      ∃ U0 : Set E,
        IsOpen U0 ∧ x ∈ U0 ∧
          ∃ m : ℕ, ∃ g : Fin m → E → ℂ,
            (∀ a, DifferentiableOn ℂ (g a) U0) ∧
              A ∩ U0 = {y | y ∈ V ∩ U0 ∧ ∀ a, g a y = 0}

/-- The source-oriented relative-open predicate is the generic relative-open
predicate with `V = sourceOrientedGramVariety d n`. -/
theorem IsRelOpenInSourceOrientedGramVariety.to_isRelOpenIn
    {U : Set (SourceOrientedGramData d n)}
    (hU : IsRelOpenInSourceOrientedGramVariety d n U) :
    IsRelOpenIn (sourceOrientedGramVariety d n) U :=
  hU

/-- Oriented source maximal minors are differentiable functions of the
oriented source coordinates. -/
@[fun_prop]
theorem differentiable_sourceOriented_sourceMatrixMinor
    (d n k : ℕ) (I J : Fin k → Fin n) :
    Differentiable ℂ (fun G : SourceOrientedGramData d n =>
      sourceMatrixMinor n k I J G.gram) := by
  unfold sourceMatrixMinor SourceOrientedGramData.gram
  fun_prop

/-- The oriented exceptional-rank locus is a finite-equation analytic
subvariety of the oriented source variety. -/
theorem sourceOrientedExceptionalRank_isAnalyticSubvariety
    (d n : ℕ) :
    IsAnalyticSubvarietyIn
      (sourceOrientedGramVariety d n)
      {G : SourceOrientedGramData d n | SourceOrientedExceptionalRank d n G} := by
  classical
  constructor
  · intro G hG
    exact hG.1
  · intro x hx
    let k : ℕ := min (d + 1) n
    let MinorIndex := (Fin k → Fin n) × (Fin k → Fin n)
    let e : MinorIndex ≃ Fin (Fintype.card MinorIndex) :=
      Fintype.equivFin MinorIndex
    let g : Fin (Fintype.card MinorIndex) →
        SourceOrientedGramData d n → ℂ :=
      fun a G => sourceMatrixMinor n k (e.symm a).1 (e.symm a).2 G.gram
    refine ⟨Set.univ, isOpen_univ, trivial,
      Fintype.card MinorIndex, g, ?_, ?_⟩
    · intro a
      dsimp [g]
      exact
        (differentiable_sourceOriented_sourceMatrixMinor
          d n k (e.symm a).1 (e.symm a).2).differentiableOn
    · ext G
      constructor
      · intro hG
        have hEset :
            G ∈ {G : SourceOrientedGramData d n |
                SourceOrientedExceptionalRank d n G} := hG.1
        rw [sourceOrientedExceptionalRank_eq_minorsVanishing d n] at hEset
        have hminors :
            G ∈ sourceOrientedGramVariety d n ∩
              {G : SourceOrientedGramData d n |
                ∀ I J : Fin k → Fin n,
                  sourceMatrixMinor n k I J G.gram = 0} := by
          simpa [k] using hEset
        refine ⟨⟨hminors.1, trivial⟩, ?_⟩
        intro a
        exact hminors.2 (e.symm a).1 (e.symm a).2
      · intro hG
        have hvar : G ∈ sourceOrientedGramVariety d n := hG.1.1
        have hminors :
            ∀ I J : Fin k → Fin n,
              sourceMatrixMinor n k I J G.gram = 0 := by
          intro I J
          let a : Fin (Fintype.card MinorIndex) := e ⟨I, J⟩
          have ha := hG.2 a
          simpa [g, a] using ha
        have hInter :
            G ∈ sourceOrientedGramVariety d n ∩
              {G : SourceOrientedGramData d n |
                ∀ I J : Fin (min (d + 1) n) → Fin n,
                  sourceMatrixMinor n (min (d + 1) n) I J G.gram = 0} := by
          exact ⟨hvar, by simpa [k] using hminors⟩
        rw [← sourceOrientedExceptionalRank_eq_minorsVanishing d n] at hInter
        exact ⟨hInter, trivial⟩

end BHW
