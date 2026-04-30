import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexDensity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexLocalChart

/-!
# Source distributional uniqueness on Hall-Wightman real environments

This file consumes the checked source complex Gram-variety identity principle
to prove the theorem-2-facing uniqueness predicate for Hall-Wightman real
scalar-product environments.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- A Hall-Wightman real scalar-product environment is a uniqueness set for
variety-holomorphic source scalar representatives. -/
theorem sourceDistributionalUniquenessSetOnVariety_of_realEnvironment
    [NeZero d]
    (n : ℕ)
    {O : Set (Fin n → Fin n → ℝ)}
    (hO_env : IsHWRealEnvironment d n O) :
    sourceDistributionalUniquenessSetOnVariety d n O := by
  refine ⟨hO_env.nonempty, ?_⟩
  intro U Φ Ψ hU_rel hU_conn hO_sub hΦ hΨ h_eq
  let H : (Fin n → Fin n → ℂ) → ℂ := fun Z => Φ Z - Ψ Z
  have hH : SourceVarietyHolomorphicOn d n H U :=
    SourceVarietyHolomorphicOn.sub (d := d) (n := n) hΦ hΨ
  have hO_zero :
      ∀ G ∈ O, H (sourceRealGramComplexify n G) = 0 := by
    intro G hG
    dsimp [H]
    exact sub_eq_zero.mpr (h_eq G hG)
  obtain ⟨W, hW_rel, hW_ne, hW_sub, hW_eq⟩ :=
    sourceVariety_localChart_totallyReal_zero
      (d := d) (n := n) hO_env hU_rel hO_sub hH hO_zero
  have hzeroU : Set.EqOn H 0 U :=
    sourceComplexGramVariety_identity_principle
      (d := d) (n := n) hU_rel hU_conn hW_rel hW_ne hW_sub hH hW_eq
  intro Z hZ
  exact sub_eq_zero.mp (hzeroU hZ)

/-- The source Gram image of a nonempty open Jost patch is a uniqueness set for
variety-holomorphic source scalar representatives.

The proof chooses a regular Jost point in the patch using density of
`SourceGramRegularAt`, builds a smaller Hall-Wightman real environment there,
proves uniqueness on that smaller environment, and enlarges by monotonicity to
the full Gram image of the patch. -/
theorem sourceDistributionalUniquenessSetOnVariety_of_open_jost_patch
    [NeZero d]
    (n : ℕ)
    {V : Set (Fin n → Fin (d + 1) → ℝ)}
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_jost : ∀ x ∈ V, x ∈ JostSet d n) :
    sourceDistributionalUniquenessSetOnVariety d n
      (sourceRealMinkowskiGram d n '' V) := by
  rcases (dense_sourceGramRegularAt d n).exists_mem_open hV_open hV_nonempty with
    ⟨x0, hx0reg, hx0V⟩
  have hx0_jost : x0 ∈ JostSet d n := hV_jost x0 hx0V
  rcases sourceRealGramMap_realEnvironmentAt_of_regular
      (d := d) n hx0reg hx0_jost V hV_open hx0V with
    ⟨O, hO_sub, hO_env⟩
  exact
    sourceDistributionalUniquenessSetOnVariety_mono d n
      (sourceDistributionalUniquenessSetOnVariety_of_realEnvironment
        (d := d) n hO_env)
      hO_sub

/-- Package the Gram image of a nonempty open Jost patch in exactly the form
needed by selected OS/Jost anchor data. -/
theorem exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch
    [NeZero d]
    (n : ℕ)
    {V : Set (Fin n → Fin (d + 1) → ℝ)}
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_jost : ∀ x ∈ V, x ∈ JostSet d n) :
    ∃ E : Set (Fin n → Fin n → ℝ),
      sourceDistributionalUniquenessSetOnVariety d n E ∧
      (∀ x ∈ V, sourceRealMinkowskiGram d n x ∈ E) ∧
      (∀ G ∈ E, ∃ x ∈ V, sourceRealMinkowskiGram d n x = G) := by
  refine ⟨sourceRealMinkowskiGram d n '' V, ?_, ?_, ?_⟩
  · exact
      sourceDistributionalUniquenessSetOnVariety_of_open_jost_patch
        (d := d) n hV_open hV_nonempty hV_jost
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · intro G hG
    rcases hG with ⟨x, hxV, hGx⟩
    exact ⟨x, hxV, hGx⟩

end BHW
