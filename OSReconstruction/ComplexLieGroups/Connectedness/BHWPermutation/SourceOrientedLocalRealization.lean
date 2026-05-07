import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented

/-!
# Local realization for the oriented extended-tube image

This file isolates the purely topological part of relative openness for the
oriented extended-tube image.  The hard Hall-Wightman Lemma-3 content remains
the local vector-realization datum at each extended-tube point.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Local vector-realization data for the oriented extended-tube image near an
extended-tube source tuple.  The `realizes` field is the mathematical content:
nearby oriented-variety points in the ambient neighborhood must be realized by
actual source tuples still lying in `ExtendedTube`. -/
structure SourceOrientedExtendedTubeLocalRealizationData
    (d n : ℕ)
    (z0 : Fin n → Fin (d + 1) → ℂ) where
  Ω : Set (SourceOrientedGramData d n)
  Ω_open : IsOpen Ω
  center_mem : sourceOrientedMinkowskiInvariant d n z0 ∈ Ω
  realizes :
    Ω ∩ sourceOrientedGramVariety d n ⊆
      sourceOrientedExtendedTubeDomain d n

/-- The local-realization theorem is exactly the missing geometric input for
relative openness of the oriented extended-tube image. -/
def SourceOrientedExtendedTubeLocalRealizationProducer
    (d n : ℕ) : Type :=
  ∀ {z0 : Fin n → Fin (d + 1) → ℂ},
    z0 ∈ ExtendedTube d n →
      SourceOrientedExtendedTubeLocalRealizationData d n z0

/-- Relative openness of the oriented extended-tube image, once local
realization is supplied at every extended-tube source tuple. -/
theorem sourceOrientedExtendedTubeDomain_relOpen_of_localRealization
    (localRealization :
      SourceOrientedExtendedTubeLocalRealizationProducer d n) :
    IsRelOpenInSourceOrientedGramVariety d n
      (sourceOrientedExtendedTubeDomain d n) := by
  classical
  let I : Type := {z : Fin n → Fin (d + 1) → ℂ // z ∈ ExtendedTube d n}
  let Ω : Set (SourceOrientedGramData d n) :=
    ⋃ p : I, (localRealization p.2).Ω
  refine ⟨Ω, ?_, ?_⟩
  · exact isOpen_iUnion fun p => (localRealization p.2).Ω_open
  · ext G
    constructor
    · intro hG
      rcases hG with ⟨z, hz, rfl⟩
      constructor
      · exact Set.mem_iUnion.2
          ⟨⟨z, hz⟩, (localRealization hz).center_mem⟩
      · exact ⟨z, rfl⟩
    · rintro ⟨hGΩ, hGvar⟩
      rcases Set.mem_iUnion.1 hGΩ with ⟨p, hp⟩
      exact (localRealization p.2).realizes ⟨hp, hGvar⟩

/-- Relative openness plus connectedness of the oriented extended-tube image,
with the geometric work isolated in the local-realization producer. -/
theorem sourceOrientedExtendedTubeDomain_relOpen_connected_of_localRealization
    (localRealization :
      SourceOrientedExtendedTubeLocalRealizationProducer d n) :
    IsRelOpenInSourceOrientedGramVariety d n
        (sourceOrientedExtendedTubeDomain d n) ∧
      IsConnected (sourceOrientedExtendedTubeDomain d n) := by
  exact
    ⟨sourceOrientedExtendedTubeDomain_relOpen_of_localRealization
        (d := d) (n := n) localRealization,
      sourceOrientedExtendedTubeDomain_connected d n⟩

end BHW
