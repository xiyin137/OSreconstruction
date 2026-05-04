import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation

/-!
# Rank-deficient oriented local-image packets

This file records the topology interface expected from the rank-deficient
Schur/residual normal-form construction.  The hard algebraic construction must
produce one of these packets; the lemma here extracts the connected relatively
open patch needed by the oriented local-basis dispatcher.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Local-image data for a rank-deficient point of the oriented source
variety.  The parameter space is intentionally abstract: the planned producer
will instantiate it with the finite Schur head/mixed/tail parameter box. -/
structure SourceOrientedRankDeficientVarietyLocalImageData
    {P : Type*} [TopologicalSpace P]
    (G0 : SourceOrientedGramData d n)
    (N0 : Set (SourceOrientedGramData d n)) where
  parameterBox : Set P
  parameterBox_open : IsOpen parameterBox
  parameterBox_connected : IsConnected parameterBox
  p0 : P
  p0_mem : p0 ∈ parameterBox
  image : P → SourceOrientedGramData d n
  image_continuousOn : ContinuousOn image parameterBox
  center_eq : image p0 = G0
  image_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n (image '' parameterBox)
  image_sub :
    image '' parameterBox ⊆ N0 ∩ sourceOrientedGramVariety d n

namespace SourceOrientedRankDeficientVarietyLocalImageData

/-- A rank-deficient local-image packet yields the connected relatively open
patch required by the oriented local-basis theorem. -/
theorem to_connectedRelOpenPatch
    {P : Type*} [TopologicalSpace P]
    {G0 : SourceOrientedGramData d n}
    {N0 : Set (SourceOrientedGramData d n)}
    (R :
      SourceOrientedRankDeficientVarietyLocalImageData
        (d := d) (n := n) (P := P) G0 N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      IsConnected V ∧
      V ⊆ N0 ∩ sourceOrientedGramVariety d n := by
  refine ⟨R.image '' R.parameterBox, ?_, R.image_relOpen, ?_, R.image_sub⟩
  · exact ⟨R.p0, R.p0_mem, R.center_eq⟩
  · exact R.parameterBox_connected.image R.image R.image_continuousOn

end SourceOrientedRankDeficientVarietyLocalImageData

/-- A producer of rank-deficient local-image packets is exactly the
rank-deficient patch producer expected by the local-basis dispatcher. -/
theorem sourceOrientedRankDeficientPatchAt_of_localImageProducer
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientVarietyLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hex : SourceOrientedExceptionalRank d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      IsConnected V ∧
      V ⊆ N0 ∩ sourceOrientedGramVariety d n := by
  rcases rankDeficientLocalImageAt hG0 hex hN0_open hG0N0 with
    ⟨P, instP, R⟩
  letI : TopologicalSpace P := instP
  exact R.to_connectedRelOpenPatch

end BHW
