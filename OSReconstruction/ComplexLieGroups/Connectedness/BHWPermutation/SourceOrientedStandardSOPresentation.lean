import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedInvariantKernel

/-!
# Conditional standard `SO` coordinate-presentation packet

This file records the exact standard-dot invariant-theory boundary needed by
the oriented source normality route.  It is intentionally axiom-free: it does
not prove or assume the first or second fundamental theorem for `SO_D(ℂ)`.
Instead, it packages those two facts as an explicit data object and derives the
already-formal standard/source surjectivity and transport consequences.

Downstream theorem-2 code may consume this packet only as an explicit
hypothesis until the standard `SO` FFT/SFT theorem is proved or imported from
a sorry-free source with the same coordinate conventions.  The optional
paper-classical axiom producer lives in `SourceOrientedStandardSOAxiom.lean`
and is deliberately not imported by the BHW permutation barrel.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Exact conditional standard-dot coordinate presentation for the special
orthogonal invariant ring on `(ℂ^D)^n`.

The `fft` field is the first fundamental theorem in the displayed
pairing/ordered-volume coordinates.  The `sft` field is the second fundamental
theorem identifying the kernel with the explicit symmetry, rank-minor,
alternation, Cauchy-Binet, and linear vector-bracket syzygy relation ideal.

This structure is not an axiom; it is a local proof-object shape for a future
sorry-free standard invariant-theory theorem. -/
structure StandardSOCoordinatePresentationData
    (D n : ℕ) : Prop where
  fft :
    standardSOInvariantSubalgebra D n =
      Algebra.adjoin ℂ
        (Set.range (standardPairingCoordinatePolynomial D n) ∪
          Set.range (standardVolumeCoordinatePolynomial D n))
  sft :
    RingHom.ker (standardSOInvariantCoordinateMap D n) =
      standardSOAlgebraicRelationIdeal D n

namespace StandardSOCoordinatePresentationData

/-- Surjectivity of the actual invariant-coordinate map follows formally from
the displayed-generator FFT field. -/
theorem surjective
    {D n : ℕ}
    (H : StandardSOCoordinatePresentationData D n) :
    Function.Surjective (standardSOInvariantCoordinateMap D n) :=
  standardSOInvariantCoordinateMap_surjective_of_generators D n H.fft

end StandardSOCoordinatePresentationData

/-- The conditional presentation packet yields the triple shape used in proof
docs for the future unconditional standard `SO` theorem. -/
theorem standardSO_FFT_SFT_coordinatePresentation_of_data
    {D n : ℕ}
    (H : StandardSOCoordinatePresentationData D n) :
    standardSOInvariantSubalgebra D n =
      Algebra.adjoin ℂ
        (Set.range (standardPairingCoordinatePolynomial D n) ∪
          Set.range (standardVolumeCoordinatePolynomial D n)) ∧
    RingHom.ker (standardSOInvariantCoordinateMap D n) =
      standardSOAlgebraicRelationIdeal D n ∧
    Function.Surjective (standardSOInvariantCoordinateMap D n) :=
  ⟨H.fft, H.sft, H.surjective⟩

/-- Source FFT generation transported from a conditional standard-dot
presentation packet. -/
theorem sourceOrientedInvariantRing_generated_by_gram_det_of_presentation
    {d n : ℕ}
    (H : StandardSOCoordinatePresentationData (d + 1) n) :
    sourceOrientedInvariantSubalgebra d n =
      Algebra.adjoin ℂ
        (Set.range (sourceGramCoordinatePolynomial d n) ∪
          Set.range (sourceFullFrameDetPolynomial d n)) :=
  sourceOrientedInvariantRing_generated_by_gram_det_of_standard_generators
    d n H.fft

/-- Source SFT kernel equality transported from a conditional standard-dot
presentation packet. -/
theorem sourceOrientedInvariantRing_relations_kernel_of_presentation
    {d n : ℕ}
    (H : StandardSOCoordinatePresentationData (d + 1) n) :
    RingHom.ker (sourceOrientedInvariantCoordinateMap d n) =
      sourceOrientedAlgebraicRelationIdeal d n :=
  sourceOrientedInvariantRing_relations_kernel_of_standard d n H.sft

/-- Source invariant-coordinate surjectivity transported from a conditional
standard-dot presentation packet. -/
theorem sourceOrientedInvariantCoordinateMap_surjective_of_presentation
    {d n : ℕ}
    (H : StandardSOCoordinatePresentationData (d + 1) n) :
    Function.Surjective (sourceOrientedInvariantCoordinateMap d n) :=
  sourceOrientedInvariantCoordinateMap_surjective_of_standard_generators
    d n H.fft

/-- Source-side coordinate presentation data transported from the standard-dot
presentation.  This is the source theorem shape consumed by later
coordinate-ring and normality adapters. -/
structure SourceOrientedCoordinatePresentationData
    (d n : ℕ) : Prop where
  fft :
    sourceOrientedInvariantSubalgebra d n =
      Algebra.adjoin ℂ
        (Set.range (sourceGramCoordinatePolynomial d n) ∪
          Set.range (sourceFullFrameDetPolynomial d n))
  sft :
    RingHom.ker (sourceOrientedInvariantCoordinateMap d n) =
      sourceOrientedAlgebraicRelationIdeal d n
  surjective :
    Function.Surjective (sourceOrientedInvariantCoordinateMap d n)

/-- The exact standard-dot presentation packet formally gives the source
presentation packet through the checked source/dot transport layer. -/
theorem sourceOrientedCoordinatePresentationData_of_standard
    {d n : ℕ}
    (H : StandardSOCoordinatePresentationData (d + 1) n) :
    SourceOrientedCoordinatePresentationData d n :=
  ⟨sourceOrientedInvariantRing_generated_by_gram_det_of_presentation H,
    sourceOrientedInvariantRing_relations_kernel_of_presentation H,
    sourceOrientedInvariantCoordinateMap_surjective_of_presentation H⟩

end BHW
