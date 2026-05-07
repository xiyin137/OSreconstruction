import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedStandardSOInvariantSubalgebra

/-!
# Source/dot transport for actual oriented invariant subalgebras

This file transports the actual standard-dot `SO` fixed subalgebra back to
source Minkowski tuple coordinates.  It defines the source actual invariant
subalgebra as that pullback, defines the actual source invariant-coordinate
map, and proves that generation, kernel, and surjectivity statements transport
from the standard-dot presentation.

No standard `SO` FFT/SFT theorem is proved here.
-/

noncomputable section

set_option linter.unnecessarySimpa false

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The actual source-oriented invariant subalgebra, defined by transporting
the standard-dot fixed subalgebra through the source/dot coordinate-ring
equivalence. -/
def sourceOrientedInvariantSubalgebra
    (d n : ℕ) : Subalgebra ℂ (sourceTupleCoordinateRing d n) :=
  Subalgebra.comap
    (sourceMinkowskiToDotCoordinateRingEquiv d n).toAlgHom
    (standardSOInvariantSubalgebra (d + 1) n)

/-- The source/dot tuple-coordinate equivalence sends the source actual
invariant subalgebra onto the standard-dot actual invariant subalgebra. -/
theorem sourceMinkowskiToDotCoordinateRingEquiv_map_sourceInvariantSubalgebra
    (d n : ℕ) :
    algEquivMapSubalgebra
        (sourceMinkowskiToDotCoordinateRingEquiv d n)
        (sourceOrientedInvariantSubalgebra d n) =
      standardSOInvariantSubalgebra (d + 1) n := by
  ext y
  constructor
  · intro hy
    rcases Subalgebra.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine Subalgebra.mem_map.mpr ?_
    refine
      ⟨(sourceMinkowskiToDotCoordinateRingEquiv d n).symm y, ?_, by simp⟩
    simpa [sourceOrientedInvariantSubalgebra] using hy

/-- Source/dot equivalence restricted to actual invariant subalgebras. -/
def sourceMinkowskiToDotInvariantSubalgebraEquiv
    (d n : ℕ) :
    sourceOrientedInvariantSubalgebra d n ≃ₐ[ℂ]
      standardSOInvariantSubalgebra (d + 1) n :=
  algEquivOfMappedSubalgebraEq
    (sourceMinkowskiToDotCoordinateRingEquiv d n)
    (sourceOrientedInvariantSubalgebra d n)
    (standardSOInvariantSubalgebra (d + 1) n)
    (sourceMinkowskiToDotCoordinateRingEquiv_map_sourceInvariantSubalgebra d n)

/-- The source generated subalgebra is contained in the actual source
invariant subalgebra.  The reverse inclusion is transported from the standard
FFT theorem in a later theorem. -/
theorem sourceOrientedGeneratorSubalgebra_le_invariantSubalgebra
    (d n : ℕ) :
    sourceOrientedGeneratorSubalgebra d n ≤
      sourceOrientedInvariantSubalgebra d n := by
  intro p hp
  change sourceMinkowskiToDotCoordinateRingEquiv d n p ∈
    standardSOInvariantSubalgebra (d + 1) n
  have hmap :
      sourceMinkowskiToDotCoordinateRingEquiv d n p ∈
        algEquivMapSubalgebra
          (sourceMinkowskiToDotCoordinateRingEquiv d n)
          (sourceOrientedGeneratorSubalgebra d n) :=
    Subalgebra.mem_map.mpr ⟨p, hp, rfl⟩
  have hgen :
      sourceMinkowskiToDotCoordinateRingEquiv d n p ∈
        standardSOGeneratorSubalgebra (d + 1) n := by
    simpa [sourceMinkowskiToDotCoordinateRingEquiv_map_sourceGeneratorSubalgebra]
      using hmap
  exact standardSOGeneratorSubalgebra_le_invariantSubalgebra (d + 1) n hgen

/-- Inclusion of the source generated subalgebra into the actual source
invariant subalgebra. -/
def sourceOrientedGeneratorToInvariantAlgHom
    (d n : ℕ) :
    sourceOrientedGeneratorSubalgebra d n →ₐ[ℂ]
      sourceOrientedInvariantSubalgebra d n :=
  Subalgebra.inclusion
    (sourceOrientedGeneratorSubalgebra_le_invariantSubalgebra d n)

/-- The actual source invariant-coordinate map, obtained by following the
source generated-coordinate map by inclusion into actual invariants. -/
def sourceOrientedInvariantCoordinateMap
    (d n : ℕ) :
    sourceOrientedInvariantCoordinateRing d n →ₐ[ℂ]
      sourceOrientedInvariantSubalgebra d n :=
  (sourceOrientedGeneratorToInvariantAlgHom d n).comp
    (sourceOrientedGeneratorCoordinateMap d n)

@[simp]
theorem sourceOrientedInvariantCoordinateMap_apply_gram
    (d n : ℕ) (ij : Fin n × Fin n) :
    sourceOrientedInvariantCoordinateMap d n (MvPolynomial.X (Sum.inl ij)) =
      ⟨sourceGramCoordinatePolynomial d n ij,
        sourceOrientedGeneratorSubalgebra_le_invariantSubalgebra d n
          (sourceGramCoordinatePolynomial_mem_generatorSubalgebra d n ij)⟩ := by
  ext
  simp [sourceOrientedInvariantCoordinateMap,
    sourceOrientedGeneratorToInvariantAlgHom, sourceGramGeneratorElement]

@[simp]
theorem sourceOrientedInvariantCoordinateMap_apply_det
    (d n : ℕ) (ι : Fin (d + 1) ↪ Fin n) :
    sourceOrientedInvariantCoordinateMap d n (MvPolynomial.X (Sum.inr ι)) =
      ⟨sourceFullFrameDetPolynomial d n ι,
        sourceOrientedGeneratorSubalgebra_le_invariantSubalgebra d n
          (sourceFullFrameDetPolynomial_mem_generatorSubalgebra d n ι)⟩ := by
  ext
  simp [sourceOrientedInvariantCoordinateMap,
    sourceOrientedGeneratorToInvariantAlgHom, sourceFullFrameDetGeneratorElement]

/-- The source/dot invariant-coordinate square commutes. -/
theorem sourceMinkowskiToDotInvariantCoordinateMap_commutes
    (d n : ℕ)
    (p : sourceOrientedInvariantCoordinateRing d n) :
    sourceMinkowskiToDotInvariantSubalgebraEquiv d n
        (sourceOrientedInvariantCoordinateMap d n p) =
      standardSOInvariantCoordinateMap (d + 1) n
        (sourceMinkowskiToDotInvariantCoordinateEquiv d n p) := by
  apply Subtype.ext
  change sourceMinkowskiToDotCoordinateRingEquiv d n
      ((sourceOrientedGeneratorCoordinateMap d n p :
        sourceOrientedGeneratorSubalgebra d n) :
          sourceTupleCoordinateRing d n) =
    ((standardSOGeneratorCoordinateMap (d + 1) n
        (sourceMinkowskiToDotInvariantCoordinateEquiv d n p) :
        standardSOGeneratorSubalgebra (d + 1) n) :
          standardTupleCoordinateRing (d + 1) n)
  exact
    congrArg Subtype.val
      (sourceMinkowskiToDotGeneratorCoordinateMap_commutes d n p)

/-- Source invariant-coordinate surjectivity transported from the standard
invariant-coordinate map. -/
theorem sourceOrientedInvariantCoordinateMap_surjective_of_standard
    (d n : ℕ)
    (hstd :
      Function.Surjective
        (standardSOInvariantCoordinateMap (d + 1) n)) :
    Function.Surjective (sourceOrientedInvariantCoordinateMap d n) :=
  surjective_of_algEquiv_transport
    (eDomain := sourceMinkowskiToDotInvariantCoordinateEquiv d n)
    (eCodomain := sourceMinkowskiToDotInvariantSubalgebraEquiv d n)
    (f := sourceOrientedInvariantCoordinateMap d n)
    (g := standardSOInvariantCoordinateMap (d + 1) n)
    (hmap := sourceMinkowskiToDotInvariantCoordinateMap_commutes d n)
    hstd

/-- Source FFT generation transported from the standard FFT generation
equality. -/
theorem sourceOrientedInvariantRing_generated_by_gram_det_of_standard
    (d n : ℕ)
    (hFFT :
      standardSOInvariantSubalgebra (d + 1) n =
        standardSOGeneratorSubalgebra (d + 1) n) :
    sourceOrientedInvariantSubalgebra d n =
      sourceOrientedGeneratorSubalgebra d n := by
  apply
    algEquivMapSubalgebra_injective
      (sourceMinkowskiToDotCoordinateRingEquiv d n)
  rw [sourceMinkowskiToDotCoordinateRingEquiv_map_sourceInvariantSubalgebra,
    sourceMinkowskiToDotCoordinateRingEquiv_map_sourceGeneratorSubalgebra,
    hFFT]

/-- Source FFT generation transported from the standard FFT in its displayed
pairing/volume adjoin form. -/
theorem sourceOrientedInvariantRing_generated_by_gram_det_of_standard_generators
    (d n : ℕ)
    (hFFT :
      standardSOInvariantSubalgebra (d + 1) n =
        Algebra.adjoin ℂ
          (Set.range (standardPairingCoordinatePolynomial (d + 1) n) ∪
            Set.range (standardVolumeCoordinatePolynomial (d + 1) n))) :
    sourceOrientedInvariantSubalgebra d n =
      Algebra.adjoin ℂ
        (Set.range (sourceGramCoordinatePolynomial d n) ∪
          Set.range (sourceFullFrameDetPolynomial d n)) := by
  have hstd :
      standardSOInvariantSubalgebra (d + 1) n =
        standardSOGeneratorSubalgebra (d + 1) n := by
    simpa [standardSOGeneratorSubalgebra] using hFFT
  simpa [sourceOrientedGeneratorSubalgebra] using
    sourceOrientedInvariantRing_generated_by_gram_det_of_standard
      d n hstd

/-- Source invariant-coordinate surjectivity transported from the standard
FFT in its displayed pairing/volume adjoin form. -/
theorem sourceOrientedInvariantCoordinateMap_surjective_of_standard_generators
    (d n : ℕ)
    (hFFT :
      standardSOInvariantSubalgebra (d + 1) n =
        Algebra.adjoin ℂ
          (Set.range (standardPairingCoordinatePolynomial (d + 1) n) ∪
            Set.range (standardVolumeCoordinatePolynomial (d + 1) n))) :
    Function.Surjective (sourceOrientedInvariantCoordinateMap d n) :=
  sourceOrientedInvariantCoordinateMap_surjective_of_standard d n
    (standardSOInvariantCoordinateMap_surjective_of_generators
      (d + 1) n hFFT)

/-- Source SFT kernel transported from the standard SFT kernel equality. -/
theorem sourceOrientedInvariantRing_relations_kernel_of_standard
    (d n : ℕ)
    (hSFT :
      RingHom.ker (standardSOInvariantCoordinateMap (d + 1) n) =
        standardSOAlgebraicRelationIdeal (d + 1) n) :
    RingHom.ker (sourceOrientedInvariantCoordinateMap d n) =
      sourceOrientedAlgebraicRelationIdeal d n := by
  apply
    algEquivMapIdeal_injective
      (sourceMinkowskiToDotInvariantCoordinateEquiv d n)
  rw [algEquivMapIdeal_ker_of_commutes
      (sourceMinkowskiToDotInvariantCoordinateEquiv d n)
      (sourceMinkowskiToDotInvariantSubalgebraEquiv d n)
      (sourceOrientedInvariantCoordinateMap d n)
      (standardSOInvariantCoordinateMap (d + 1) n)
      (sourceMinkowskiToDotInvariantCoordinateMap_commutes d n),
    hSFT,
    sourceOrientedRelationIdeal_transport_dot]

end BHW
