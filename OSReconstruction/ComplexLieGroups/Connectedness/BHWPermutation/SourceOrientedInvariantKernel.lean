import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedInvariantSubalgebraTransport
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedStandardSOInvariantKernel

/-!
# One containment in the source-oriented relation-kernel theorem

This file transports the easy standard-dot SFT containment to source
coordinates: every displayed source relation maps to zero under the actual
source invariant-coordinate map.

The reverse containment is still the genuine SFT theorem, transported by
`sourceOrientedInvariantRing_relations_kernel_of_standard`.
-/

noncomputable section

set_option linter.unnecessarySimpa false

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Every explicit source-oriented algebraic relation lies in the kernel of
the actual source invariant-coordinate map.  The reverse inclusion is the
genuine SFT theorem. -/
theorem sourceOrientedAlgebraicRelationIdeal_le_invariantCoordinateMap_ker
    (d n : ℕ) :
    sourceOrientedAlgebraicRelationIdeal d n ≤
      RingHom.ker (sourceOrientedInvariantCoordinateMap d n) := by
  intro p hp
  change sourceOrientedInvariantCoordinateMap d n p = 0
  apply (sourceMinkowskiToDotInvariantSubalgebraEquiv d n).injective
  have hmapMem :
      sourceMinkowskiToDotInvariantCoordinateEquiv d n p ∈
        algEquivMapIdeal
          (sourceMinkowskiToDotInvariantCoordinateEquiv d n)
          (sourceOrientedAlgebraicRelationIdeal d n) := by
    unfold algEquivMapIdeal
    rw [Ideal.mem_map_iff_of_surjective]
    · exact ⟨p, hp, rfl⟩
    · exact
        (sourceMinkowskiToDotInvariantCoordinateEquiv d n).toRingEquiv.surjective
  have hstdMem :
      sourceMinkowskiToDotInvariantCoordinateEquiv d n p ∈
        standardSOAlgebraicRelationIdeal (d + 1) n := by
    simpa [sourceOrientedRelationIdeal_transport_dot d n] using hmapMem
  have hstdKer :
      standardSOInvariantCoordinateMap (d + 1) n
          (sourceMinkowskiToDotInvariantCoordinateEquiv d n p) = 0 := by
    exact
      standardSOAlgebraicRelationIdeal_le_invariantCoordinateMap_ker
        (d + 1) n hstdMem
  have hcomm := sourceMinkowskiToDotInvariantCoordinateMap_commutes d n p
  simpa [hcomm, hstdKer]

end BHW
