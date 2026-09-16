import ReverseBridge
import OSReconstruction.Wightman.Reconstruction.Main

/-!
Proofs for the standard Comparator. The independent records are equivalent to
the production records; the family of distributions is preserved in both
directions. No theorem declaration from `Challenge` is imported here.
-/

noncomputable section
namespace OSReconstructionAudit

/-- The qualitative audit statement has exactly the production hypotheses
and conclusion after the record adapters. -/
theorem eToR_iff {d : ℕ} [NeZero d] :
    EToR d ↔ OSReconstruction.EToRStatement d := by
  constructor
  · intro h A growth
    obtain ⟨W, pair⟩ := h (OS.ofProduction A) (arityLinearGrowth.ofProduction growth)
    exact ⟨W.toProduction, (wickPair_iff _ _).mp pair⟩
  · intro h A growth
    obtain ⟨W, pair⟩ := h A.toProduction growth.toProduction
    exact ⟨Wightman.ofProduction W, (wickPair_iff _ _).mpr pair⟩

/-- The quantitative equivalence retains the output estimate and uniqueness
among all Wick-paired distribution families. -/
theorem eToROSII_iff {d : ℕ} [NeZero d] :
    EToROSII d ↔ OSReconstruction.EToROSIIStatement d := by
  constructor
  · intro h A growth
    obtain ⟨W, pair, bound, unique⟩ :=
      h (OS.ofProduction A) (originalGrowth.ofProduction growth)
    refine ⟨W.toProduction, (wickPair_iff _ _).mp pair,
      (outputGrowth_iff _ _).mp bound, ?_⟩
    intro V hV
    exact unique V ((wickPair_iff _ _).mpr hV)
  · intro h A growth
    obtain ⟨W, pair, bound, unique⟩ := h A.toProduction growth.toProduction
    refine ⟨Wightman.ofProduction W, (wickPair_iff _ _).mpr pair,
      (outputGrowth_iff _ _).mpr bound, ?_⟩
    intro V hV
    exact unique V ((wickPair_iff _ _).mp hV)

theorem e_to_r {d : ℕ} [NeZero d] : EToR d :=
  eToR_iff.mpr OSReconstruction.e_to_r_specification

theorem e_to_r_osii {d : ℕ} [NeZero d] : EToROSII d :=
  eToROSII_iff.mpr OSReconstruction.e_to_r_osii_specification

/-- The fixed independent constructor gives exactly the original reverse
contract, including equality with the actual production Schwinger family. -/
theorem rToE_iff {d : ℕ} [NeZero d] :
    RToE d ↔ OSReconstruction.RToEStatement d constructSchwingerFunctions := by
  constructor
  · intro h W
    obtain ⟨A, identity, pair⟩ := h (Wightman.ofProduction W)
    refine ⟨A.toProduction, ?_, (wickPair_iff _ _).mp pair⟩
    change A.S = constructSchwingerFunctions W
    simpa only [constructSchwinger_eq, Wightman.toProduction_ofProduction] using identity
  · intro h W
    obtain ⟨A, identity, pair⟩ := h W.toProduction
    exact ⟨OS.ofProduction A, identity.trans (constructSchwinger_eq W).symm,
      (wickPair_iff _ _).mpr pair⟩

theorem r_to_e {d : ℕ} [NeZero d] : RToE d :=
  rToE_iff.mpr OSReconstruction.r_to_e_specification

end OSReconstructionAudit
