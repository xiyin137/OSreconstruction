import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketTimeShell

/-!
# Anchored packet carriers with a retained lower bound

The target-and-hub moving-slice argument needs the common packet carrier to
remember that every time coordinate lies above the packet anchor.  The
standard zero-tail packet construction has this property, but the older
packet interface intentionally forgot it.

This file retains that one extra geometric fact without strengthening the
general `AnchoredPacketTimeShellFamilyData` API used elsewhere.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- An anchored packet whose selected common time carrier lies
coordinatewise above its packet anchor. -/
structure LowerAnchoredPacketTimeShellFamilyData
    (I : Section43ProductTimeApproximateIdentity k)
    (anchor : Fin k → ℝ) where
  packet : AnchoredPacketTimeShellFamilyData (d := d) I anchor
  tailStart_eq_zero : packet.carrierData.tailStart = 0
  anchor_le_carrier :
    ∀ τ ∈ packet.carrierData.carrier, ∀ i, anchor i ≤ τ i

/-- Every strict-positive packet anchor admits a zero-tail packet retaining
the coordinatewise lower-bound property. -/
theorem nonempty_lowerAnchoredPacketTimeShellFamilyData
    (I : Section43ProductTimeApproximateIdentity k)
    (anchor : Fin k → ℝ)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion k) :
    Nonempty
      (LowerAnchoredPacketTimeShellFamilyData
        (d := d) I anchor) := by
  obtain ⟨C, hC_zero, hC_lower⟩ :=
    I.exists_anchoredCompactTimeCarrierData_zeroTail_lower
      anchor hanchor
  obtain ⟨partition⟩ :=
    nonempty_initialBaseTimeCarrierPartitionData
      (d := d) C.carrier C.carrier_compact C.carrier_positive
  let packet : AnchoredPacketTimeShellFamilyData (d := d) I anchor := {
    anchor_positive := hanchor
    carrierData := C
    partition := partition }
  exact
    ⟨{
      packet := packet
      tailStart_eq_zero := hC_zero
      anchor_le_carrier := hC_lower }⟩

end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
