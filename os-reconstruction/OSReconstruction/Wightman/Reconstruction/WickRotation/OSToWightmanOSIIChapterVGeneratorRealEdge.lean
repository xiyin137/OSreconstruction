/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIPositiveTimeHilbertRealEdge















noncomputable section

open Complex Set

namespace OSReconstruction
namespace OSIIChapterV

variable {d k n : ℕ} [NeZero d]

/-- A Hilbert-valued field has a positive-time source realization on a real
parameter region. -/
def HasPositiveTimeSourceRealEdge
    (OS : OsterwalderSchraderAxioms d)
    (field : (Fin k → ℂ) → OSHilbertSpace OS)
    (source :
      (Fin k → ℝ) →
        euclideanPositiveTimeSubmodule (d := d) n)
    (U : Set (Fin k → ℝ)) : Prop :=
  ∀ x, x ∈ U →
    field (fun a => (x a : ℂ)) =
      osiiPositiveTimeSingleVectorCLM OS n (source x)

namespace GeneratorIndex

variable {k : ℕ} (i : GeneratorIndex k)

/-- Real left field parameters selected by a global generator point. -/
def leftRealCoordinates
    (τ : Fin k → ℝ) :
    Fin (i.n - 1) → ℝ :=
  fun a => -τ (i.leftGlobalIndex a)

/-- Real right field parameters selected by a global generator point. -/
def rightRealCoordinates
    (τ : Fin k → ℝ) :
    Fin (i.m - 1) → ℝ :=
  fun b => τ (i.rightGlobalIndex b)

@[simp]
theorem splitCoordinatesCLM_positiveReal_left
    (τ : Fin k → ℝ) (a : Fin (i.n - 1)) :
    star ((i.splitCoordinatesCLM
      (osiiPositiveRealTimeEmbed τ)).2.1 a) =
        (i.leftRealCoordinates τ a : ℂ) := by
  simp [leftRealCoordinates, osiiPositiveRealTimeEmbed]

@[simp]
theorem splitCoordinatesCLM_positiveReal_bridge
    (τ : Fin k → ℝ) :
    (i.splitCoordinatesCLM
      (osiiPositiveRealTimeEmbed τ)).1 =
        (τ i.bridgeGlobalIndex : ℂ) := by
  rfl

@[simp]
theorem splitCoordinatesCLM_positiveReal_right
    (τ : Fin k → ℝ) (b : Fin (i.m - 1)) :
    (i.splitCoordinatesCLM
      (osiiPositiveRealTimeEmbed τ)).2.2 b =
        (i.rightRealCoordinates τ b : ℂ) := by
  rfl

end GeneratorIndex

/-- Positive real global coordinates lie in a generator domain whenever the
bridge is positive and the two extracted real field parameters lie in the
corresponding complex field domains. -/
theorem positiveRealTimeEmbed_mem_generatorSemigroupDomain
    (i : GeneratorIndex k)
    {U : Set (Fin (i.n - 1) → ℂ)}
    {V : Set (Fin (i.m - 1) → ℂ)}
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hleft :
      (fun a => (i.leftRealCoordinates τ a : ℂ)) ∈ U)
    (hright :
      (fun b => (i.rightRealCoordinates τ b : ℂ)) ∈ V) :
    osiiPositiveRealTimeEmbed τ ∈
      generatorSemigroupDomain i U V := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hbridge
  · change
      (fun a =>
        star ((i.splitCoordinatesCLM
          (osiiPositiveRealTimeEmbed τ)).2.1 a)) ∈ U
    simpa only [GeneratorIndex.splitCoordinatesCLM_positiveReal_left] using
      hleft
  · simpa only [GeneratorIndex.splitCoordinatesCLM_positiveReal_right] using
      hright

/-- The genuine split generator recovers its exact zero-diagonal Schwinger
source on the positive real edge using only the original OS axioms. -/
theorem generatorSemigroupPairing_positiveReal_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (i : GeneratorIndex k)
    (left : (Fin (i.n - 1) → ℂ) → OSHilbertSpace OS)
    (right : (Fin (i.m - 1) → ℂ) → OSHilbertSpace OS)
    (leftSource :
      (Fin (i.n - 1) → ℝ) →
        euclideanPositiveTimeSubmodule (d := d) i.n)
    (rightSource :
      (Fin (i.m - 1) → ℝ) →
        euclideanPositiveTimeSubmodule (d := d) i.m)
    {U : Set (Fin (i.n - 1) → ℝ)}
    {V : Set (Fin (i.m - 1) → ℝ)}
    (hleftEdge :
      HasPositiveTimeSourceRealEdge OS left leftSource U)
    (hrightEdge :
      HasPositiveTimeSourceRealEdge OS right rightSource V)
    (τ : Fin k → ℝ)
    (hbridge : 0 < τ i.bridgeGlobalIndex)
    (hleft : i.leftRealCoordinates τ ∈ U)
    (hright : i.rightRealCoordinates τ ∈ V) :
    osiiSemigroupMixedHilbertPairing OS left right
        (i.splitCoordinatesCLM (osiiPositiveRealTimeEmbed τ)) =
      OS.S (i.n + i.m)
        (ZeroDiagonalSchwartz.ofClassical
          ((leftSource (i.leftRealCoordinates τ)).1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (τ i.bridgeGlobalIndex)
              (rightSource (i.rightRealCoordinates τ)).1))) := by
  have hleftField :=
    hleftEdge (i.leftRealCoordinates τ) hleft
  have hrightField :=
    hrightEdge (i.rightRealCoordinates τ) hright
  change
    @inner ℂ (OSHilbertSpace OS) _
      (left (star (i.splitCoordinatesCLM
        (osiiPositiveRealTimeEmbed τ)).2.1))
      (osiiOriginalOSHilbertComplex OS
        (i.splitCoordinatesCLM (osiiPositiveRealTimeEmbed τ)).1
        (right (i.splitCoordinatesCLM
          (osiiPositiveRealTimeEmbed τ)).2.2)) = _
  have hleftCoordinates :
      star (i.splitCoordinatesCLM
        (osiiPositiveRealTimeEmbed τ)).2.1 =
        fun a => (i.leftRealCoordinates τ a : ℂ) := by
    ext a
    exact GeneratorIndex.splitCoordinatesCLM_positiveReal_left i τ a
  have hrightCoordinates :
      (i.splitCoordinatesCLM (osiiPositiveRealTimeEmbed τ)).2.2 =
        fun b => (i.rightRealCoordinates τ b : ℂ) := by
    ext b
    exact GeneratorIndex.splitCoordinatesCLM_positiveReal_right i τ b
  rw [hleftCoordinates, hrightCoordinates,
    GeneratorIndex.splitCoordinatesCLM_positiveReal_bridge,
    hleftField, hrightField]
  exact osiiOriginalOSPositiveTimeSemigroupPairing_ofReal_eq_schwinger
    OS i.n i.m (τ i.bridgeGlobalIndex) hbridge
    (leftSource (i.leftRealCoordinates τ))
    (rightSource (i.rightRealCoordinates τ))

end OSIIChapterV
end OSReconstruction
