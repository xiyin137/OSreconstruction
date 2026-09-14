/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeParametricContinuation





















noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Insert independent reflected-left and right parameters into the reduced
`2k + 1` Chapter V time-gap chart.

The reflected-left coordinates occur in reverse order and with a minus sign.
The bridge coordinate is zero, and the right coordinates retain their order
with a minus sign. The signs are the test-function pullback convention for the
chronological source translations. -/
def reflectedReducedTimeDisplacement
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜) :
    Fin (k + (k + 1)) → 𝕜 :=
  Fin.addCases
    (fun i => -u (Fin.castAdd k (Fin.rev i)))
    (Fin.cases 0 fun i => -u (Fin.natAdd k i))

@[simp] theorem reflectedReducedTimeDisplacement_left
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜)
    (i : Fin k) :
    reflectedReducedTimeDisplacement u (Fin.castAdd (k + 1) i) =
      -u (Fin.castAdd k (Fin.rev i)) := by
  simp [reflectedReducedTimeDisplacement]

@[simp] theorem reflectedReducedTimeDisplacement_bridge
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜) :
    reflectedReducedTimeDisplacement u
        (Fin.natAdd k (0 : Fin (k + 1))) = 0 := by
  simp [reflectedReducedTimeDisplacement]

@[simp] theorem reflectedReducedTimeDisplacement_right
    {𝕜 : Type*} [Neg 𝕜] [Zero 𝕜]
    {k : ℕ}
    (u : Fin (k + k) → 𝕜)
    (i : Fin k) :
    reflectedReducedTimeDisplacement u (Fin.natAdd k i.succ) =
      -u (Fin.natAdd k i) := by
  simp [reflectedReducedTimeDisplacement]

/-- Complex-linear version of the reduced reflected time displacement. -/
def reflectedReducedTimeDisplacementCLM (k : ℕ) :
    (Fin (k + k) → ℂ) →L[ℂ] (Fin (k + (k + 1)) → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    Fin.addCases
      (fun i =>
        -(ContinuousLinearMap.proj
          (Fin.castAdd k (Fin.rev i))))
      (fun r =>
        Fin.cases 0
          (fun i =>
            -(ContinuousLinearMap.proj
              (Fin.natAdd k i)))
          r)
      j

@[simp] theorem reflectedReducedTimeDisplacementCLM_apply
    {k : ℕ}
    (u : Fin (k + k) → ℂ) :
    reflectedReducedTimeDisplacementCLM k u =
      reflectedReducedTimeDisplacement u := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp [reflectedReducedTimeDisplacementCLM,
      reflectedReducedTimeDisplacement]
  · intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · simp [reflectedReducedTimeDisplacementCLM,
        reflectedReducedTimeDisplacement]
    · simp [reflectedReducedTimeDisplacementCLM,
        reflectedReducedTimeDisplacement]

end OSIIChapterV
end OSReconstruction
