/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedSpatialDensity












noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction

/-- Spatial gap coordinates of the reflected self-pair of an `r`-gap
source.  The middle gap has zero spatial component. -/
def osiiEquation629ReflectedSelfPairSpatialBlocks
    (d r : Nat)
    (x : Fin (r * d) -> Real) :
    Fin (r + (r + 1)) -> Fin d -> Real :=
  Fin.append
    (fun i mu => -x (finProdFinEquiv (Fin.rev i, mu)))
    (Fin.cons 0 fun i mu => x (finProdFinEquiv (i, mu)))

/-- Flat-coordinate form of the reflected spatial self-pair. -/
def osiiEquation629ReflectedSelfPairSpatialPoint
    (d r : Nat)
    (x : Fin (r * d) -> Real) :
    Fin ((r + (r + 1)) * d) -> Real :=
  flattenCLEquivReal (r + (r + 1)) d
    (osiiEquation629ReflectedSelfPairSpatialBlocks d r x)

@[simp]
theorem osiiEquation629ReflectedSelfPairSpatialBlocks_left
    (d r : Nat)
    (x : Fin (r * d) -> Real)
    (i : Fin r) (mu : Fin d) :
    osiiEquation629ReflectedSelfPairSpatialBlocks d r x
        (Fin.castAdd (r + 1) i) mu =
      -x (finProdFinEquiv (Fin.rev i, mu)) := by
  simp [osiiEquation629ReflectedSelfPairSpatialBlocks]

@[simp]
theorem osiiEquation629ReflectedSelfPairSpatialBlocks_bridge
    (d r : Nat)
    (x : Fin (r * d) -> Real)
    (mu : Fin d) :
    osiiEquation629ReflectedSelfPairSpatialBlocks d r x
        (Fin.natAdd r (0 : Fin (r + 1))) mu = 0 := by
  simp [osiiEquation629ReflectedSelfPairSpatialBlocks]

@[simp]
theorem osiiEquation629ReflectedSelfPairSpatialBlocks_right
    (d r : Nat)
    (x : Fin (r * d) -> Real)
    (i : Fin r) (mu : Fin d) :
    osiiEquation629ReflectedSelfPairSpatialBlocks d r x
        (Fin.natAdd r i.succ) mu =
      x (finProdFinEquiv (i, mu)) := by
  simp [osiiEquation629ReflectedSelfPairSpatialBlocks]

/-- Reflection, reversal, duplication, and insertion of the zero bridge do
not increase the flat finite-coordinate sup norm. -/
theorem norm_osiiEquation629ReflectedSelfPairSpatialPoint_le
    (d r : Nat)
    (x : Fin (r * d) -> Real) :
    ‖osiiEquation629ReflectedSelfPairSpatialPoint d r x‖ <= ‖x‖ := by
  rw [osiiEquation629ReflectedSelfPairSpatialPoint,
    flattenCLEquivReal_norm_eq]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  refine Fin.addCases ?_ ?_
  · intro i
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
    intro mu
    simp only [osiiEquation629ReflectedSelfPairSpatialBlocks_left, norm_neg]
    exact norm_le_pi_norm x (finProdFinEquiv (Fin.rev i, mu))
  · refine Fin.cases ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
      intro mu
      simp only [osiiEquation629ReflectedSelfPairSpatialBlocks_bridge,
        norm_zero]
      exact norm_nonneg x
    · intro i
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
      intro mu
      simp only [osiiEquation629ReflectedSelfPairSpatialBlocks_right]
      exact norm_le_pi_norm x (finProdFinEquiv (i, mu))

namespace OSIIChapterV
namespace GeneratorIndex

variable {k : Nat}

/-- Internal spatial coordinates of the left absolute block, before forming
its reflected self-pair.  Reflection and chronological reversal belong to
`osiiEquation629ReflectedSelfPairSpatialPoint` and must occur exactly once. -/
def leftSpatialCoordinates
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    Fin ((i.n - 1) * d) -> Real :=
  flattenCLEquivReal (i.n - 1) d fun a mu =>
    x (finProdFinEquiv (i.leftGlobalIndex (Fin.rev a), mu))

/-- Spatial gaps entering the right Hilbert source. -/
def rightSpatialCoordinates
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    Fin ((i.m - 1) * d) -> Real :=
  flattenCLEquivReal (i.m - 1) d fun b mu =>
    x (finProdFinEquiv (i.rightGlobalIndex b, mu))

theorem norm_leftSpatialCoordinates_le
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    ‖i.leftSpatialCoordinates d x‖ <= ‖x‖ := by
  rw [leftSpatialCoordinates, flattenCLEquivReal_norm_eq]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro mu
  exact norm_le_pi_norm x
    (finProdFinEquiv (i.leftGlobalIndex (Fin.rev a), mu))

theorem norm_rightSpatialCoordinates_le
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    ‖i.rightSpatialCoordinates d x‖ <= ‖x‖ := by
  rw [rightSpatialCoordinates, flattenCLEquivReal_norm_eq]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro b
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro mu
  exact norm_le_pi_norm x (finProdFinEquiv (i.rightGlobalIndex b, mu))

/-- Left reflected self-pair spatial point at a generator split. -/
def leftReflectedSelfPairSpatialPoint
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    Fin (((i.n - 1) + ((i.n - 1) + 1)) * d) -> Real :=
  osiiEquation629ReflectedSelfPairSpatialPoint d (i.n - 1)
    (i.leftSpatialCoordinates d x)

/-- Right reflected self-pair spatial point at a generator split. -/
def rightReflectedSelfPairSpatialPoint
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    Fin (((i.m - 1) + ((i.m - 1) + 1)) * d) -> Real :=
  osiiEquation629ReflectedSelfPairSpatialPoint d (i.m - 1)
    (i.rightSpatialCoordinates d x)

theorem norm_leftReflectedSelfPairSpatialPoint_le
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    ‖i.leftReflectedSelfPairSpatialPoint d x‖ <= ‖x‖ :=
  (norm_osiiEquation629ReflectedSelfPairSpatialPoint_le
      d (i.n - 1) (i.leftSpatialCoordinates d x)).trans
    (i.norm_leftSpatialCoordinates_le d x)

theorem norm_rightReflectedSelfPairSpatialPoint_le
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    ‖i.rightReflectedSelfPairSpatialPoint d x‖ <= ‖x‖ :=
  (norm_osiiEquation629ReflectedSelfPairSpatialPoint_le
      d (i.m - 1) (i.rightSpatialCoordinates d x)).trans
    (i.norm_rightSpatialCoordinates_le d x)

end GeneratorIndex
end OSIIChapterV
end OSReconstruction
