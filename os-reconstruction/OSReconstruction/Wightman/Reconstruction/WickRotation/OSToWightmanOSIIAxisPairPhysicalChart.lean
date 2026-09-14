/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceAdapter




















noncomputable section

open Complex Topology
open scoped Classical BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Complex Wick rotation on one displacement block. -/
def osiiAxisPairWickBlock
    (z : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  Fin.cases (Complex.I * z 0) (fun j => z (Fin.succ j))

/-- Inverse Wick rotation on one complex displacement block. -/
def osiiAxisPairInverseWickBlock
    (w : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  Fin.cases (-Complex.I * w 0) (fun j => w (Fin.succ j))

/-- Wick rotation followed by inverse Wick rotation is the identity. -/
@[simp] theorem osiiAxisPairWickBlock_inverseWickBlock
    (w : Fin (d + 1) → ℂ) :
    osiiAxisPairWickBlock (osiiAxisPairInverseWickBlock w) = w := by
  funext ν
  refine Fin.cases ?_ ?_ ν
  · simp only [osiiAxisPairWickBlock, osiiAxisPairInverseWickBlock,
      Fin.cases_zero]
    rw [← mul_assoc]
    simp
  · intro j
    simp [osiiAxisPairWickBlock, osiiAxisPairInverseWickBlock]

private noncomputable def osiiAxisPairWickTimeUnit : ℂˣ :=
  Units.mk0 Complex.I (by simp)

/-- Complex Wick rotation is a continuous complex-linear equivalence. -/
noncomputable def osiiAxisPairWickBlockCLE :
    (Fin (d + 1) → ℂ) ≃L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun ν =>
    if _hν : ν = 0 then
      ContinuousLinearEquiv.smulLeft osiiAxisPairWickTimeUnit
    else
      ContinuousLinearEquiv.refl ℂ ℂ

@[simp] theorem osiiAxisPairWickBlockCLE_apply
    (z : Fin (d + 1) → ℂ) :
    osiiAxisPairWickBlockCLE z = osiiAxisPairWickBlock z := by
  funext ν
  refine Fin.cases ?_ ?_ ν
  · simp [osiiAxisPairWickBlockCLE, osiiAxisPairWickTimeUnit,
      osiiAxisPairWickBlock]
  · intro j
    simp [osiiAxisPairWickBlockCLE, osiiAxisPairWickBlock]

@[simp] theorem osiiAxisPairWickBlockCLE_symm_apply
    (w : Fin (d + 1) → ℂ) :
    osiiAxisPairWickBlockCLE.symm w =
      osiiAxisPairInverseWickBlock w := by
  apply osiiAxisPairWickBlockCLE.injective
  simp

/-- Complex Euclidean perturbation of a Wick-rotated block relative to a real
Euclidean center. -/
def osiiAxisPairWickPerturbation
    (ξ : Fin (d + 1) → ℝ)
    (w : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  osiiAxisPairInverseWickBlock w - fun ν => (ξ ν : ℂ)

/-- The inverse-Wick coordinate of a real Wick-rotated point is its complex
Euclidean embedding. -/
theorem osiiAxisPairInverseWickBlock_wickRotatePoint
    (y : Fin (d + 1) → ℝ) :
    osiiAxisPairInverseWickBlock (wickRotatePoint y) =
      fun ν => (y ν : ℂ) := by
  funext ν
  refine Fin.cases ?_ ?_ ν
  · change -Complex.I * (Complex.I * (y 0 : ℂ)) = (y 0 : ℂ)
    exact neg_I_mul_I_mul (y 0 : ℂ)
  · intro j
    simp [osiiAxisPairInverseWickBlock, wickRotatePoint]

/-- Project one complex physical block to its canonical real Euclidean Wick
slice. -/
def osiiAxisPairWickProjection
    (w : Fin (d + 1) → ℂ) : Fin (d + 1) → ℝ :=
  fun ν => (osiiAxisPairInverseWickBlock w ν).re

/-- A checked local physical chart around one positive Euclidean center at a
fixed auxiliary slope. -/
structure OSIIAxisPairPhysicalChart
    (d : ℕ) [NeZero d]
    (T : ℝ) (ξ : Fin (d + 1) → ℝ) where
  hT : 0 < T
  hξ0 : 0 < ξ 0
  eta : ℝ
  eta_pos : 0 < eta
  eta_argSum :
    (Fintype.card (osiiAxisPairIndex d) : ℝ) * Real.arctan eta <
      Real.pi / 2
  radius : ℝ
  radius_pos : 0 < radius
  coeff_narrowSector :
    ∀ ζ : Fin (d + 1) → ℂ,
      (∀ ν : Fin (d + 1), ‖ζ ν‖ < radius) →
        osiiAxisPairCoeffMap T ξ ζ ∈
          osiiAxisPairNarrowSector (d := d) eta
  logMap_differentiable :
    DifferentiableOn ℂ
      (fun ζ : Fin (d + 1) → ℂ =>
        osiiAxisPairLogCoeffMap T ξ ζ)
      {ζ : Fin (d + 1) → ℂ |
        ∀ ν : Fin (d + 1), ‖ζ ν‖ < radius}
  logMap_mapsTo :
    Set.MapsTo
      (fun ζ : Fin (d + 1) → ℂ =>
        osiiAxisPairLogCoeffMap T ξ ζ)
      {ζ : Fin (d + 1) → ℂ |
        ∀ ν : Fin (d + 1), ‖ζ ν‖ < radius}
      (osiiAxisPairLogDomain (d := d))

namespace OSIIAxisPairPhysicalChart

/-- The one-block Minkowski carrier of a physical chart. -/
def carrier
    (C : OSIIAxisPairPhysicalChart d T ξ) :
    Set (Fin (d + 1) → ℂ) :=
  {w | ∀ ν : Fin (d + 1),
    ‖osiiAxisPairWickPerturbation ξ w ν‖ < C.radius}

/-- The chart's logarithmic axis-pair coordinate map. -/
def logMap
    (C : OSIIAxisPairPhysicalChart d T ξ)
    (w : Fin (d + 1) → ℂ) :
    osiiAxisPairIndex d → ℂ :=
  osiiAxisPairLogCoeffMap T ξ
    (osiiAxisPairWickPerturbation ξ w)

end OSIIAxisPairPhysicalChart

end OSReconstruction
