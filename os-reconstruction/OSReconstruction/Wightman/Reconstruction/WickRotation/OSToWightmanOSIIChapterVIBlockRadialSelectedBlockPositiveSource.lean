/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelCovariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPositiveSource

















noncomputable section

open Matrix
open scoped Classical

namespace OSReconstruction

/-- Euclidean parity fixes the distinguished time coordinate and reverses all
orthogonal spatial coordinates. -/
def osiiStep4EuclideanParityMatrix (d : Nat) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) Real :=
  Matrix.diagonal fun mu => if mu = 0 then 1 else -1

theorem osiiStep4EuclideanParityMatrix_orthogonal (d : Nat) :
    (osiiStep4EuclideanParityMatrix d).transpose *
        osiiStep4EuclideanParityMatrix d = 1 := by
  rw [show (osiiStep4EuclideanParityMatrix d).transpose =
      osiiStep4EuclideanParityMatrix d by
    simp [osiiStep4EuclideanParityMatrix]]
  rw [osiiStep4EuclideanParityMatrix,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = 0 <;> simp [hi]
  · simp [Matrix.diagonal, hij]

@[simp] theorem osiiStep4EuclideanParityMatrix_mulVec_apply
    (d : Nat) (x : SpacetimeDim d) (mu : Fin (d + 1)) :
    (osiiStep4EuclideanParityMatrix d).mulVec x mu =
      if mu = 0 then x mu else -x mu := by
  simp [osiiStep4EuclideanParityMatrix, Matrix.mulVec_diagonal]

@[simp] theorem osiiStep4EuclideanParityMatrix_mulVec_zero
    (d : Nat) (x : SpacetimeDim d) :
    (osiiStep4EuclideanParityMatrix d).mulVec x 0 = x 0 := by
  simp

theorem osiiStep4EuclideanParityMatrix_mulVec_involutive
    (d : Nat) (x : SpacetimeDim d) :
    (osiiStep4EuclideanParityMatrix d).mulVec
        ((osiiStep4EuclideanParityMatrix d).mulVec x) = x := by
  ext mu
  by_cases hmu : mu = 0 <;> simp [hmu]

/-- Index of the distinguished block in a chain with `n` blocks before it and
`m` blocks after it. -/
def osiiStep4SelectedBlockIndex (n m : Nat) : Fin (n + 1 + m) :=
  Fin.castAdd m (Fin.last n)

@[simp] theorem osiiStep4SelectedBlockIndex_val (n m : Nat) :
    (osiiStep4SelectedBlockIndex n m).val = n := by
  simp [osiiStep4SelectedBlockIndex]

/-- The `i`th left block when the blocks before the selected one are read from
the selected block outwards. -/
def osiiStep4ReversedBeforeBlockIndex
    (n m : Nat) (i : Fin n) : Fin (n + 1 + m) :=
  Fin.cast (Nat.add_assoc n 1 m).symm
    (Fin.castAdd (1 + m) (Fin.rev i))

/-- The `i`th block after the selected block. -/
def osiiStep4AfterBlockIndex
    (n m : Nat) (i : Fin m) : Fin (n + 1 + m) :=
  Fin.natAdd (n + 1) i

/-- Restrict a flattened full chain to its selected spacetime block. -/
def osiiStep4SelectedRealBlock
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real) : Fin q -> Real :=
  fun mu => x (finProdFinEquiv (osiiStep4SelectedBlockIndex n m, mu))

/-- Reverse the blocks before the selected one and apply Euclidean parity to
each spacetime block. -/
def osiiStep4ParityReversedBeforeRealBlocks
    (d n m : Nat)
    (x : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    Fin (n * (d + 1)) -> Real :=
  flattenCLEquivReal n (d + 1) fun i =>
    (osiiStep4EuclideanParityMatrix d).mulVec fun mu =>
      x (finProdFinEquiv (osiiStep4ReversedBeforeBlockIndex n m i, mu))

/-- Restrict a flattened full chain to the blocks after the selected one. -/
def osiiStep4AfterRealBlocks
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real) : Fin (m * q) -> Real :=
  flattenCLEquivReal m q fun i mu =>
    x (finProdFinEquiv (osiiStep4AfterBlockIndex n m i, mu))

@[simp] theorem osiiStep4SelectedRealBlock_apply
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real) (mu : Fin q) :
    osiiStep4SelectedRealBlock n m q x mu =
      x (finProdFinEquiv (osiiStep4SelectedBlockIndex n m, mu)) := by
  rfl

@[simp] theorem osiiStep4ParityReversedBeforeRealBlocks_apply
    (d n m : Nat)
    (x : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (i : Fin n) (mu : Fin (d + 1)) :
    osiiStep4ParityReversedBeforeRealBlocks d n m x
        (finProdFinEquiv (i, mu)) =
      (osiiStep4EuclideanParityMatrix d).mulVec
        (fun nu => x (finProdFinEquiv
          (osiiStep4ReversedBeforeBlockIndex n m i, nu))) mu := by
  simp [osiiStep4ParityReversedBeforeRealBlocks]

@[simp] theorem osiiStep4AfterRealBlocks_apply
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real)
    (i : Fin m) (mu : Fin q) :
    osiiStep4AfterRealBlocks n m q x (finProdFinEquiv (i, mu)) =
      x (finProdFinEquiv (osiiStep4AfterBlockIndex n m i, mu)) := by
  simp [osiiStep4AfterRealBlocks]

/-- Half of the selected real block. -/
def osiiStep4SelectedRealBlockHalf
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real) : Fin q -> Real :=
  (2 : Real)⁻¹ • osiiStep4SelectedRealBlock n m q x

/-- Endpoint center for the reflected left source. -/
def osiiStep4SelectedBlockLeftEndpointCenter
    (d n m : Nat)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) : SpacetimeDim d :=
  (osiiStep4EuclideanParityMatrix d).mulVec
    (osiiStep4SelectedRealBlockHalf n m (d + 1) center)

/-- Endpoint center for the right source. -/
def osiiStep4SelectedBlockRightEndpointCenter
    (d n m : Nat)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) : SpacetimeDim d :=
  osiiStep4SelectedRealBlockHalf n m (d + 1) center

/-- Fixed imaginary endpoint carried by the reflected left radial factor. -/
def osiiStep4SelectedBlockLeftEndpointImag
    (d n m : Nat)
    (y y' : Fin ((n + 1 + m) * (d + 1)) -> Real) : SpacetimeDim d :=
  (osiiStep4EuclideanParityMatrix d).mulVec
    (osiiStep4SelectedRealBlock n m (d + 1) y -
      osiiStep4SelectedRealBlock n m (d + 1) y')

/-- Fixed imaginary endpoint carried by the right radial factor. -/
def osiiStep4SelectedBlockRightEndpointImag
    (d n m : Nat)
    (y' : Fin ((n + 1 + m) * (d + 1)) -> Real) : SpacetimeDim d :=
  osiiStep4SelectedRealBlock n m (d + 1) y'

theorem osiiStep4SelectedBlockEndpointCenter_sum
    (d n m : Nat)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    (osiiStep4EuclideanParityMatrix d).mulVec
          (osiiStep4SelectedBlockLeftEndpointCenter d n m center) +
        osiiStep4SelectedBlockRightEndpointCenter d n m center =
      osiiStep4SelectedRealBlock n m (d + 1) center := by
  rw [osiiStep4SelectedBlockLeftEndpointCenter,
    osiiStep4SelectedBlockRightEndpointCenter,
    osiiStep4EuclideanParityMatrix_mulVec_involutive]
  ext mu
  simp [osiiStep4SelectedRealBlockHalf]
  ring

theorem osiiStep4SelectedBlockEndpointImag_sum
    (d n m : Nat)
    (y y' : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    (osiiStep4EuclideanParityMatrix d).mulVec
          (osiiStep4SelectedBlockLeftEndpointImag d n m y y') +
        osiiStep4SelectedBlockRightEndpointImag d n m y' =
      osiiStep4SelectedRealBlock n m (d + 1) y := by
  rw [osiiStep4SelectedBlockLeftEndpointImag,
    osiiStep4SelectedBlockRightEndpointImag,
    osiiStep4EuclideanParityMatrix_mulVec_involutive]
  ext mu
  simp

/-- The two endpoint radial factors are exactly the two factors inside the
selected-block convolution integrand. -/
theorem osiiStep4SelectedBlockEndpointRadialProduct_eq_integrand
    (d n m : Nat) (rho : Real)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (u v : SpacetimeDim d) :
    osiiStep4ComplexBlockRadialG (d + 1) rho
        (osiiStep4ComplexOfRealImag
          (u - osiiStep4SelectedBlockLeftEndpointCenter d n m center)
          (osiiStep4SelectedBlockLeftEndpointImag d n m y y')) *
      osiiStep4ComplexBlockRadialG (d + 1) rho
        (osiiStep4ComplexOfRealImag
          (v - osiiStep4SelectedBlockRightEndpointCenter d n m center)
          (osiiStep4SelectedBlockRightEndpointImag d n m y')) =
    osiiStep4ComplexBlockPartialConvolutionIntegrand (d + 1) rho
      (osiiStep4ComplexOfRealImag
        ((osiiStep4EuclideanParityMatrix d).mulVec u + v -
          osiiStep4SelectedRealBlock n m (d + 1) center)
        (osiiStep4SelectedRealBlock n m (d + 1) y))
      (osiiStep4SelectedRealBlock n m (d + 1) y')
      (v - osiiStep4SelectedBlockRightEndpointCenter d n m center) := by
  let P := osiiStep4EuclideanParityMatrix d
  let a := osiiStep4SelectedBlockLeftEndpointCenter d n m center
  let b := osiiStep4SelectedBlockRightEndpointCenter d n m center
  let etaL := osiiStep4SelectedBlockLeftEndpointImag d n m y y'
  let etaR := osiiStep4SelectedBlockRightEndpointImag d n m y'
  let c := osiiStep4SelectedRealBlock n m (d + 1) center
  let eta := osiiStep4SelectedRealBlock n m (d + 1) y
  have hc : P.mulVec a + b = c := by
    exact osiiStep4SelectedBlockEndpointCenter_sum d n m center
  have heta : P.mulVec etaL + etaR = eta := by
    exact osiiStep4SelectedBlockEndpointImag_sum d n m y y'
  have hreal :
      (P.mulVec u + v - c) - (v - b) = P.mulVec (u - a) := by
    rw [← hc, Matrix.mulVec_sub]
    abel
  have himag : eta - etaR = P.mulVec etaL := by
    rw [← heta]
    abel
  have hfirst :
      osiiStep4ComplexOfRealImag (P.mulVec u + v - c) eta -
          osiiStep4ComplexOfRealImag (v - b) etaR =
        osiiStep4RealMatrixComplexAction P
          (osiiStep4ComplexOfRealImag (u - a) etaL) := by
    rw [osiiStep4RealMatrixComplexAction_ofRealImag]
    ext mu
    apply Complex.ext
    · simpa only [Pi.sub_apply, osiiStep4ComplexOfRealImag_re,
        Complex.sub_re] using congrFun hreal mu
    · simpa only [Pi.sub_apply, osiiStep4ComplexOfRealImag_im,
        Complex.sub_im] using congrFun himag mu
  change
    osiiStep4ComplexBlockRadialG (d + 1) rho
        (osiiStep4ComplexOfRealImag (u - a) etaL) *
      osiiStep4ComplexBlockRadialG (d + 1) rho
        (osiiStep4ComplexOfRealImag (v - b) etaR) =
      osiiStep4ComplexBlockRadialG (d + 1) rho
          (osiiStep4ComplexOfRealImag (P.mulVec u + v - c) eta -
            osiiStep4ComplexOfRealImag (v - b) etaR) *
        osiiStep4ComplexBlockRadialG (d + 1) rho
          (osiiStep4ComplexOfRealImag (v - b) etaR)
  rw [hfirst,
    osiiStep4ComplexBlockRadialG_realMatrix_invariant P
      (osiiStep4EuclideanParityMatrix_orthogonal d)]

@[simp] theorem osiiStep4SelectedRealBlockHalf_apply
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real) (mu : Fin q) :
    osiiStep4SelectedRealBlockHalf n m q x mu =
      (2 : Real)⁻¹ * x (finProdFinEquiv
        (osiiStep4SelectedBlockIndex n m, mu)) := by
  simp [osiiStep4SelectedRealBlockHalf]

@[simp] theorem osiiStep4SelectedBlockLeftEndpointCenter_zero
    (d n m : Nat)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    osiiStep4SelectedBlockLeftEndpointCenter d n m center 0 =
      (2 : Real)⁻¹ * center (finProdFinEquiv
        (osiiStep4SelectedBlockIndex n m, (0 : Fin (d + 1)))) := by
  simp [osiiStep4SelectedBlockLeftEndpointCenter]

@[simp] theorem osiiStep4SelectedBlockRightEndpointCenter_zero
    (d n m : Nat)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    osiiStep4SelectedBlockRightEndpointCenter d n m center 0 =
      (2 : Real)⁻¹ * center (finProdFinEquiv
        (osiiStep4SelectedBlockIndex n m, (0 : Fin (d + 1)))) := by
  simp [osiiStep4SelectedBlockRightEndpointCenter]

theorem osiiStep4SelectedBlockLeftEndpointCenter_time_lower
    (d n m : Nat) {rho : Real} (hrho : 0 < rho)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    rho / 4 <=
      osiiStep4SelectedBlockLeftEndpointCenter d n m center 0 := by
  have hc := hcenter (osiiStep4SelectedBlockIndex n m)
  rw [osiiStep4SelectedBlockLeftEndpointCenter_zero]
  norm_num at ⊢ hc
  nlinarith

theorem osiiStep4SelectedBlockRightEndpointCenter_time_lower
    (d n m : Nat) {rho : Real} (hrho : 0 < rho)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    rho / 4 <=
      osiiStep4SelectedBlockRightEndpointCenter d n m center 0 := by
  have hc := hcenter (osiiStep4SelectedBlockIndex n m)
  rw [osiiStep4SelectedBlockRightEndpointCenter_zero]
  norm_num at ⊢ hc
  nlinarith

theorem osiiStep4ParityReversedBeforeRealBlocks_time_lower
    (d n m : Nat) {rho : Real}
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (i : Fin n) :
    rho / 2 <= osiiStep4ParityReversedBeforeRealBlocks d n m center
      (finProdFinEquiv (i, (0 : Fin (d + 1)))) := by
  simpa using hcenter (osiiStep4ReversedBeforeBlockIndex n m i)

theorem osiiStep4AfterRealBlocks_time_lower
    (d n m : Nat) {rho : Real}
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (i : Fin m) :
    rho / 2 <= osiiStep4AfterRealBlocks n m (d + 1) center
      (finProdFinEquiv (i, (0 : Fin (d + 1)))) := by
  simpa using hcenter (osiiStep4AfterBlockIndex n m i)

/-- Positive-time source built from the blocks before the selected one and
the left radial factor.  It has exactly `n + 1` absolute points. -/
noncomputable def osiiStep4SelectedBlockLeftPositiveTimeSource
    (d n m : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    euclideanPositiveTimeSubmodule (d := d) (n + 1) :=
  osiiStep4RadialEndpointPositiveTimeSource d n hrho
    (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
    (osiiStep4SelectedBlockLeftEndpointImag d n m y y')
    (osiiStep4ParityReversedBeforeRealBlocks d n m center)
    (osiiStep4ParityReversedBeforeRealBlocks d n m y)
    (osiiStep4ParityReversedBeforeRealBlocks d n m y')
    (osiiStep4SelectedBlockLeftEndpointCenter_time_lower
      d n m hrho center hcenter)
    (osiiStep4ParityReversedBeforeRealBlocks_time_lower
      d n m center hcenter)

/-- Positive-time source built from the blocks after the selected one and the
right radial factor.  It has exactly `m + 1` absolute points. -/
noncomputable def osiiStep4SelectedBlockRightPositiveTimeSource
    (d n m : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    euclideanPositiveTimeSubmodule (d := d) (m + 1) :=
  osiiStep4RadialEndpointPositiveTimeSource d m hrho
    (osiiStep4SelectedBlockRightEndpointCenter d n m center)
    (osiiStep4SelectedBlockRightEndpointImag d n m y')
    (osiiStep4AfterRealBlocks n m (d + 1) center)
    (osiiStep4AfterRealBlocks n m (d + 1) y)
    (osiiStep4AfterRealBlocks n m (d + 1) y')
    (osiiStep4SelectedBlockRightEndpointCenter_time_lower
      d n m hrho center hcenter)
    (osiiStep4AfterRealBlocks_time_lower d n m center hcenter)

end OSReconstruction
