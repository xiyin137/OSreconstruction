/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformSchwartzDegree
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound











noncomputable section

open Complex Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

/-- The explicit flat Schwartz family controlling polynomially weighted L1
mass.  The decay exponent is the Euclidean volume integrable power. -/
def osiiSpatialPolynomialWeightedL1ExplicitFlatSeminorms
    (m p : Nat) : Finset (Nat × Nat) :=
  Finset.Iic (p + (m + 1), 0)

/-- The explicit flat coefficient controlling polynomially weighted L1 mass.
-/
noncomputable def osiiSpatialPolynomialWeightedL1ExplicitFlatConstant
    (m p : Nat) : Real :=
  let n := m + 1
  let J : Real := ∫ x : Fin m -> Real,
    (1 + ‖x‖) ^ (-(n : Real))
  2 ^ (p + n) * (1 + J)

theorem osiiSpatialPolynomialWeightedL1ExplicitFlatConstant_pos
    (m p : Nat) :
    0 < osiiSpatialPolynomialWeightedL1ExplicitFlatConstant m p := by
  let n := m + 1
  let J : Real := ∫ x : Fin m -> Real,
    (1 + ‖x‖) ^ (-(n : Real))
  have hJ : 0 <= J := by
    dsimp [J]
    exact integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
  change 0 < 2 ^ (p + n) * (1 + J)
  positivity

/-- The real and complex Schwartz seminorm bundles have the same evaluated
gauge on complex-valued tests.  This lets the real-coordinate transport
estimate feed the complex-linear Section-4.3 certificate without changing
indices. -/
theorem osiiSchwartzComplexFinsetSup_eq_real
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    (s : Finset (Nat × Nat))
    (phi : SchwartzMap E Complex) :
    s.sup (schwartzSeminormFamily Complex E Complex) phi =
      s.sup (schwartzSeminormFamily Real E Complex) phi := by
  rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  rfl

/-- The initial weight order of the explicit zero-derivative interval is
exactly its endpoint. -/
theorem schwartzSeminormWeightOrder_Iic_zero
    (p : Nat) :
    schwartzSeminormWeightOrder (Finset.Iic (p, 0)) = p := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact (Finset.mem_Iic.mp hj).1
  · apply Finset.le_sup
      (s := Finset.Iic (p, 0))
      (f := fun j : Nat × Nat => j.1)
      (b := (p, 0))
    simp

/-- The explicit weighted-L1 interval introduces no derivative order. -/
theorem schwartzSeminormDerivativeOrder_Iic_zero
    (p : Nat) :
    schwartzSeminormDerivativeOrder (Finset.Iic (p, 0)) = 0 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact (Finset.mem_Iic.mp hj).2
  · exact Nat.zero_le _

/-- The weighted flat L1 mass is controlled by the explicit initial
Schwartz interval, with no finite-family choice hidden in the statement. -/
theorem osiiSpatialPolynomialWeightedL1_le_explicitFlatSeminorms
    (m p : Nat)
    (phi : SchwartzMap (Fin m -> Real) Complex) :
    osiiSpatialPolynomialWeightedL1 p phi <=
      osiiSpatialPolynomialWeightedL1ExplicitFlatConstant m p *
        (osiiSpatialPolynomialWeightedL1ExplicitFlatSeminorms m p).sup
          (schwartzSeminormFamily Complex (Fin m -> Real) Complex) phi := by
  let n : Nat := m + 1
  let s : Finset (Nat × Nat) := Finset.Iic (p + n, 0)
  let decay : (Fin m -> Real) -> Real := fun x =>
    (1 + ‖x‖) ^ (-(n : Real))
  have hdecay_integrable : Integrable decay := by
    dsimp [decay, n]
    apply integrable_one_add_norm
    simp
  let J : Real := ∫ x : Fin m -> Real, decay x
  have hJ_nonneg : 0 <= J := by
    dsimp [J]
    exact integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
  let K : Real := 2 ^ (p + n) * (1 + J)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  change osiiSpatialPolynomialWeightedL1 p phi <=
    K * s.sup
      (schwartzSeminormFamily Complex (Fin m -> Real) Complex) phi
  let sem : Real :=
    s.sup (schwartzSeminormFamily Complex (Fin m -> Real) Complex) phi
  have hsem : 0 <= sem := apply_nonneg _ _
  have hpointwise : ∀ x : Fin m -> Real,
      (1 + ‖x‖) ^ p * ‖phi x‖ <=
        decay x * (2 ^ (p + n) * sem) := by
    intro x
    have hsch :
        (1 + ‖x‖) ^ (p + n) * ‖phi x‖ <=
          2 ^ (p + n) * sem := by
      dsimp [sem]
      change (1 + ‖x‖) ^ (p + n) * ‖phi x‖ <=
        2 ^ (p + n) *
          ((s.sup fun m => SchwartzMap.seminorm Complex m.1 m.2) phi)
      simpa [s] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := Complex) (m := (p + n, 0)) (k := p + n) (n := 0)
          le_rfl le_rfl phi x)
    rw [show decay x = (1 + ‖x‖) ^ (-(n : Real)) by rfl]
    rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
      le_div_iff₀' (by positivity), Real.rpow_natCast]
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hsch
  calc
    osiiSpatialPolynomialWeightedL1 p phi <=
        ∫ x : Fin m -> Real,
          decay x * (2 ^ (p + n) * sem) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x =>
          mul_nonneg (by positivity) (norm_nonneg (phi x))
      · exact hdecay_integrable.mul_const _
      · exact Filter.Eventually.of_forall hpointwise
    _ = 2 ^ (p + n) * J * sem := by
      rw [integral_mul_const]
      dsimp [J]
      ring
    _ <= K * sem := by
      apply mul_le_mul_of_nonneg_right _ hsem
      dsimp [K]
      have hpow : 0 <= (2 : Real) ^ (p + n) := pow_nonneg (by norm_num) _
      nlinarith

namespace OSIIEquation621WeightedL1Section43BoundData

/-- Source-native Section-4.3 weighted-L1 data.  Flattening preserves the
explicit flat seminorm indices; its operator-norm loss is retained in the
coefficient instead of selecting a new target family by continuity. -/
noncomputable def explicitIndexPreserving
    (d k p : Nat) :
    OSIIEquation621WeightedL1Section43BoundData d k p := by
  let m := k * d
  let s := osiiSpatialPolynomialWeightedL1ExplicitFlatSeminorms m p
  let K := osiiSpatialPolynomialWeightedL1ExplicitFlatConstant m p
  let e := (section43SpatialFlatCLE d k).symm
  let factor := schwartzCompEquivFinsetFactor e s
  let C := K * (factor + 1)
  have hK : 0 < K := by
    dsimp [K]
    exact osiiSpatialPolynomialWeightedL1ExplicitFlatConstant_pos m p
  have hfactor : 0 <= factor := by
    dsimp [factor]
    exact schwartzCompEquivFinsetFactor_nonneg e s
  refine {
    spatialSeminorms := s
    constant := C
    constant_pos := by
      dsimp [C]
      positivity
    bound := ?_ }
  intro chi
  let flat := section43SpatialFlatSchwartzCLE d k chi
  have hflat :
      osiiSpatialPolynomialWeightedL1 p flat <=
        K * s.sup
          (schwartzSeminormFamily Complex (Fin (k * d) -> Real) Complex)
          flat := by
    simpa [flat, m, s, K] using
      osiiSpatialPolynomialWeightedL1_le_explicitFlatSeminorms
        (k * d) p flat
  have htransport :
      s.sup
          (schwartzSeminormFamily Complex (Fin (k * d) -> Real) Complex)
          flat <=
        factor * s.sup
          (schwartzSeminormFamily Complex
            (Section43SpatialSpace d k) Complex) chi := by
    rw [osiiSchwartzComplexFinsetSup_eq_real,
      osiiSchwartzComplexFinsetSup_eq_real]
    change s.sup
        (schwartzSeminormFamily Real (Fin (k * d) -> Real) Complex)
        ((SchwartzMap.compCLMOfContinuousLinearEquiv Complex e) chi) <=
      factor * s.sup
        (schwartzSeminormFamily Real
          (Section43SpatialSpace d k) Complex) chi
    exact finsetSup_compContinuousLinearEquiv_le e s chi
  let Q := s.sup
    (schwartzSeminormFamily Complex
      (Section43SpatialSpace d k) Complex) chi
  have hQ : 0 <= Q := apply_nonneg _ _
  calc
    osiiSpatialPolynomialWeightedL1 p
        (section43SpatialFlatSchwartzCLE d k chi) <=
      K * s.sup
          (schwartzSeminormFamily Complex (Fin (k * d) -> Real) Complex)
          flat := by simpa [flat] using hflat
    _ <= K * (factor * Q) :=
      mul_le_mul_of_nonneg_left (by simpa [Q] using htransport) hK.le
    _ <= K * ((factor + 1) * Q) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) hQ
    _ = C * s.sup
          (schwartzSeminormFamily Complex
            (Section43SpatialSpace d k) Complex) chi := by
      dsimp [C, Q]
      ring

end OSIIEquation621WeightedL1Section43BoundData

end OSReconstruction
