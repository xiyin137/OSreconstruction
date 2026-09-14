/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIProductionRadialGraded

noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

theorem osiiProduction_onePointEquiv_norm_le_one
    (d : Nat) :
    ‖(ContinuousLinearEquiv.funUnique
      (Fin 1) Real (SpacetimeDim d)).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa [ContinuousLinearEquiv.coe_funUnique] using
    (norm_le_pi_norm x (default : Fin 1))

theorem osiiProduction_onePointEquiv_symm_norm_le_one
    (d : Nat) :
    ‖(ContinuousLinearEquiv.funUnique
      (Fin 1) Real (SpacetimeDim d)).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  change ‖x‖ ≤ ‖x‖
  exact le_rfl

theorem osiiProduction_rectangle_card
    (L : Nat) :
    (((Finset.Iic (L, L)).card : Nat) : Real) =
      (((L + 1 : Nat) : Real)) ^ 2 := by
  rw [Finset.card_Iic_prod, Nat.card_Iic]
  push_cast
  ring

theorem osiiProduction_rectangle_tensor_bound
    (L : Nat) :
    schwartzTensorProductFinsetFactor (Finset.Iic (L, L)) ≤
      (2 : Real) ^ (2 * L + 3) := by
  rw [osiiProduction_schwartzTensorProductFinsetFactor_Iic]
  have hpower : 1 ≤ (2 : Real) ^ (L + 1) :=
    one_le_pow₀ (by norm_num)
  calc
    2 * ((2 : Real) ^ (L + 1) - 1) *
        ((2 : Real) ^ (L + 1) - 1) ≤
      2 * (2 : Real) ^ (L + 1) * (2 : Real) ^ (L + 1) := by
        gcongr <;> linarith
    _ = (2 : Real) ^ (2 * L + 3) := by
      rw [show 2 * (2 : Real) ^ (L + 1) * 2 ^ (L + 1) =
        (2 ^ (L + 1) * 2 ^ (L + 1)) * 2 by ring]
      rw [← pow_add, ← pow_succ]
      congr 1
      omega

theorem osiiProduction_onePointEquiv_finsetFactor_le_card
    (d : Nat) (t : Finset (Nat × Nat)) :
    schwartzCompEquivFinsetFactor
        (ContinuousLinearEquiv.funUnique
          (Fin 1) Real (SpacetimeDim d)) t ≤
      (t.card : Real) := by
  calc
    schwartzCompEquivFinsetFactor
        (ContinuousLinearEquiv.funUnique
          (Fin 1) Real (SpacetimeDim d)) t ≤
      ∑ j ∈ t, (1 : Real) ^ j.1 * (1 : Real) ^ j.2 := by
        apply schwartzCompEquivFinsetFactor_le_of_norm_le
        · norm_num
        · exact osiiProduction_onePointEquiv_symm_norm_le_one d
        · exact osiiProduction_onePointEquiv_norm_le_one d
    _ = (t.card : Real) := by simp

theorem osiiProduction_reducedLiftFactor_growingRectangle_bound
    (d k L : Nat) :
    reducedTestLiftIndexPreservingFactor d k (Finset.Iic (L, L)) ≤
      8 * (((L + 1 : Nat) : Real)) ^ 6 *
        (((k + 1 : Nat) : Real)) ^ L * (16 : Real) ^ L := by
  let t : Finset (Nat × Nat) := Finset.Iic (L, L)
  let one := ContinuousLinearEquiv.funUnique
    (Fin 1) Real (SpacetimeDim d)
  let cast :=
    ContinuousLinearEquiv.piCongrLeft Real
      (fun _ : Fin (1 + k) => SpacetimeDim d)
      (finCongr (Nat.add_comm k 1))
  let diff := BHW.realDiffCoordCLE (k + 1) d
  let N : Real := (L + 1 : Nat)
  let R : Real := (k + 1 : Nat)
  have hcard : (t.card : Real) = N ^ 2 := by
    simpa [t, N] using osiiProduction_rectangle_card L
  have hdiff :
      schwartzCompEquivFinsetFactor diff t ≤
        N ^ 2 * ((k : Real) + 2) ^ L * (2 : Real) ^ L := by
    have h :=
      schwartzCompEquivFinsetFactor_realDiffCoordCLE_le_arityPolynomial
        d k t
    simpa [diff, t, hcard, N,
      schwartzSeminormWeightOrder_Iic,
      schwartzSeminormDerivativeOrder_Iic,
      osiiProduction_rectangle_card] using h
  have hcast :
      schwartzCompEquivFinsetFactor cast t ≤ N ^ 2 := by
    calc
      schwartzCompEquivFinsetFactor cast t ≤ (t.card : Real) := by
        exact schwartzCompEquivFinsetFactor_piCongrLeft_le_card
          (E := SpacetimeDim d) (finCongr (Nat.add_comm k 1)) t
      _ = N ^ 2 := hcard
  have hone :
      schwartzCompEquivFinsetFactor one t ≤ N ^ 2 := by
    calc
      schwartzCompEquivFinsetFactor one t ≤ (t.card : Real) :=
        osiiProduction_onePointEquiv_finsetFactor_le_card d t
      _ = N ^ 2 := hcard
  have htensor :
      schwartzTensorProductFinsetFactor t ≤
        (2 : Real) ^ (2 * L + 3) := by
    simpa [t] using osiiProduction_rectangle_tensor_bound L
  have hcast_nonneg : 0 ≤ schwartzCompEquivFinsetFactor cast t :=
    schwartzCompEquivFinsetFactor_nonneg cast t
  have hone_nonneg : 0 ≤ schwartzCompEquivFinsetFactor one t :=
    schwartzCompEquivFinsetFactor_nonneg one t
  have htensor_nonneg : 0 ≤ schwartzTensorProductFinsetFactor t :=
    schwartzTensorProductFinsetFactor_nonneg t
  have hshift : (k : Real) + 2 ≤ 2 * R := by
    dsimp [R]
    push_cast
    nlinarith [show (0 : Real) ≤ (k : Real) by positivity]
  have hpowers :
      (2 : Real) ^ L * 2 ^ L * 2 ^ (2 * L + 3) =
        8 * (16 : Real) ^ L := by
    calc
      (2 : Real) ^ L * 2 ^ L * 2 ^ (2 * L + 3) =
        2 ^ (4 * L + 3) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
      _ = 8 * (16 : Real) ^ L := by
        rw [pow_add, pow_mul]
        norm_num
        ring
  have hdecomp :
      reducedTestLiftIndexPreservingFactor d k t =
        schwartzCompEquivFinsetFactor diff t *
          schwartzCompEquivFinsetFactor cast t *
          schwartzTensorProductFinsetFactor t *
          schwartzCompEquivFinsetFactor one t := by
    dsimp [reducedTestLiftIndexPreservingFactor, diff, cast, one, t]
    rw [schwartzSeminormRectangle_Iic]
  change reducedTestLiftIndexPreservingFactor d k t ≤
    8 * N ^ 6 * R ^ L * (16 : Real) ^ L
  calc
    reducedTestLiftIndexPreservingFactor d k t =
      schwartzCompEquivFinsetFactor diff t *
        schwartzCompEquivFinsetFactor cast t *
        schwartzTensorProductFinsetFactor t *
        schwartzCompEquivFinsetFactor one t := hdecomp
    _ ≤ (N ^ 2 * ((k : Real) + 2) ^ L * 2 ^ L) *
          N ^ 2 * 2 ^ (2 * L + 3) * N ^ 2 := by
            gcongr
    _ ≤ (N ^ 2 * (2 * R) ^ L * 2 ^ L) *
          N ^ 2 * 2 ^ (2 * L + 3) * N ^ 2 := by
            gcongr
    _ = N ^ 6 * R ^ L *
          ((2 : Real) ^ L * 2 ^ L * 2 ^ (2 * L + 3)) := by
            rw [mul_pow]
            ring
    _ = 8 * N ^ 6 * R ^ L * (16 : Real) ^ L := by
      rw [hpowers]
      ring

theorem osiiProduction_splitCoefficient_bound
    (C : Real) (hC : 256 ≤ C) (r s : Nat) (hr : 0 < r) :
    16 * (256 : Real) ^ (2 * r * s) *
        C ^ r * C ^ (2 * (2 * r * s)) *
        (r : Real) ^ (2 * (2 * r * s)) *
        (((2 * r * s).factorial : Nat) : Real) ^ 4 *
        (((2 * r * s + 1 : Nat) : Real)) ^ 6 ≤
      (C ^ (2 + 6 * s) *
          (((2 * max s 1 : Nat) : Real)) ^ (8 * s) *
          (((2 * s + 1 : Nat) : Real)) ^ 6) ^ r *
        (r : Real) ^ ((12 * s + 6) * r) := by
  let L : Nat := 2 * r * s
  let M : Real := (2 * max s 1 : Nat)
  let B : Real := (2 * s + 1 : Nat)
  let R : Real := r
  have hC_one : 1 ≤ C := by linarith
  have hR_one : 1 ≤ R := by
    dsimp [R]
    exact_mod_cast hr
  have hB_one : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ 2 * s + 1 by omega)
  have hM_nonneg : 0 ≤ M := by positivity
  have hL_le : L ≤ (2 * max s 1) * r := by
    dsimp [L]
    calc
      2 * r * s ≤ 2 * r * max s 1 :=
        Nat.mul_le_mul_left (2 * r) (le_max_left s 1)
      _ = (2 * max s 1) * r := by ring
  have hL_real : (L : Real) ≤ M * R := by
    dsimp [M, R]
    exact_mod_cast hL_le
  have hfactorial : (L.factorial : Real) ≤ (M * R) ^ L := by
    calc
      (L.factorial : Real) ≤ (L : Real) ^ L := by
        exact_mod_cast Nat.factorial_le_pow L
      _ ≤ (M * R) ^ L :=
        pow_le_pow_left₀ (by positivity) hL_real L
  have hL_add : L + 1 ≤ (2 * s + 1) * r := by
    dsimp [L]
    calc
      2 * r * s + 1 ≤ 2 * r * s + r :=
        Nat.add_le_add_left hr (2 * r * s)
      _ = (2 * s + 1) * r := by ring
  have hL_add_real : ((L + 1 : Nat) : Real) ≤ B * R := by
    dsimp [B, R]
    exact_mod_cast hL_add
  have hBR_one : 1 ≤ B * R :=
    one_le_mul_of_one_le_of_one_le hB_one hR_one
  have hlast :
      ((L + 1 : Nat) : Real) ^ 6 ≤ (B * R) ^ (6 * r) := by
    calc
      ((L + 1 : Nat) : Real) ^ 6 ≤ (B * R) ^ 6 := by gcongr
      _ ≤ (B * R) ^ (6 * r) :=
        pow_le_pow_right₀ hBR_one (by omega)
  have hsixteen : (16 : Real) ≤ C ^ r := by
    calc
      (16 : Real) ≤ C := by linarith
      _ = C ^ 1 := by simp
      _ ≤ C ^ r := pow_le_pow_right₀ hC_one (by omega)
  change
    16 * (256 : Real) ^ L * C ^ r * C ^ (2 * L) *
        R ^ (2 * L) * (L.factorial : Real) ^ 4 *
        ((L + 1 : Nat) : Real) ^ 6 ≤
      (C ^ (2 + 6 * s) * M ^ (8 * s) * B ^ 6) ^ r *
        R ^ ((12 * s + 6) * r)
  calc
    16 * (256 : Real) ^ L * C ^ r * C ^ (2 * L) *
        R ^ (2 * L) * (L.factorial : Real) ^ 4 *
        ((L + 1 : Nat) : Real) ^ 6 ≤
      C ^ r * C ^ L * C ^ r * C ^ (2 * L) *
        R ^ (2 * L) * ((M * R) ^ L) ^ 4 *
        (B * R) ^ (6 * r) := by
          gcongr
    _ = (C ^ (2 + 6 * s) * M ^ (8 * s) * B ^ 6) ^ r *
        R ^ ((12 * s + 6) * r) := by
      dsimp [L]
      simp only [mul_pow, ← pow_mul]
      ring

theorem osiiProduction_actualSplitCoefficient_bound
    (d k s : Nat) (M K B C : Real)
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K) (hB0 : 0 ≤ B)
    (hM : M ≤ C) (hK : K ≤ C) (hB : B ≤ C)
    (hC : 256 ≤ C) :
    let r : Nat := k + 1
    let L : Nat := 2 * r * s
    reducedTestLiftIndexPreservingFactor d k (Finset.Iic (L, L)) *
        (2 ^ (2 * L + 1) * M * B ^ L *
          (L.factorial : Real) ^ 2) *
        ((4 : Real) ^ L * K ^ k * B ^ L *
          (r : Real) ^ L * (L.factorial : Real) ^ 2) ≤
      (C ^ (2 + 6 * s) *
          (((2 * max s 1 : Nat) : Real)) ^ (8 * s) *
          (((2 * s + 1 : Nat) : Real)) ^ 6) ^ r *
        (r : Real) ^ ((12 * s + 6) * r) := by
  dsimp
  let r : Nat := k + 1
  let L : Nat := 2 * r * s
  let R : Real := r
  let N : Real := (L + 1 : Nat)
  have hr : 0 < r := by
    dsimp [r]
    omega
  have hC0 : 0 ≤ C := by linarith
  have hR0 : 0 ≤ R := by positivity
  have hN0 : 0 ≤ N := by positivity
  have hfactorial0 : 0 ≤ (L.factorial : Real) := by positivity
  have hlift :
      reducedTestLiftIndexPreservingFactor d k (Finset.Iic (L, L)) ≤
        8 * N ^ 6 * R ^ L * (16 : Real) ^ L := by
    simpa [N, R, r] using
      osiiProduction_reducedLiftFactor_growingRectangle_bound d k L
  have hregularizer :
      (16 : Real) ^ L * 2 ^ (2 * L + 1) * 4 ^ L =
        2 * (256 : Real) ^ L := by
    have htwo :
        (2 : Real) ^ (2 * L + 1) =
          2 * (4 : Real) ^ L := by
      calc
        (2 : Real) ^ (2 * L + 1) =
          2 ^ (2 * L) * 2 := by rw [pow_succ]
        _ = (2 ^ 2) ^ L * 2 := by rw [pow_mul]
        _ = 2 * (4 : Real) ^ L := by norm_num; ring
    rw [htwo]
    calc
      (16 : Real) ^ L * (2 * 4 ^ L) * 4 ^ L =
        2 * (16 ^ L * 4 ^ L * 4 ^ L) := by ring
      _ = 2 * ((16 : Real) * 4 * 4) ^ L := by
        rw [mul_pow, mul_pow]
      _ = 2 * (256 : Real) ^ L := by norm_num
  have hCpower :
      C * C ^ L * C ^ k * C ^ L =
        C ^ r * C ^ (2 * L) := by
    have hdouble : C ^ (2 * L) = C ^ L * C ^ L := by
      rw [show 2 * L = L + L by omega, pow_add]
    dsimp [r]
    rw [pow_succ, hdouble]
    ring
  have hnumeric := osiiProduction_splitCoefficient_bound C hC r s hr
  change
    reducedTestLiftIndexPreservingFactor d k (Finset.Iic (L, L)) *
        (2 ^ (2 * L + 1) * M * B ^ L *
          (L.factorial : Real) ^ 2) *
        ((4 : Real) ^ L * K ^ k * B ^ L *
          R ^ L * (L.factorial : Real) ^ 2) ≤
      (C ^ (2 + 6 * s) *
          (((2 * max s 1 : Nat) : Real)) ^ (8 * s) *
          (((2 * s + 1 : Nat) : Real)) ^ 6) ^ r *
        R ^ ((12 * s + 6) * r)
  calc
    reducedTestLiftIndexPreservingFactor d k (Finset.Iic (L, L)) *
        (2 ^ (2 * L + 1) * M * B ^ L *
          (L.factorial : Real) ^ 2) *
        ((4 : Real) ^ L * K ^ k * B ^ L *
          R ^ L * (L.factorial : Real) ^ 2) ≤
      (8 * N ^ 6 * R ^ L * (16 : Real) ^ L) *
        (2 ^ (2 * L + 1) * C * C ^ L *
          (L.factorial : Real) ^ 2) *
        ((4 : Real) ^ L * C ^ k * C ^ L *
          R ^ L * (L.factorial : Real) ^ 2) := by
            gcongr
    _ = 16 * (256 : Real) ^ L * C ^ r * C ^ (2 * L) *
          R ^ (2 * L) * (L.factorial : Real) ^ 4 *
          N ^ 6 := by
            rw [show
              (8 * N ^ 6 * R ^ L * (16 : Real) ^ L) *
                  (2 ^ (2 * L + 1) * C * C ^ L *
                    (L.factorial : Real) ^ 2) *
                  ((4 : Real) ^ L * C ^ k * C ^ L *
                    R ^ L * (L.factorial : Real) ^ 2) =
                8 * ((16 : Real) ^ L * 2 ^ (2 * L + 1) * 4 ^ L) *
                  (C * C ^ L * C ^ k * C ^ L) *
                  (R ^ L * R ^ L) *
                  ((L.factorial : Real) ^ 2 *
                    (L.factorial : Real) ^ 2) * N ^ 6 by ring]
            rw [hregularizer, hCpower, ← pow_add, ← pow_add]
            ring_nf
    _ ≤ (C ^ (2 + 6 * s) *
          (((2 * max s 1 : Nat) : Real)) ^ (8 * s) *
          (((2 * s + 1 : Nat) : Real)) ^ 6) ^ r *
        R ^ ((12 * s + 6) * r) := by
          simpa [L, R, N] using hnumeric

def osiiProduction_radialSplitBase (d : Nat) : Real :=
  let M : Real :=
    (∫ z : Fin (d + 1) → Complex,
      osiiStep4ComplexBlockRadialRaw (d + 1) 16 z)⁻¹ *
        Real.exp 6
  let K : Real := (4 : Real) ^ (d + 1) * M ^ 2
  let B : Real := 98304 * (((d + 1) * 2 : Nat) : Real) ^ 2
  max 256 (max M (max K B))

def osiiProduction_radialSplitCoefficient
    (d s k : Nat) : Real :=
  let L : Nat := (k + 1) * (2 * s)
  let M : Real :=
    (∫ z : Fin (d + 1) → Complex,
      osiiStep4ComplexBlockRadialRaw (d + 1) 16 z)⁻¹ *
        Real.exp 6
  let K : Real := (4 : Real) ^ (d + 1) * M ^ 2
  let B : Real := 98304 * (((d + 1) * 2 : Nat) : Real) ^ 2
  reducedTestLiftIndexPreservingFactor d k (Finset.Iic (L, L)) *
    (2 ^ (2 * L + 1) * M * B ^ L *
      (L.factorial : Real) ^ 2) *
    ((4 : Real) ^ L * K ^ k * B ^ L *
      ((k + 1 : Nat) : Real) ^ L *
      (L.factorial : Real) ^ 2)

theorem osiiProduction_radialSplitCoefficient_arityMajorant
    (d s k : Nat) :
    osiiProduction_radialSplitCoefficient d s k ≤
      (osiiProduction_radialSplitBase d ^ (2 + 6 * s) *
          (((2 * max s 1 : Nat) : Real)) ^ (8 * s) *
          (((2 * s + 1 : Nat) : Real)) ^ 6) ^ (k + 1) *
        (((k + 1 : Nat) : Real)) ^
          ((12 * s + 6) * (k + 1)) := by
  let M : Real :=
    (∫ z : Fin (d + 1) → Complex,
      osiiStep4ComplexBlockRadialRaw (d + 1) 16 z)⁻¹ *
        Real.exp 6
  let K : Real := (4 : Real) ^ (d + 1) * M ^ 2
  let B : Real := 98304 * (((d + 1) * 2 : Nat) : Real) ^ 2
  let C : Real := osiiProduction_radialSplitBase d
  have hmass :
      0 < ∫ z : Fin (d + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (d + 1) 16 z :=
    osiiStep4ComplexBlockRadialRaw_integral_pos
      (d + 1) (by norm_num)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC : 256 ≤ C := by
    dsimp [C, osiiProduction_radialSplitBase]
    exact le_max_left _ _
  have hM : M ≤ C := by
    dsimp [C, osiiProduction_radialSplitBase]
    exact le_max_of_le_right (le_max_left _ _)
  have hK : K ≤ C := by
    dsimp [C, osiiProduction_radialSplitBase, K, M]
    exact le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))
  have hB : B ≤ C := by
    dsimp [C, osiiProduction_radialSplitBase, B]
    exact le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))
  have h :=
    osiiProduction_actualSplitCoefficient_bound
      d k s M K B C hM0 hK0 hB0 hM hK hB hC
  simpa [osiiProduction_radialSplitCoefficient, C, K, M, B,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

theorem osiiProduction_radialEndpointFullSource_explicit
    (d s k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho ≤ 16)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) → Real) :
    (Finset.Iic ((k + 1) * (2 * s), (k + 1) * (2 * s))).sup
        (schwartzSeminormFamily Real
          (NPointDomain d (k + 1)) Complex)
        (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho endpointCenter endpointImag center y y') ≤
      osiiProduction_radialSplitCoefficient d s k *
        (16 / rho) ^
          (k * (3 * (d + 1) + 4 * s) +
            (2 * (d + 1) + 4 * s)) *
        (1 + ‖endpointCenter‖) ^ ((k + 1) * (2 * s)) *
        (1 + ‖center‖) ^ ((k + 1) * (2 * s)) := by
  let L : Nat := (k + 1) * (2 * s)
  let t : Finset (Nat × Nat) := Finset.Iic (L, L)
  let CLift : Real := reducedTestLiftIndexPreservingFactor d k t
  let CHead : Real :=
    2 ^ (2 * L + 1) *
      (∫ z : Fin (d + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (d + 1) 16 z)⁻¹ *
      Real.exp 6 *
      (98304 * (((d + 1) * 2 : Nat) : Real) ^ 2) ^ L *
        (L.factorial : Real) ^ 2
  let CTail : Real :=
    (4 : Real) ^ L *
      ((4 : Real) ^ (d + 1) *
        ((∫ z : Fin (d + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (d + 1) 16 z)⁻¹ *
          Real.exp 6) ^ 2) ^ k *
      (98304 * (((d + 1) * 2 : Nat) : Real) ^ 2) ^ L *
        ((k + 1 : Nat) : Real) ^ L *
        (L.factorial : Real) ^ 2
  let chi : SchwartzMap (SpacetimeDim d) Complex :=
    osiiStep4CenteredComplexBlockRadialGRealSchwartz
      (d + 1) hrho endpointCenter endpointImag
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y'
  have hmass :
      0 < ∫ z : Fin (d + 1) → Complex,
        osiiStep4ComplexBlockRadialRaw (d + 1) 16 z :=
    osiiStep4ComplexBlockRadialRaw_integral_pos
      (d + 1) (by norm_num)
  have hCLift : 0 ≤ CLift :=
    reducedTestLiftIndexPreservingFactor_nonneg d k t
  have hCHead : 0 ≤ CHead := by
    dsimp [CHead]
    positivity
  have hrect : schwartzSeminormRectangle t = t :=
    schwartzSeminormRectangle_Iic L L
  have hlift :=
    reducedTestLift_indexPreserving_product_bound d k t chi phi
  have hhead :=
    osiiStep4CenteredComplexBlockRadialGRealSchwartz_Iic_gevrey_bound
      d hrho hrho_le endpointCenter endpointImag L L
  have htail :=
    osiiStep4CenteredPartialConvolutionKernelFullSource_Iic_gevrey_bound
      d k hrho hrho_le center y y' L L
  have hscale :
      (2 * (d + 1) + L) + (3 * (d + 1) * k + L) =
        k * (3 * (d + 1) + 4 * s) +
          (2 * (d + 1) + 4 * s) := by
    dsimp [L]
    ring
  have hcoefficient :
      osiiProduction_radialSplitCoefficient d s k =
        CLift * CHead * CTail := by
    dsimp [osiiProduction_radialSplitCoefficient,
      CLift, CHead, CTail, t, L]
    ring
  change
    t.sup (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex)
      (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag center y y') ≤
      osiiProduction_radialSplitCoefficient d s k *
        (16 / rho) ^
          (k * (3 * (d + 1) + 4 * s) +
            (2 * (d + 1) + 4 * s)) *
        (1 + ‖endpointCenter‖) ^ L *
        (1 + ‖center‖) ^ L
  calc
    t.sup (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex)
      (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag center y y') ≤
      CLift *
          t.sup (schwartzSeminormFamily Real
            (SpacetimeDim d) Complex) chi *
          t.sup (schwartzSeminormFamily Real
            (NPointDomain d k) Complex) phi := by
        simpa [hrect, chi, phi,
          osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource]
          using hlift
    _ ≤ CLift *
          (CHead * (16 / rho) ^ (2 * (d + 1) + L) *
            (1 + ‖endpointCenter‖) ^ L) *
          (CTail * (16 / rho) ^ (3 * (d + 1) * k + L) *
            (1 + ‖center‖) ^ L) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (by simpa [t, chi, CHead] using hhead) hCLift)
        (by simpa [t, phi, CTail] using htail)
        (apply_nonneg _ _)
        (mul_nonneg hCLift (by positivity))
    _ = osiiProduction_radialSplitCoefficient d s k *
        (16 / rho) ^
          (k * (3 * (d + 1) + 4 * s) +
            (2 * (d + 1) + 4 * s)) *
        (1 + ‖endpointCenter‖) ^ L *
        (1 + ‖center‖) ^ L := by
      rw [hcoefficient, ← hscale, pow_add]
      ring

theorem osiiProduction_radialSplitArityBase_one_le
    (d s : Nat) :
    1 ≤
      osiiProduction_radialSplitBase d ^ (2 + 6 * s) *
        (((2 * max s 1 : Nat) : Real)) ^ (8 * s) *
        (((2 * s + 1 : Nat) : Real)) ^ 6 := by
  have hbase : (1 : Real) ≤ osiiProduction_radialSplitBase d := by
    calc
      (1 : Real) ≤ 256 := by norm_num
      _ ≤ osiiProduction_radialSplitBase d := by
        dsimp [osiiProduction_radialSplitBase]
        exact le_max_left _ _
  have hindex : (1 : Real) ≤ (((2 * max s 1 : Nat) : Real)) := by
    exact_mod_cast (show 1 ≤ 2 * max s 1 by omega)
  have hplus : (1 : Real) ≤ (((2 * s + 1 : Nat) : Real)) := by
    exact_mod_cast (show 1 ≤ 2 * s + 1 by omega)
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ hbase)
      (one_le_pow₀ hindex))
    (one_le_pow₀ hplus)

theorem exists_radialEndpointFullSource_fixedArityMajorant
    (d s : Nat) [NeZero d] :
    ∃ A : Real, 1 ≤ A ∧
      ∀ (k : Nat) {rho : Real}
        (hrho : 0 < rho) (_ : rho ≤ 16)
        (endpointCenter endpointImag : SpacetimeDim d)
        (center y y' : Fin (k * (d + 1)) → Real),
        (Finset.Iic ((k + 1) * (2 * s),
            (k + 1) * (2 * s))).sup
          (schwartzSeminormFamily Real
            (NPointDomain d (k + 1)) Complex)
          (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
            d k hrho endpointCenter endpointImag center y y') ≤
          A ^ (k + 1) *
            (((k + 1 : Nat) : Real)) ^
              ((12 * s + 6) * (k + 1)) *
            (16 / rho) ^
              (k * (3 * (d + 1) + 4 * s) +
                (2 * (d + 1) + 4 * s)) *
            (1 + ‖endpointCenter‖) ^ ((k + 1) * (2 * s)) *
            (1 + ‖center‖) ^ ((k + 1) * (2 * s)) := by
  let A : Real :=
    osiiProduction_radialSplitBase d ^ (2 + 6 * s) *
      (((2 * max s 1 : Nat) : Real)) ^ (8 * s) *
      (((2 * s + 1 : Nat) : Real)) ^ 6
  refine ⟨A, osiiProduction_radialSplitArityBase_one_le d s, ?_⟩
  intro k rho hrho hrho_le endpointCenter endpointImag center y y'
  have hsource :=
    osiiProduction_radialEndpointFullSource_explicit
      d s k hrho hrho_le endpointCenter endpointImag center y y'
  have hcoefficient :=
    osiiProduction_radialSplitCoefficient_arityMajorant d s k
  calc
    (Finset.Iic ((k + 1) * (2 * s),
        (k + 1) * (2 * s))).sup
      (schwartzSeminormFamily Real
        (NPointDomain d (k + 1)) Complex)
      (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag center y y') ≤
      osiiProduction_radialSplitCoefficient d s k *
        (16 / rho) ^
          (k * (3 * (d + 1) + 4 * s) +
            (2 * (d + 1) + 4 * s)) *
        (1 + ‖endpointCenter‖) ^ ((k + 1) * (2 * s)) *
        (1 + ‖center‖) ^ ((k + 1) * (2 * s)) := hsource
    _ ≤ A ^ (k + 1) *
            (((k + 1 : Nat) : Real)) ^
              ((12 * s + 6) * (k + 1)) *
            (16 / rho) ^
              (k * (3 * (d + 1) + 4 * s) +
                (2 * (d + 1) + 4 * s)) *
            (1 + ‖endpointCenter‖) ^ ((k + 1) * (2 * s)) *
            (1 + ‖center‖) ^ ((k + 1) * (2 * s)) := by
      gcongr

end OSReconstruction

