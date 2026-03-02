import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2Invariants

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

/-- `d=1,n=2` complex configurations. -/
abbrev D1N2Config := Fin 2 → Fin (1 + 1) → ℂ

/-- `d=1` complex vectors. -/
abbrev D1Vec := Fin (1 + 1) → ℂ

/-- `d=1` complex Minkowski bilinear form (signature `(-,+)`). -/
def d1MinkowskiBilinC (u v : D1Vec) : ℂ :=
  ∑ μ, (minkowskiSignature 1 μ : ℂ) * u μ * v μ

/-- Symmetry of the complex `d=1` Minkowski bilinear form. -/
lemma d1MinkowskiBilinC_symm (u v : D1Vec) :
    d1MinkowskiBilinC u v = d1MinkowskiBilinC v u := by
  simp [d1MinkowskiBilinC, mul_comm, mul_left_comm]

/-- `Q₀ = z₀·z₀`. -/
def d1Q0 (z : D1N2Config) : ℂ :=
  d1MinkowskiBilinC (z 0) (z 0)

/-- `Q₁ = z₁·z₁`. -/
def d1Q1 (z : D1N2Config) : ℂ :=
  d1MinkowskiBilinC (z 1) (z 1)

/-- `P = z₀·z₁`. -/
def d1P01 (z : D1N2Config) : ℂ :=
  d1MinkowskiBilinC (z 0) (z 1)

/-- Matrix whose columns are the two `d=1` points `(z₀,z₁)`. -/
def d1PointMatrix (z : D1N2Config) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun μ k => z k μ

/-- `S = -2 det([z₀|z₁])`. Under swap, `S` changes sign. -/
def d1S01 (z : D1N2Config) : ℂ :=
  (-2 : ℂ) * (d1PointMatrix z).det

/-- Light-cone `u` coordinate for point `0`. -/
def d1U0 (z : D1N2Config) : ℂ := z 0 0 + z 0 1

/-- Light-cone `v` coordinate for point `0`. -/
def d1V0 (z : D1N2Config) : ℂ := z 0 0 - z 0 1

/-- Light-cone `u` coordinate for point `1`. -/
def d1U1 (z : D1N2Config) : ℂ := z 1 0 + z 1 1

/-- Light-cone `v` coordinate for point `1`. -/
def d1V1 (z : D1N2Config) : ℂ := z 1 0 - z 1 1

/-- Light-cone mixed invariant `R = u₀ v₁`. -/
def d1R01 (z : D1N2Config) : ℂ := d1U0 z * d1V1 z

/-- Light-cone mixed invariant `T = u₁ v₀`. -/
def d1T01 (z : D1N2Config) : ℂ := d1U1 z * d1V0 z

/-- With signature `(-,+)`, `Q₀ = -(u₀ v₀)`. -/
lemma d1Q0_eq_neg_U0_mul_V0 (z : D1N2Config) :
    d1Q0 z = -(d1U0 z * d1V0 z) := by
  simp [d1Q0, d1MinkowskiBilinC, d1U0, d1V0, Fin.sum_univ_two, minkowskiSignature]
  ring

/-- With signature `(-,+)`, `Q₁ = -(u₁ v₁)`. -/
lemma d1Q1_eq_neg_U1_mul_V1 (z : D1N2Config) :
    d1Q1 z = -(d1U1 z * d1V1 z) := by
  simp [d1Q1, d1MinkowskiBilinC, d1U1, d1V1, Fin.sum_univ_two, minkowskiSignature]
  ring

/-- With signature `(-,+)`, `2P = -(R + T)`. -/
lemma d1_two_mul_P01_eq_neg_R01_add_T01 (z : D1N2Config) :
    (2 : ℂ) * d1P01 z = -(d1R01 z + d1T01 z) := by
  simp [d1P01, d1R01, d1T01, d1U0, d1V0, d1U1, d1V1,
    d1MinkowskiBilinC, Fin.sum_univ_two, minkowskiSignature]
  ring

/-- `S = R - T`. -/
lemma d1S01_eq_R01_sub_T01 (z : D1N2Config) :
    d1S01 z = d1R01 z - d1T01 z := by
  simp [d1S01, d1R01, d1T01, d1U0, d1V0, d1U1, d1V1, d1PointMatrix, Matrix.det_fin_two]
  ring

/-- `R * T = Q₀ * Q₁`. -/
lemma d1_R01_mul_T01_eq_Q0_mul_Q1 (z : D1N2Config) :
    d1R01 z * d1T01 z = d1Q0 z * d1Q1 z := by
  calc
    d1R01 z * d1T01 z
        = (d1U0 z * d1V1 z) * (d1U1 z * d1V0 z) := by rfl
    _ = (d1U0 z * d1V0 z) * (d1U1 z * d1V1 z) := by ring
    _ = (-d1Q0 z) * (-d1Q1 z) := by
          rw [d1Q0_eq_neg_U0_mul_V0, d1Q1_eq_neg_U1_mul_V1]
          ring
    _ = d1Q0 z * d1Q1 z := by ring

/-- Solve for `R` from `(P,S)` with signature `(-,+)`. -/
lemma d1R01_eq_of_P01_S01 (z : D1N2Config) :
    d1R01 z = (d1S01 z - (2 : ℂ) * d1P01 z) / 2 := by
  have hP : (2 : ℂ) * d1P01 z = -(d1R01 z + d1T01 z) := d1_two_mul_P01_eq_neg_R01_add_T01 z
  have hS : d1S01 z = d1R01 z - d1T01 z := d1S01_eq_R01_sub_T01 z
  have hsum : d1R01 z + d1T01 z = -((2 : ℂ) * d1P01 z) := by
    calc
      d1R01 z + d1T01 z = -(-(d1R01 z + d1T01 z)) := by ring
      _ = -((2 : ℂ) * d1P01 z) := by rw [← hP]
  calc
    d1R01 z = ((d1R01 z + d1T01 z) + (d1R01 z - d1T01 z)) / 2 := by ring
    _ = (-((2 : ℂ) * d1P01 z) + d1S01 z) / 2 := by rw [hsum, hS]
    _ = (d1S01 z - (2 : ℂ) * d1P01 z) / 2 := by ring

/-- Solve for `T` from `(P,S)` with signature `(-,+)`. -/
lemma d1T01_eq_of_P01_S01 (z : D1N2Config) :
    d1T01 z = (-(d1S01 z) - (2 : ℂ) * d1P01 z) / 2 := by
  have hP : (2 : ℂ) * d1P01 z = -(d1R01 z + d1T01 z) := d1_two_mul_P01_eq_neg_R01_add_T01 z
  have hS : d1S01 z = d1R01 z - d1T01 z := d1S01_eq_R01_sub_T01 z
  have hsum : d1R01 z + d1T01 z = -((2 : ℂ) * d1P01 z) := by
    calc
      d1R01 z + d1T01 z = -(-(d1R01 z + d1T01 z)) := by ring
      _ = -((2 : ℂ) * d1P01 z) := by rw [← hP]
  calc
    d1T01 z = ((d1R01 z + d1T01 z) - (d1R01 z - d1T01 z)) / 2 := by ring
    _ = (-((2 : ℂ) * d1P01 z) - d1S01 z) / 2 := by rw [hsum, hS]
    _ = (-(d1S01 z) - (2 : ℂ) * d1P01 z) / 2 := by ring

/-- `d=1` forward-cone criterion in `±` variables. -/
lemma inOpenForwardCone_d1_iff_pm (η : Fin (1 + 1) → ℝ) :
    InOpenForwardCone 1 η ↔ (η 0 + η 1 > 0 ∧ η 0 - η 1 > 0) := by
  constructor
  · intro hη
    have hq : -(η 0) ^ 2 + (η 1) ^ 2 < 0 := by
      simpa [minkowskiSignature] using hη.2
    have h_sq : (η 1) ^ 2 < (η 0) ^ 2 := by nlinarith [hq]
    have h_abs : |η 1| < η 0 := abs_lt_of_sq_lt_sq h_sq (le_of_lt hη.1)
    exact ⟨by linarith [neg_abs_le (η 1)], by linarith [le_abs_self (η 1)]⟩
  · intro hpm
    refine ⟨by linarith [hpm.1, hpm.2], ?_⟩
    have hq : -(η 0) ^ 2 + (η 1) ^ 2 < 0 := by nlinarith [hpm.1, hpm.2]
    simpa [minkowskiSignature] using hq

/-- For `z ∈ FT_{1,2}`, `Im(u0) > 0`. -/
lemma d1U0_im_pos_of_forward (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    0 < (d1U0 z).im := by
  have hz0cone : InOpenForwardCone 1 (fun μ => (z 0 μ).im) :=
    (forwardTube_d1_n2_iff z).1 hz |>.1
  have hpm := (inOpenForwardCone_d1_iff_pm (fun μ => (z 0 μ).im)).1 hz0cone
  simpa [d1U0, Complex.add_im] using hpm.1

/-- For `z ∈ FT_{1,2}`, `Im(v0) > 0`. -/
lemma d1V0_im_pos_of_forward (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    0 < (d1V0 z).im := by
  have hz0cone : InOpenForwardCone 1 (fun μ => (z 0 μ).im) :=
    (forwardTube_d1_n2_iff z).1 hz |>.1
  have hpm := (inOpenForwardCone_d1_iff_pm (fun μ => (z 0 μ).im)).1 hz0cone
  simpa [d1V0, Complex.sub_im] using hpm.2

/-- For `z ∈ FT_{1,2}`, `u0 ≠ 0`. -/
lemma d1U0_ne_zero_of_forward (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    d1U0 z ≠ 0 := by
  intro hu0
  have him0 : (d1U0 z).im = 0 := by simp [hu0]
  linarith [d1U0_im_pos_of_forward z hz]

/-- For `z ∈ FT_{1,2}`, `v0 ≠ 0`. -/
lemma d1V0_ne_zero_of_forward (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    d1V0 z ≠ 0 := by
  intro hv0
  have him0 : (d1V0 z).im = 0 := by simp [hv0]
  linarith [d1V0_im_pos_of_forward z hz]

/-- For `z ∈ FT_{1,2}`, `Im(u1) > 0`. -/
lemma d1U1_im_pos_of_forward (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    0 < (d1U1 z).im := by
  rcases (forwardTube_d1_n2_iff z).1 hz with ⟨hz0cone, hzdiffcone⟩
  have hpm0 := (inOpenForwardCone_d1_iff_pm (fun μ => (z 0 μ).im)).1 hz0cone
  have hpmd := (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).1 hzdiffcone
  have hplus :
      0 < ((z 0 0).im + (z 0 1).im) + (((z 1 0 - z 0 0).im) + ((z 1 1 - z 0 1).im)) := by
    linarith [hpm0.1, hpmd.1]
  have hsum :
      (((z 0 0).im + (z 0 1).im) + (((z 1 0 - z 0 0).im) + ((z 1 1 - z 0 1).im))) =
        (d1U1 z).im := by
    simp [d1U1, Complex.add_im, Complex.sub_im]
    ring
  exact hsum ▸ hplus

/-- For `z ∈ FT_{1,2}`, `Im(v1) > 0`. -/
lemma d1V1_im_pos_of_forward (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    0 < (d1V1 z).im := by
  rcases (forwardTube_d1_n2_iff z).1 hz with ⟨hz0cone, hzdiffcone⟩
  have hpm0 := (inOpenForwardCone_d1_iff_pm (fun μ => (z 0 μ).im)).1 hz0cone
  have hpmd := (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).1 hzdiffcone
  have hminus :
      0 < ((z 0 0).im - (z 0 1).im) + (((z 1 0 - z 0 0).im) - ((z 1 1 - z 0 1).im)) := by
    linarith [hpm0.2, hpmd.2]
  have hsum :
      (((z 0 0).im - (z 0 1).im) + (((z 1 0 - z 0 0).im) - ((z 1 1 - z 0 1).im))) =
        (d1V1 z).im := by
    simp [d1V1, Complex.sub_im]
    ring
  exact hsum ▸ hminus

/-- For `z ∈ FT_{1,2}`, `u1 ≠ 0`. -/
lemma d1U1_ne_zero_of_forward (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    d1U1 z ≠ 0 := by
  intro hu1
  have him0 : (d1U1 z).im = 0 := by simp [hu1]
  linarith [d1U1_im_pos_of_forward z hz]

/-- For `z ∈ FT_{1,2}`, `v1 ≠ 0`. -/
lemma d1V1_ne_zero_of_forward (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    d1V1 z ≠ 0 := by
  intro hv1
  have him0 : (d1V1 z).im = 0 := by simp [hv1]
  linarith [d1V1_im_pos_of_forward z hz]

/-- Lorentz action on a single `d=1` complex vector. -/
def d1LorentzVecAct (Λ : ComplexLorentzGroup 1) (u : D1Vec) : D1Vec :=
  fun μ => ∑ ν, Λ.val μ ν * u ν

private theorem d1_metric_eq_00 (Λ : ComplexLorentzGroup 1) :
    (-1 : ℂ) * Λ.val 0 0 * Λ.val 0 0 + Λ.val 1 0 * Λ.val 1 0 = (-1 : ℂ) := by
  simpa [minkowskiSignature] using Λ.metric_preserving (0 : Fin 2) (0 : Fin 2)

private theorem d1_metric_eq_01 (Λ : ComplexLorentzGroup 1) :
    (-1 : ℂ) * Λ.val 0 0 * Λ.val 0 1 + Λ.val 1 0 * Λ.val 1 1 = 0 := by
  simpa [minkowskiSignature] using Λ.metric_preserving (0 : Fin 2) (1 : Fin 2)

private theorem d1_metric_eq_10 (Λ : ComplexLorentzGroup 1) :
    (-1 : ℂ) * Λ.val 0 1 * Λ.val 0 0 + Λ.val 1 1 * Λ.val 1 0 = 0 := by
  simpa [minkowskiSignature] using Λ.metric_preserving (1 : Fin 2) (0 : Fin 2)

private theorem d1_metric_eq_11 (Λ : ComplexLorentzGroup 1) :
    (-1 : ℂ) * Λ.val 0 1 * Λ.val 0 1 + Λ.val 1 1 * Λ.val 1 1 = (1 : ℂ) := by
  simpa [minkowskiSignature] using Λ.metric_preserving (1 : Fin 2) (1 : Fin 2)

/-- Lorentz invariance of the `d=1` complex Minkowski bilinear form. -/
lemma d1MinkowskiBilinC_lorentzVecAct (Λ : ComplexLorentzGroup 1)
    (u v : D1Vec) :
    d1MinkowskiBilinC (d1LorentzVecAct Λ u) (d1LorentzVecAct Λ v) =
      d1MinkowskiBilinC u v := by
  have h00 := d1_metric_eq_00 Λ
  have h01 := d1_metric_eq_01 Λ
  have h10 := d1_metric_eq_10 Λ
  have h11 := d1_metric_eq_11 Λ
  calc
    d1MinkowskiBilinC (d1LorentzVecAct Λ u) (d1LorentzVecAct Λ v)
        = ((-1 : ℂ) * Λ.val 0 0 * Λ.val 0 0 + Λ.val 1 0 * Λ.val 1 0) * (u 0 * v 0) +
          ((-1 : ℂ) * Λ.val 0 0 * Λ.val 0 1 + Λ.val 1 0 * Λ.val 1 1) * (u 0 * v 1) +
          ((-1 : ℂ) * Λ.val 0 1 * Λ.val 0 0 + Λ.val 1 1 * Λ.val 1 0) * (u 1 * v 0) +
          ((-1 : ℂ) * Λ.val 0 1 * Λ.val 0 1 + Λ.val 1 1 * Λ.val 1 1) * (u 1 * v 1) := by
            simp [d1MinkowskiBilinC, d1LorentzVecAct, Fin.sum_univ_two, minkowskiSignature]
            ring
    _ = (-1 : ℂ) * (u 0 * v 0) + (u 1 * v 1) := by
          rw [h00, h01, h10, h11]
          ring
    _ = d1MinkowskiBilinC u v := by
          simp [d1MinkowskiBilinC, Fin.sum_univ_two, minkowskiSignature]

private lemma d1LorentzVecAct_eq_config (Λ : ComplexLorentzGroup 1) (z : D1N2Config)
    (k : Fin 2) :
    (complexLorentzAction Λ z) k = d1LorentzVecAct Λ (z k) := by
  ext μ
  simp [complexLorentzAction, d1LorentzVecAct]

/-- `Q₀` is invariant under the complex Lorentz action. -/
lemma d1Q0_lorentzAction (Λ : ComplexLorentzGroup 1) (z : D1N2Config) :
    d1Q0 (complexLorentzAction Λ z) = d1Q0 z := by
  have h0 : (complexLorentzAction Λ z) 0 = d1LorentzVecAct Λ (z 0) :=
    d1LorentzVecAct_eq_config Λ z 0
  simp [d1Q0, h0, d1MinkowskiBilinC_lorentzVecAct]

/-- `Q₁` is invariant under the complex Lorentz action. -/
lemma d1Q1_lorentzAction (Λ : ComplexLorentzGroup 1) (z : D1N2Config) :
    d1Q1 (complexLorentzAction Λ z) = d1Q1 z := by
  have h1 : (complexLorentzAction Λ z) 1 = d1LorentzVecAct Λ (z 1) :=
    d1LorentzVecAct_eq_config Λ z 1
  simp [d1Q1, h1, d1MinkowskiBilinC_lorentzVecAct]

/-- `P` is invariant under the complex Lorentz action. -/
lemma d1P01_lorentzAction (Λ : ComplexLorentzGroup 1) (z : D1N2Config) :
    d1P01 (complexLorentzAction Λ z) = d1P01 z := by
  have h0 : (complexLorentzAction Λ z) 0 = d1LorentzVecAct Λ (z 0) :=
    d1LorentzVecAct_eq_config Λ z 0
  have h1 : (complexLorentzAction Λ z) 1 = d1LorentzVecAct Λ (z 1) :=
    d1LorentzVecAct_eq_config Λ z 1
  simp [d1P01, h0, h1, d1MinkowskiBilinC_lorentzVecAct]

private lemma d1PointMatrix_lorentzAction (Λ : ComplexLorentzGroup 1) (z : D1N2Config) :
    d1PointMatrix (complexLorentzAction Λ z) = Λ.val * d1PointMatrix z := by
  ext μ k
  simp [d1PointMatrix, complexLorentzAction, Matrix.mul_apply]

/-- `S` is invariant under the complex Lorentz action. -/
lemma d1S01_lorentzAction (Λ : ComplexLorentzGroup 1) (z : D1N2Config) :
    d1S01 (complexLorentzAction Λ z) = d1S01 z := by
  rw [d1S01, d1S01, d1PointMatrix_lorentzAction, Matrix.det_mul, Λ.proper, one_mul]

/-- Under swap `(0,1)`, `Q₀` becomes `Q₁`. -/
lemma d1Q0_swap01 (z : D1N2Config) :
    d1Q0 (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = d1Q1 z := by
  simp [d1Q0, d1Q1, permAct]

/-- Under swap `(0,1)`, `Q₁` becomes `Q₀`. -/
lemma d1Q1_swap01 (z : D1N2Config) :
    d1Q1 (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = d1Q0 z := by
  simp [d1Q0, d1Q1, permAct]

/-- Under swap `(0,1)`, `P` stays fixed. -/
lemma d1P01_swap01 (z : D1N2Config) :
    d1P01 (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = d1P01 z := by
  simp [d1P01, permAct, d1MinkowskiBilinC_symm]

/-- Under swap `(0,1)`, `R` becomes `T`. -/
lemma d1R01_swap01 (z : D1N2Config) :
    d1R01 (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = d1T01 z := by
  simp [d1R01, d1T01, d1U0, d1V0, d1U1, d1V1, permAct]

/-- Under swap `(0,1)`, `T` becomes `R`. -/
lemma d1T01_swap01 (z : D1N2Config) :
    d1T01 (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = d1R01 z := by
  simp [d1R01, d1T01, d1U0, d1V0, d1U1, d1V1, permAct]

private def d1SwapMatrix01 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (1 : ℂ); (1 : ℂ), (0 : ℂ)]

private lemma d1PointMatrix_swap01 (z : D1N2Config) :
    d1PointMatrix (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) =
      d1PointMatrix z * d1SwapMatrix01 := by
  ext μ k
  fin_cases μ <;> fin_cases k <;>
    simp [d1PointMatrix, permAct, d1SwapMatrix01, Matrix.mul_apply, Fin.sum_univ_two]

private lemma d1SwapMatrix01_det : d1SwapMatrix01.det = (-1 : ℂ) := by
  simp [d1SwapMatrix01, Matrix.det_fin_two]

/-- Under swap `(0,1)`, `S` changes sign. -/
lemma d1S01_swap01 (z : D1N2Config) :
    d1S01 (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = -d1S01 z := by
  rw [d1S01, d1PointMatrix_swap01, Matrix.det_mul, d1SwapMatrix01_det]
  rw [d1S01]
  ring

/-- The invariant triple `(Q₀,Q₁,P)`. -/
def d1InvariantTriple (z : D1N2Config) : ℂ × ℂ × ℂ :=
  (d1Q0 z, d1Q1 z, d1P01 z)

/-- The signed invariant quadruple `(Q₀,Q₁,P,S)`. -/
def d1InvariantQuad (z : D1N2Config) : ℂ × ℂ × ℂ × ℂ :=
  (d1Q0 z, d1Q1 z, d1P01 z, d1S01 z)

/-- Equality of invariant quadruples implies equality of `R`. -/
lemma d1R01_eq_of_invariantQuad_eq {z w : D1N2Config}
    (hquad : d1InvariantQuad z = d1InvariantQuad w) :
    d1R01 z = d1R01 w := by
  have hP : d1P01 z = d1P01 w := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquad
  have hS : d1S01 z = d1S01 w := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquad
  rw [d1R01_eq_of_P01_S01, d1R01_eq_of_P01_S01, hP, hS]

/-- Equality of invariant quadruples implies equality of `T`. -/
lemma d1T01_eq_of_invariantQuad_eq {z w : D1N2Config}
    (hquad : d1InvariantQuad z = d1InvariantQuad w) :
    d1T01 z = d1T01 w := by
  have hP : d1P01 z = d1P01 w := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquad
  have hS : d1S01 z = d1S01 w := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquad
  rw [d1T01_eq_of_P01_S01, d1T01_eq_of_P01_S01, hP, hS]

/-- The invariant triple is invariant under complex Lorentz action. -/
lemma d1InvariantTriple_lorentzAction (Λ : ComplexLorentzGroup 1) (z : D1N2Config) :
    d1InvariantTriple (complexLorentzAction Λ z) = d1InvariantTriple z := by
  simp [d1InvariantTriple, d1Q0_lorentzAction, d1Q1_lorentzAction, d1P01_lorentzAction]

/-- The signed invariant quadruple is Lorentz-invariant. -/
lemma d1InvariantQuad_lorentzAction (Λ : ComplexLorentzGroup 1) (z : D1N2Config) :
    d1InvariantQuad (complexLorentzAction Λ z) = d1InvariantQuad z := by
  simp [d1InvariantQuad, d1Q0_lorentzAction, d1Q1_lorentzAction,
    d1P01_lorentzAction, d1S01_lorentzAction]

/-- The invariant triple under swap `(0,1)` exchanges the first two slots. -/
lemma d1InvariantTriple_swap01 (z : D1N2Config) :
    d1InvariantTriple (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) =
      (d1Q1 z, d1Q0 z, d1P01 z) := by
  simp [d1InvariantTriple, d1Q0_swap01, d1Q1_swap01, d1P01_swap01]

/-- Under swap `(0,1)`, the signed quadruple transforms by
`(Q₀,Q₁,P,S) ↦ (Q₁,Q₀,P,-S)`. -/
lemma d1InvariantQuad_swap01 (z : D1N2Config) :
    d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) =
      (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
  simp [d1InvariantQuad, d1Q0_swap01, d1Q1_swap01, d1P01_swap01, d1S01_swap01]

private def d1UAt (z : D1N2Config) (k : Fin 2) : ℂ := z k 0 + z k 1

private def d1VAt (z : D1N2Config) (k : Fin 2) : ℂ := z k 0 - z k 1

private lemma d1_coord0_eq_UV (z : D1N2Config) (k : Fin 2) :
    z k 0 = (d1UAt z k + d1VAt z k) / 2 := by
  simp [d1UAt, d1VAt]

private lemma d1_coord1_eq_UV (z : D1N2Config) (k : Fin 2) :
    z k 1 = (d1UAt z k - d1VAt z k) / 2 := by
  simp [d1UAt, d1VAt]

private def d1ScalarBoostMatrix (lmb : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((lmb + lmb⁻¹) / 2), ((lmb - lmb⁻¹) / 2);
    ((lmb - lmb⁻¹) / 2), ((lmb + lmb⁻¹) / 2)]

private lemma d1_scalarBoost_rel (lmb : ℂ) (hlmb : lmb ≠ 0) :
    ((lmb + lmb⁻¹) / 2) * ((lmb + lmb⁻¹) / 2) -
      ((lmb - lmb⁻¹) / 2) * ((lmb - lmb⁻¹) / 2) = (1 : ℂ) := by
  field_simp [hlmb]
  ring

private lemma d1ScalarBoostMatrix_metric (lmb : ℂ) (hlmb : lmb ≠ 0) :
    ∀ (μ ν : Fin (1 + 1)),
      ∑ α : Fin (1 + 1),
        (minkowskiSignature 1 α : ℂ) * d1ScalarBoostMatrix lmb α μ * d1ScalarBoostMatrix lmb α ν =
      if μ = ν then (minkowskiSignature 1 μ : ℂ) else 0 := by
  intro μ ν
  have hrel := d1_scalarBoost_rel lmb hlmb
  fin_cases μ <;> fin_cases ν
  · calc
      ∑ α : Fin 2,
          (minkowskiSignature 1 α : ℂ) * d1ScalarBoostMatrix lmb α 0 * d1ScalarBoostMatrix lmb α 0
          = (-1 : ℂ) * (((lmb + lmb⁻¹) / 2) * ((lmb + lmb⁻¹) / 2)) +
              (((lmb - lmb⁻¹) / 2) * ((lmb - lmb⁻¹) / 2)) := by
              simp [d1ScalarBoostMatrix, minkowskiSignature, Fin.sum_univ_two]
      _ = -((((lmb + lmb⁻¹) / 2) * ((lmb + lmb⁻¹) / 2) -
              ((lmb - lmb⁻¹) / 2) * ((lmb - lmb⁻¹) / 2))) := by ring
      _ = (-1 : ℂ) := by simp [hrel]
      _ = if (0 : Fin 2) = (0 : Fin 2) then (minkowskiSignature 1 (0 : Fin 2) : ℂ) else 0 := by
            simp [minkowskiSignature]
  · calc
      ∑ α : Fin 2,
          (minkowskiSignature 1 α : ℂ) * d1ScalarBoostMatrix lmb α 0 * d1ScalarBoostMatrix lmb α 1
          = (-1 : ℂ) * (((lmb + lmb⁻¹) / 2) * ((lmb - lmb⁻¹) / 2)) +
              (((lmb - lmb⁻¹) / 2) * ((lmb + lmb⁻¹) / 2)) := by
              simp [d1ScalarBoostMatrix, minkowskiSignature, Fin.sum_univ_two]
      _ = 0 := by ring
      _ = if (0 : Fin 2) = (1 : Fin 2) then (minkowskiSignature 1 (0 : Fin 2) : ℂ) else 0 := by
            simp
  · calc
      ∑ α : Fin 2,
          (minkowskiSignature 1 α : ℂ) * d1ScalarBoostMatrix lmb α 1 * d1ScalarBoostMatrix lmb α 0
          = (-1 : ℂ) * (((lmb - lmb⁻¹) / 2) * ((lmb + lmb⁻¹) / 2)) +
              (((lmb + lmb⁻¹) / 2) * ((lmb - lmb⁻¹) / 2)) := by
              simp [d1ScalarBoostMatrix, minkowskiSignature, Fin.sum_univ_two]
      _ = 0 := by ring
      _ = if (1 : Fin 2) = (0 : Fin 2) then (minkowskiSignature 1 (1 : Fin 2) : ℂ) else 0 := by
            simp
  · calc
      ∑ α : Fin 2,
          (minkowskiSignature 1 α : ℂ) * d1ScalarBoostMatrix lmb α 1 * d1ScalarBoostMatrix lmb α 1
          = (-1 : ℂ) * (((lmb - lmb⁻¹) / 2) * ((lmb - lmb⁻¹) / 2)) +
              (((lmb + lmb⁻¹) / 2) * ((lmb + lmb⁻¹) / 2)) := by
              simp [d1ScalarBoostMatrix, minkowskiSignature, Fin.sum_univ_two]
      _ = (((lmb + lmb⁻¹) / 2) * ((lmb + lmb⁻¹) / 2) -
            ((lmb - lmb⁻¹) / 2) * ((lmb - lmb⁻¹) / 2)) := by ring
      _ = (1 : ℂ) := hrel
      _ = if (1 : Fin 2) = (1 : Fin 2) then (minkowskiSignature 1 (1 : Fin 2) : ℂ) else 0 := by
            simp [minkowskiSignature]

private lemma d1ScalarBoostMatrix_det (lmb : ℂ) (hlmb : lmb ≠ 0) :
    (d1ScalarBoostMatrix lmb).det = (1 : ℂ) := by
  have hrel := d1_scalarBoost_rel lmb hlmb
  calc
    (d1ScalarBoostMatrix lmb).det
        = ((lmb + lmb⁻¹) / 2) * ((lmb + lmb⁻¹) / 2) -
            ((lmb - lmb⁻¹) / 2) * ((lmb - lmb⁻¹) / 2) := by
              simp [d1ScalarBoostMatrix, Matrix.det_fin_two]
    _ = (1 : ℂ) := hrel

private def d1ScalarBoost (lmb : ℂ) (hlmb : lmb ≠ 0) : ComplexLorentzGroup 1 where
  val := d1ScalarBoostMatrix lmb
  metric_preserving := d1ScalarBoostMatrix_metric lmb hlmb
  proper := d1ScalarBoostMatrix_det lmb hlmb

private lemma d1UAt_scalarBoost (lmb : ℂ) (hlmb : lmb ≠ 0) (z : D1N2Config) (k : Fin 2) :
    d1UAt (complexLorentzAction (d1ScalarBoost lmb hlmb) z) k = lmb * d1UAt z k := by
  calc
    d1UAt (complexLorentzAction (d1ScalarBoost lmb hlmb) z) k
        = ((∑ ν, (d1ScalarBoost lmb hlmb).val 0 ν * z k ν) +
            (∑ ν, (d1ScalarBoost lmb hlmb).val 1 ν * z k ν)) := by
              simp [d1UAt, complexLorentzAction]
    _ = (((lmb + lmb⁻¹) / 2) * z k 0 + ((lmb - lmb⁻¹) / 2) * z k 1) +
        (((lmb - lmb⁻¹) / 2) * z k 0 + ((lmb + lmb⁻¹) / 2) * z k 1) := by
          simp [d1ScalarBoost, d1ScalarBoostMatrix, Fin.sum_univ_two]
    _ = lmb * (z k 0 + z k 1) := by
          field_simp [hlmb]
          ring
    _ = lmb * d1UAt z k := by simp [d1UAt]

private lemma d1VAt_scalarBoost (lmb : ℂ) (hlmb : lmb ≠ 0) (z : D1N2Config) (k : Fin 2) :
    d1VAt (complexLorentzAction (d1ScalarBoost lmb hlmb) z) k = lmb⁻¹ * d1VAt z k := by
  calc
    d1VAt (complexLorentzAction (d1ScalarBoost lmb hlmb) z) k
        = ((∑ ν, (d1ScalarBoost lmb hlmb).val 0 ν * z k ν) -
            (∑ ν, (d1ScalarBoost lmb hlmb).val 1 ν * z k ν)) := by
              simp [d1VAt, complexLorentzAction]
    _ = (((lmb + lmb⁻¹) / 2) * z k 0 + ((lmb - lmb⁻¹) / 2) * z k 1) -
        (((lmb - lmb⁻¹) / 2) * z k 0 + ((lmb + lmb⁻¹) / 2) * z k 1) := by
          simp [d1ScalarBoost, d1ScalarBoostMatrix, Fin.sum_univ_two]
    _ = lmb⁻¹ * (z k 0 - z k 1) := by
          field_simp [hlmb]
          ring
    _ = lmb⁻¹ * d1VAt z k := by simp [d1VAt]

/-- On `FT_{1,2}`, equality of signed invariant quadruples implies same
complex Lorentz orbit. -/
theorem d1_exists_lorentz_of_sameInvariantQuad_on_FT
    {z w : D1N2Config}
    (hz : z ∈ ForwardTube 1 2)
    (hw : w ∈ ForwardTube 1 2)
    (hquad : d1InvariantQuad z = d1InvariantQuad w) :
    ∃ Λ : ComplexLorentzGroup 1, w = complexLorentzAction Λ z := by
  have hQ0 : d1Q0 z = d1Q0 w := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.1) hquad
  have hR : d1R01 z = d1R01 w := d1R01_eq_of_invariantQuad_eq hquad
  have hT : d1T01 z = d1T01 w := d1T01_eq_of_invariantQuad_eq hquad
  have hU0z_ne : d1U0 z ≠ 0 := d1U0_ne_zero_of_forward z hz
  have hU0w_ne : d1U0 w ≠ 0 := d1U0_ne_zero_of_forward w hw
  have hV0w_ne : d1V0 w ≠ 0 := d1V0_ne_zero_of_forward w hw
  let lmb : ℂ := d1U0 w / d1U0 z
  have hlmb_ne : lmb ≠ 0 := by
    dsimp [lmb]
    exact div_ne_zero hU0w_ne hU0z_ne
  have hU0_scale : d1U0 w = lmb * d1U0 z := by
    dsimp [lmb]
    field_simp [hU0z_ne]
  have hUw_mul_inv : d1U0 w * lmb⁻¹ = d1U0 z := by
    dsimp [lmb]
    field_simp [hU0z_ne, hU0w_ne]
  have hQ0uv : d1U0 z * d1V0 z = d1U0 w * d1V0 w := by
    rw [d1Q0_eq_neg_U0_mul_V0, d1Q0_eq_neg_U0_mul_V0] at hQ0
    simpa using congrArg Neg.neg hQ0
  have hRuv : d1U0 z * d1V1 z = d1U0 w * d1V1 w := by
    simpa [d1R01] using hR
  have hTuv : d1U1 z * d1V0 z = d1U1 w * d1V0 w := by
    simpa [d1T01] using hT
  have hV0_scale : d1V0 w = lmb⁻¹ * d1V0 z := by
    apply (mul_left_cancel₀ hU0w_ne)
    calc
      d1U0 w * d1V0 w = d1U0 z * d1V0 z := hQ0uv.symm
      _ = (d1U0 w * lmb⁻¹) * d1V0 z := by rw [hUw_mul_inv]
      _ = d1U0 w * (lmb⁻¹ * d1V0 z) := by ring
  have hV0_unscale : d1V0 z = lmb * d1V0 w := by
    calc
      d1V0 z = (lmb * lmb⁻¹) * d1V0 z := by simp [hlmb_ne]
      _ = lmb * (lmb⁻¹ * d1V0 z) := by ring
      _ = lmb * d1V0 w := by rw [hV0_scale]
  have hV1_scale : d1V1 w = lmb⁻¹ * d1V1 z := by
    apply (mul_left_cancel₀ hU0w_ne)
    calc
      d1U0 w * d1V1 w = d1U0 z * d1V1 z := hRuv.symm
      _ = (d1U0 w * lmb⁻¹) * d1V1 z := by rw [hUw_mul_inv]
      _ = d1U0 w * (lmb⁻¹ * d1V1 z) := by ring
  have hU1_scale : d1U1 w = lmb * d1U1 z := by
    apply (mul_right_cancel₀ hV0w_ne)
    calc
      d1U1 w * d1V0 w = d1U1 z * d1V0 z := hTuv.symm
      _ = d1U1 z * (lmb * d1V0 w) := by rw [hV0_unscale]
      _ = (lmb * d1U1 z) * d1V0 w := by ring
  have hU_scale : ∀ k : Fin 2, d1UAt w k = lmb * d1UAt z k := by
    intro k
    fin_cases k
    · simpa [d1UAt, d1U0] using hU0_scale
    · simpa [d1UAt, d1U1] using hU1_scale
  have hV_scale : ∀ k : Fin 2, d1VAt w k = lmb⁻¹ * d1VAt z k := by
    intro k
    fin_cases k
    · simpa [d1VAt, d1V0] using hV0_scale
    · simpa [d1VAt, d1V1] using hV1_scale
  refine ⟨d1ScalarBoost lmb hlmb_ne, ?_⟩
  ext k μ
  fin_cases μ
  · calc
      w k 0 = (d1UAt w k + d1VAt w k) / 2 := d1_coord0_eq_UV w k
      _ = (lmb * d1UAt z k + lmb⁻¹ * d1VAt z k) / 2 := by
            rw [hU_scale k, hV_scale k]
      _ = (d1UAt (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k +
            d1VAt (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k) / 2 := by
              rw [d1UAt_scalarBoost lmb hlmb_ne z k, d1VAt_scalarBoost lmb hlmb_ne z k]
      _ = (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k 0 := by
            symm
            exact d1_coord0_eq_UV (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k
  · calc
      w k 1 = (d1UAt w k - d1VAt w k) / 2 := d1_coord1_eq_UV w k
      _ = (lmb * d1UAt z k - lmb⁻¹ * d1VAt z k) / 2 := by
            rw [hU_scale k, hV_scale k]
      _ = (d1UAt (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k -
            d1VAt (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k) / 2 := by
              rw [d1UAt_scalarBoost lmb hlmb_ne z k, d1VAt_scalarBoost lmb hlmb_ne z k]
      _ = (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k 1 := by
            symm
            exact d1_coord1_eq_UV (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k

/-- Equality of signed invariant quadruples implies same complex Lorentz orbit
under the scalar-boost solver nonvanishing hypotheses. -/
theorem d1_exists_lorentz_of_sameInvariantQuad_of_nonzeroU0V0
    {z w : D1N2Config}
    (hU0z_ne : d1U0 z ≠ 0)
    (hU0w_ne : d1U0 w ≠ 0)
    (hV0w_ne : d1V0 w ≠ 0)
    (hquad : d1InvariantQuad z = d1InvariantQuad w) :
    ∃ Λ : ComplexLorentzGroup 1, w = complexLorentzAction Λ z := by
  have hQ0 : d1Q0 z = d1Q0 w := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.1) hquad
  have hR : d1R01 z = d1R01 w := d1R01_eq_of_invariantQuad_eq hquad
  have hT : d1T01 z = d1T01 w := d1T01_eq_of_invariantQuad_eq hquad
  let lmb : ℂ := d1U0 w / d1U0 z
  have hlmb_ne : lmb ≠ 0 := by
    dsimp [lmb]
    exact div_ne_zero hU0w_ne hU0z_ne
  have hU0_scale : d1U0 w = lmb * d1U0 z := by
    dsimp [lmb]
    field_simp [hU0z_ne]
  have hUw_mul_inv : d1U0 w * lmb⁻¹ = d1U0 z := by
    dsimp [lmb]
    field_simp [hU0z_ne, hU0w_ne]
  have hQ0uv : d1U0 z * d1V0 z = d1U0 w * d1V0 w := by
    rw [d1Q0_eq_neg_U0_mul_V0, d1Q0_eq_neg_U0_mul_V0] at hQ0
    simpa using congrArg Neg.neg hQ0
  have hRuv : d1U0 z * d1V1 z = d1U0 w * d1V1 w := by
    simpa [d1R01] using hR
  have hTuv : d1U1 z * d1V0 z = d1U1 w * d1V0 w := by
    simpa [d1T01] using hT
  have hV0_scale : d1V0 w = lmb⁻¹ * d1V0 z := by
    apply (mul_left_cancel₀ hU0w_ne)
    calc
      d1U0 w * d1V0 w = d1U0 z * d1V0 z := hQ0uv.symm
      _ = (d1U0 w * lmb⁻¹) * d1V0 z := by rw [hUw_mul_inv]
      _ = d1U0 w * (lmb⁻¹ * d1V0 z) := by ring
  have hV0_unscale : d1V0 z = lmb * d1V0 w := by
    calc
      d1V0 z = (lmb * lmb⁻¹) * d1V0 z := by simp [hlmb_ne]
      _ = lmb * (lmb⁻¹ * d1V0 z) := by ring
      _ = lmb * d1V0 w := by rw [hV0_scale]
  have hV1_scale : d1V1 w = lmb⁻¹ * d1V1 z := by
    apply (mul_left_cancel₀ hU0w_ne)
    calc
      d1U0 w * d1V1 w = d1U0 z * d1V1 z := hRuv.symm
      _ = (d1U0 w * lmb⁻¹) * d1V1 z := by rw [hUw_mul_inv]
      _ = d1U0 w * (lmb⁻¹ * d1V1 z) := by ring
  have hU1_scale : d1U1 w = lmb * d1U1 z := by
    apply (mul_right_cancel₀ hV0w_ne)
    calc
      d1U1 w * d1V0 w = d1U1 z * d1V0 z := hTuv.symm
      _ = d1U1 z * (lmb * d1V0 w) := by rw [hV0_unscale]
      _ = (lmb * d1U1 z) * d1V0 w := by ring
  have hU_scale : ∀ k : Fin 2, d1UAt w k = lmb * d1UAt z k := by
    intro k
    fin_cases k
    · simpa [d1UAt, d1U0] using hU0_scale
    · simpa [d1UAt, d1U1] using hU1_scale
  have hV_scale : ∀ k : Fin 2, d1VAt w k = lmb⁻¹ * d1VAt z k := by
    intro k
    fin_cases k
    · simpa [d1VAt, d1V0] using hV0_scale
    · simpa [d1VAt, d1V1] using hV1_scale
  refine ⟨d1ScalarBoost lmb hlmb_ne, ?_⟩
  ext k μ
  fin_cases μ
  · calc
      w k 0 = (d1UAt w k + d1VAt w k) / 2 := d1_coord0_eq_UV w k
      _ = (lmb * d1UAt z k + lmb⁻¹ * d1VAt z k) / 2 := by
            rw [hU_scale k, hV_scale k]
      _ = (d1UAt (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k +
            d1VAt (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k) / 2 := by
              rw [d1UAt_scalarBoost lmb hlmb_ne z k, d1VAt_scalarBoost lmb hlmb_ne z k]
      _ = (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k 0 := by
            symm
            exact d1_coord0_eq_UV (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k
  · calc
      w k 1 = (d1UAt w k - d1VAt w k) / 2 := d1_coord1_eq_UV w k
      _ = (lmb * d1UAt z k - lmb⁻¹ * d1VAt z k) / 2 := by
            rw [hU_scale k, hV_scale k]
      _ = (d1UAt (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k -
            d1VAt (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k) / 2 := by
              rw [d1UAt_scalarBoost lmb hlmb_ne z k, d1VAt_scalarBoost lmb hlmb_ne z k]
      _ = (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k 1 := by
            symm
            exact d1_coord1_eq_UV (complexLorentzAction (d1ScalarBoost lmb hlmb_ne) z) k

/-- Real `Q₀` invariant, in the same normalization as local commutativity. -/
abbrev d1Q0R (x : Fin 2 → Fin (1 + 1) → ℝ) : ℝ :=
  d1MinkowskiBilin (x 0) (x 0)

/-- Real `Q₁` invariant, in the same normalization as local commutativity. -/
abbrev d1Q1R (x : Fin 2 → Fin (1 + 1) → ℝ) : ℝ :=
  d1MinkowskiBilin (x 1) (x 1)

/-- Real `P` invariant, in the same normalization as local commutativity. -/
abbrev d1P01R (x : Fin 2 → Fin (1 + 1) → ℝ) : ℝ :=
  d1MinkowskiBilin (x 0) (x 1)

/-- Real `S` invariant (signed area coordinate), matching `d1S01` under
`realEmbed`. -/
abbrev d1S01R (x : Fin 2 → Fin (1 + 1) → ℝ) : ℝ :=
  (-2 : ℝ) * ((x 0 0) * (x 1 1) - (x 0 1) * (x 1 0))

/-- Complex `Q₀` on `realEmbed x` is the real invariant `d1Q0R x`. -/
lemma d1Q0_realEmbed (x : Fin 2 → Fin (1 + 1) → ℝ) :
    d1Q0 (realEmbed x) = (d1Q0R x : ℂ) := by
  simp [d1Q0, d1Q0R, d1MinkowskiBilinC, d1MinkowskiBilin, realEmbed]

/-- Complex `Q₁` on `realEmbed x` is the real invariant `d1Q1R x`. -/
lemma d1Q1_realEmbed (x : Fin 2 → Fin (1 + 1) → ℝ) :
    d1Q1 (realEmbed x) = (d1Q1R x : ℂ) := by
  simp [d1Q1, d1Q1R, d1MinkowskiBilinC, d1MinkowskiBilin, realEmbed]

/-- Complex `P` on `realEmbed x` is the real invariant `d1P01R x`. -/
lemma d1P01_realEmbed (x : Fin 2 → Fin (1 + 1) → ℝ) :
    d1P01 (realEmbed x) = (d1P01R x : ℂ) := by
  simp [d1P01, d1P01R, d1MinkowskiBilinC, d1MinkowskiBilin, realEmbed]

/-- Complex `S` on `realEmbed x` is the real signed-area invariant `d1S01R x`. -/
lemma d1S01_realEmbed (x : Fin 2 → Fin (1 + 1) → ℝ) :
    d1S01 (realEmbed x) = (d1S01R x : ℂ) := by
  simp [d1S01, d1S01R, d1PointMatrix, Matrix.det_fin_two, realEmbed]
  ring

/-- `d=1,n=2` adjacent spacelike expression in terms of `(Q₀,Q₁,P)`. -/
lemma d1_adj_spacelike_expr_eq_q0q1p (x : Fin 2 → Fin (1 + 1) → ℝ) :
    (∑ μ, minkowskiSignature 1 μ * (x 1 μ - x 0 μ) ^ 2) =
      d1Q0R x + d1Q1R x - 2 * d1P01R x := by
  simpa [d1Q0R, d1Q1R, d1P01R] using d1_n2_adj_spacelike_expr_eq_invariants x

/-- Explicit complex-coordinate chart for `d=1,n=2`:
`z₀=(a,b)` and `z₁=(c,d)`. -/
def d1N2ComplexConfig (a b c d : ℂ) : D1N2Config :=
  fun k μ =>
    if k = 0 then
      if μ = 0 then a else b
    else
      if μ = 0 then c else d

@[simp] lemma d1N2ComplexConfig_00 (a b c d : ℂ) :
    d1N2ComplexConfig a b c d 0 0 = a := by
  simp [d1N2ComplexConfig]

@[simp] lemma d1N2ComplexConfig_01 (a b c d : ℂ) :
    d1N2ComplexConfig a b c d 0 1 = b := by
  simp [d1N2ComplexConfig]

@[simp] lemma d1N2ComplexConfig_10 (a b c d : ℂ) :
    d1N2ComplexConfig a b c d 1 0 = c := by
  simp [d1N2ComplexConfig]

@[simp] lemma d1N2ComplexConfig_11 (a b c d : ℂ) :
    d1N2ComplexConfig a b c d 1 1 = d := by
  simp [d1N2ComplexConfig]

lemma d1Q0_complexConfig (a b c d : ℂ) :
    d1Q0 (d1N2ComplexConfig a b c d) = -(a ^ 2) + b ^ 2 := by
  simp [d1Q0, d1MinkowskiBilinC, d1N2ComplexConfig, Fin.sum_univ_two, minkowskiSignature]
  ring

lemma d1Q1_complexConfig (a b c d : ℂ) :
    d1Q1 (d1N2ComplexConfig a b c d) = -(c ^ 2) + d ^ 2 := by
  simp [d1Q1, d1MinkowskiBilinC, d1N2ComplexConfig, Fin.sum_univ_two, minkowskiSignature]
  ring

lemma d1P01_complexConfig (a b c d : ℂ) :
    d1P01 (d1N2ComplexConfig a b c d) = -(a * c) + b * d := by
  simp [d1P01, d1MinkowskiBilinC, d1N2ComplexConfig, Fin.sum_univ_two, minkowskiSignature]

lemma d1S01_complexConfig (a b c d : ℂ) :
    d1S01 (d1N2ComplexConfig a b c d) = (-2 : ℂ) * (a * d - b * c) := by
  simp [d1S01, d1PointMatrix, d1N2ComplexConfig, Matrix.det_fin_two]
  ring

lemma d1InvariantQuad_complexConfig (a b c d : ℂ) :
    d1InvariantQuad (d1N2ComplexConfig a b c d) =
      (-(a ^ 2) + b ^ 2, -(c ^ 2) + d ^ 2, -(a * c) + b * d,
        (-2 : ℂ) * (a * d - b * c)) := by
  simp [d1InvariantQuad, d1Q0_complexConfig, d1Q1_complexConfig,
    d1P01_complexConfig, d1S01_complexConfig]

lemma d1InvariantQuad_complexConfig_on_quadric (a b c d : ℂ) :
    (d1S01 (d1N2ComplexConfig a b c d)) ^ 2 =
      4 * ((d1P01 (d1N2ComplexConfig a b c d)) ^ 2 -
        d1Q0 (d1N2ComplexConfig a b c d) * d1Q1 (d1N2ComplexConfig a b c d)) := by
  simp [d1Q0_complexConfig, d1Q1_complexConfig, d1P01_complexConfig,
    d1S01_complexConfig]
  ring

lemma d1InvariantQuad_complexConfig_swap (a b c d : ℂ) :
    d1InvariantQuad (d1N2ComplexConfig c d a b) =
      (d1Q1 (d1N2ComplexConfig a b c d),
        d1Q0 (d1N2ComplexConfig a b c d),
        d1P01 (d1N2ComplexConfig a b c d),
        -d1S01 (d1N2ComplexConfig a b c d)) := by
  simp [d1InvariantQuad, d1Q0_complexConfig, d1Q1_complexConfig,
    d1P01_complexConfig, d1S01_complexConfig]
  constructor <;> ring

/-- `d=1,n=2` invariant-section chart with free parameter `v0`.
It is the standard light-cone parametrization:
`u0 = q0 / v0`, `v0 = v0`, `u1 = (p - s/2)/v0`, `v1 = (p + s/2)*v0/q0`,
converted to `(t,x)` coordinates by
`t = (u+v)/2`, `x = (u-v)/2`. -/
def d1N2InvariantSection (q0 p s v0 : ℂ) : D1N2Config :=
  d1N2ComplexConfig
    (((q0 / v0) + v0) / 2)
    (((q0 / v0) - v0) / 2)
    ((((p - s / 2) / v0) + ((p + s / 2) * v0 / q0)) / 2)
    ((((p - s / 2) / v0) - ((p + s / 2) * v0 / q0)) / 2)

@[simp] lemma d1U0_invariantSection (q0 p s v0 : ℂ) :
    d1U0 (d1N2InvariantSection q0 p s v0) = q0 / v0 := by
  simp [d1N2InvariantSection, d1U0]
  ring

@[simp] lemma d1V0_invariantSection (q0 p s v0 : ℂ) :
    d1V0 (d1N2InvariantSection q0 p s v0) = v0 := by
  simp [d1N2InvariantSection, d1V0]
  ring

@[simp] lemma d1U1_invariantSection (q0 p s v0 : ℂ) :
    d1U1 (d1N2InvariantSection q0 p s v0) = (p - s / 2) / v0 := by
  simp [d1N2InvariantSection, d1U1]
  ring

@[simp] lemma d1V1_invariantSection (q0 p s v0 : ℂ) :
    d1V1 (d1N2InvariantSection q0 p s v0) = (p + s / 2) * v0 / q0 := by
  simp [d1N2InvariantSection, d1V1]
  ring

lemma d1Q0_invariantSection (q0 p s v0 : ℂ) (hv0 : v0 ≠ 0) :
    d1Q0 (d1N2InvariantSection q0 p s v0) = -q0 := by
  rw [d1Q0_eq_neg_U0_mul_V0]
  simp [d1U0_invariantSection, d1V0_invariantSection, hv0]

lemma d1P01_invariantSection (q0 p s v0 : ℂ) (hq0 : q0 ≠ 0) (hv0 : v0 ≠ 0) :
    d1P01 (d1N2InvariantSection q0 p s v0) = -p := by
  have htwo :
      (2 : ℂ) * d1P01 (d1N2InvariantSection q0 p s v0) = -(2 * p) := by
    calc
      (2 : ℂ) * d1P01 (d1N2InvariantSection q0 p s v0)
          = -(
              d1R01 (d1N2InvariantSection q0 p s v0) +
              d1T01 (d1N2InvariantSection q0 p s v0)
            ) := d1_two_mul_P01_eq_neg_R01_add_T01 (d1N2InvariantSection q0 p s v0)
      _ = -(
              (q0 / v0) * ((p + s / 2) * v0 / q0) +
              ((p - s / 2) / v0) * v0
            ) := by
              simp [d1R01, d1T01, d1U0_invariantSection, d1V1_invariantSection,
                d1U1_invariantSection, d1V0_invariantSection]
      _ = -(2 * p) := by
            field_simp [hq0, hv0]
            ring
  have hdiv : d1P01 (d1N2InvariantSection q0 p s v0) = (-(2 * p)) / 2 := by
    simpa [mul_assoc] using congrArg (fun t : ℂ => t / (2 : ℂ)) htwo
  calc
    d1P01 (d1N2InvariantSection q0 p s v0) = (-(2 * p)) / 2 := hdiv
    _ = -p := by ring

lemma d1S01_invariantSection (q0 p s v0 : ℂ) (hq0 : q0 ≠ 0) (hv0 : v0 ≠ 0) :
    d1S01 (d1N2InvariantSection q0 p s v0) = s := by
  calc
    d1S01 (d1N2InvariantSection q0 p s v0)
        = d1R01 (d1N2InvariantSection q0 p s v0) -
            d1T01 (d1N2InvariantSection q0 p s v0) := d1S01_eq_R01_sub_T01 (d1N2InvariantSection q0 p s v0)
    _ = (q0 / v0) * ((p + s / 2) * v0 / q0) - ((p - s / 2) / v0) * v0 := by
          simp [d1R01, d1T01, d1U0_invariantSection, d1V1_invariantSection,
            d1U1_invariantSection, d1V0_invariantSection]
    _ = s := by
          field_simp [hq0, hv0]
          ring

lemma d1Q1_invariantSection (q0 p s v0 : ℂ) (hq0 : q0 ≠ 0) (hv0 : v0 ≠ 0) :
    d1Q1 (d1N2InvariantSection q0 p s v0) = -((p ^ 2 - (s ^ 2) / 4) / q0) := by
  rw [d1Q1_eq_neg_U1_mul_V1]
  calc
    -(d1U1 (d1N2InvariantSection q0 p s v0) * d1V1 (d1N2InvariantSection q0 p s v0))
        = -(((p - s / 2) / v0) * (((p + s / 2) * v0) / q0)) := by
            simp [d1U1_invariantSection, d1V1_invariantSection]
    _ = -((p ^ 2 - (s ^ 2) / 4) / q0) := by
          field_simp [hq0, hv0]
          ring

lemma d1InvariantQuad_invariantSection
    (q0 p s v0 : ℂ) (hq0 : q0 ≠ 0) (hv0 : v0 ≠ 0) :
    d1InvariantQuad (d1N2InvariantSection q0 p s v0) =
      (-q0, -((p ^ 2 - (s ^ 2) / 4) / q0), -p, s) := by
  simp [d1InvariantQuad, d1Q0_invariantSection, d1Q1_invariantSection,
    d1P01_invariantSection, d1S01_invariantSection, hq0, hv0]

/-- Canonical section point with fixed light-cone gauge `v0 = I`. -/
def d1N2InvariantSectionPoint (q0 p s : ℂ) : D1N2Config :=
  d1N2InvariantSection q0 p s I

/-- Explicit open-domain conditions (in invariant variables) ensuring the
canonical section point lies in `FT_{1,2}`. -/
def d1N2InvariantSectionDomain (q0 p s : ℂ) : Prop :=
  q0 ≠ 0 ∧
  0 < (-q0.re) ∧
  0 < (q0 - p + s / 2).re ∧
  0 < (((p + s / 2) / q0 - 1).re)

lemma d1N2InvariantSectionPoint_mem_forwardTube_of_domain
    {q0 p s : ℂ}
    (hdom : d1N2InvariantSectionDomain q0 p s) :
    d1N2InvariantSectionPoint q0 p s ∈ ForwardTube 1 2 := by
  rcases hdom with ⟨hq0, hq0re, hplus, hminus⟩
  let z : D1N2Config := d1N2InvariantSectionPoint q0 p s
  have hz0_plus :
      (fun μ => (z 0 μ).im) 0 + (fun μ => (z 0 μ).im) 1 > 0 := by
    have hu0 :
        (d1U0 z).im = -q0.re := by
      dsimp [z, d1N2InvariantSectionPoint]
      simp [d1U0_invariantSection, div_eq_mul_inv]
    have hsum :
        (fun μ => (z 0 μ).im) 0 + (fun μ => (z 0 μ).im) 1 = (d1U0 z).im := by
      simp [d1U0]
    rw [hsum, hu0]
    simpa using hq0re
  have hz0_minus :
      (fun μ => (z 0 μ).im) 0 - (fun μ => (z 0 μ).im) 1 > 0 := by
    have hv0 :
        (d1V0 z).im = (1 : ℝ) := by
      dsimp [z, d1N2InvariantSectionPoint]
      simp [d1V0_invariantSection]
    have hdiff :
        (fun μ => (z 0 μ).im) 0 - (fun μ => (z 0 μ).im) 1 = (d1V0 z).im := by
      simp [d1V0, sub_eq_add_neg]
    rw [hdiff, hv0]
    norm_num
  have hz0cone : InOpenForwardCone 1 (fun μ => (z 0 μ).im) :=
    (inOpenForwardCone_d1_iff_pm (fun μ => (z 0 μ).im)).2 ⟨hz0_plus, hz0_minus⟩
  have hzdiff_plus :
      (fun μ => (z 1 μ - z 0 μ).im) 0 + (fun μ => (z 1 μ - z 0 μ).im) 1 > 0 := by
    have hu_diff :
        ((d1U1 z - d1U0 z).im) = (q0 - p + s / 2).re := by
      dsimp [z, d1N2InvariantSectionPoint]
      simp [d1U1_invariantSection, d1U0_invariantSection, div_eq_mul_inv]
      ring
    have hsum :
        (fun μ => (z 1 μ - z 0 μ).im) 0 + (fun μ => (z 1 μ - z 0 μ).im) 1 =
          (d1U1 z - d1U0 z).im := by
      simp [d1U0, d1U1, sub_eq_add_neg]
      ring
    rw [hsum, hu_diff]
    simpa using hplus
  have hzdiff_minus :
      (fun μ => (z 1 μ - z 0 μ).im) 0 - (fun μ => (z 1 μ - z 0 μ).im) 1 > 0 := by
    have hv_diff :
        ((d1V1 z - d1V0 z).im) = (((p + s / 2) / q0 - 1).re) := by
      dsimp [z, d1N2InvariantSectionPoint]
      simp [d1V1_invariantSection, d1V0_invariantSection, div_eq_mul_inv]
      ring
    have hdiff :
        (fun μ => (z 1 μ - z 0 μ).im) 0 - (fun μ => (z 1 μ - z 0 μ).im) 1 =
          (d1V1 z - d1V0 z).im := by
      simp [d1V0, d1V1, sub_eq_add_neg]
      ring
    rw [hdiff, hv_diff]
    simpa using hminus
  have hzdiffcone : InOpenForwardCone 1 (fun μ => (z 1 μ - z 0 μ).im) :=
    (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).2
      ⟨hzdiff_plus, hzdiff_minus⟩
  exact (forwardTube_d1_n2_iff z).2 ⟨hz0cone, hzdiffcone⟩

/-- Section-side parameter for the swap involution on invariant quadruples. -/
def d1N2InvariantSectionSwapQ0 (q0 p s : ℂ) : ℂ :=
  (p ^ 2 - (s ^ 2) / 4) / q0

lemma d1InvariantQuad_invariantSectionPoint
    (q0 p s : ℂ) (hq0 : q0 ≠ 0) :
    d1InvariantQuad (d1N2InvariantSectionPoint q0 p s) =
      (-q0, -(d1N2InvariantSectionSwapQ0 q0 p s), -p, s) := by
  simpa [d1N2InvariantSectionPoint, d1N2InvariantSectionSwapQ0] using
    d1InvariantQuad_invariantSection q0 p s I hq0 (by simp)

lemma d1InvariantQuad_invariantSectionPoint_swapParams
    (q0 p s : ℂ)
    (hq0 : q0 ≠ 0)
    (hΔ : d1N2InvariantSectionSwapQ0 q0 p s ≠ 0) :
    d1InvariantQuad
      (d1N2InvariantSectionPoint (d1N2InvariantSectionSwapQ0 q0 p s) p (-s)) =
      (-(d1N2InvariantSectionSwapQ0 q0 p s), -q0, -p, -s) := by
  have hquad :
      d1InvariantQuad
        (d1N2InvariantSectionPoint (d1N2InvariantSectionSwapQ0 q0 p s) p (-s)) =
        (-(d1N2InvariantSectionSwapQ0 q0 p s),
          -((p ^ 2 - ((-s) ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s),
          -p, -s) := by
    simpa [d1N2InvariantSectionPoint, d1N2InvariantSectionSwapQ0] using
      d1InvariantQuad_invariantSection
        (d1N2InvariantSectionSwapQ0 q0 p s) p (-s) I hΔ (by simp)
  have hsecond :
      -((p ^ 2 - ((-s) ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s) = -q0 := by
    have hswap :
        p ^ 2 - ((-s) ^ 2) / 4 = p ^ 2 - (s ^ 2) / 4 := by ring
    set Δ : ℂ := p ^ 2 - (s ^ 2) / 4
    have hΔne : Δ ≠ 0 := by
      intro hΔ0
      apply hΔ
      simp [d1N2InvariantSectionSwapQ0, Δ, hΔ0]
    have hnum :
        (p ^ 2 - (s ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s = q0 := by
      calc
        (p ^ 2 - (s ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s
            = Δ / (Δ / q0) := by
                simp [d1N2InvariantSectionSwapQ0, Δ]
        _ = q0 := by
              field_simp [hΔne, hq0]
    calc
      -((p ^ 2 - ((-s) ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s)
          = -((p ^ 2 - (s ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s) := by
              rw [hswap]
      _ = -q0 := by simp [hnum]
  have hsecond' :
      (p ^ 2 - ((-s) ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s = q0 := by
    exact neg_injective hsecond
  have hsecond'' :
      (p ^ 2 - (s ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s = q0 := by
    have hswap2 : p ^ 2 - ((-s) ^ 2) / 4 = p ^ 2 - (s ^ 2) / 4 := by ring
    calc
      (p ^ 2 - (s ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s
          = (p ^ 2 - ((-s) ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s := by
              rw [hswap2]
      _ = q0 := hsecond'
  calc
    d1InvariantQuad
      (d1N2InvariantSectionPoint (d1N2InvariantSectionSwapQ0 q0 p s) p (-s))
        = (-(d1N2InvariantSectionSwapQ0 q0 p s),
            -((p ^ 2 - ((-s) ^ 2) / 4) / d1N2InvariantSectionSwapQ0 q0 p s),
            -p, -s) := hquad
    _ = (-(d1N2InvariantSectionSwapQ0 q0 p s), -q0, -p, -s) := by
          simp [hsecond'']

/-- Explicit real-coordinate chart for `d=1,n=2`:
`x₀=(a,b)` and `x₁=(c,d)`. -/
def d1N2RealConfig (a b c d : ℝ) : Fin 2 → Fin (1 + 1) → ℝ :=
  fun k μ =>
    if k = 0 then
      if μ = 0 then a else b
    else
      if μ = 0 then c else d

@[simp] lemma d1N2RealConfig_00 (a b c d : ℝ) :
    d1N2RealConfig a b c d 0 0 = a := by
  simp [d1N2RealConfig]

@[simp] lemma d1N2RealConfig_01 (a b c d : ℝ) :
    d1N2RealConfig a b c d 0 1 = b := by
  simp [d1N2RealConfig]

@[simp] lemma d1N2RealConfig_10 (a b c d : ℝ) :
    d1N2RealConfig a b c d 1 0 = c := by
  simp [d1N2RealConfig]

@[simp] lemma d1N2RealConfig_11 (a b c d : ℝ) :
    d1N2RealConfig a b c d 1 1 = d := by
  simp [d1N2RealConfig]

@[simp] lemma d1N2ComplexConfig_realCast (a b c d : ℝ) :
    d1N2ComplexConfig a b c d = realEmbed (d1N2RealConfig a b c d) := by
  ext k μ
  fin_cases k <;> fin_cases μ <;>
    simp [d1N2ComplexConfig, d1N2RealConfig, realEmbed]

lemma d1Q0R_realConfig (a b c d : ℝ) :
    d1Q0R (d1N2RealConfig a b c d) = -(a ^ 2) + b ^ 2 := by
  simp [d1Q0R, d1MinkowskiBilin, d1N2RealConfig, Fin.sum_univ_two, minkowskiSignature]
  ring

lemma d1Q1R_realConfig (a b c d : ℝ) :
    d1Q1R (d1N2RealConfig a b c d) = -(c ^ 2) + d ^ 2 := by
  simp [d1Q1R, d1MinkowskiBilin, d1N2RealConfig, Fin.sum_univ_two, minkowskiSignature]
  ring

lemma d1P01R_realConfig (a b c d : ℝ) :
    d1P01R (d1N2RealConfig a b c d) = -(a * c) + b * d := by
  simp [d1P01R, d1MinkowskiBilin, d1N2RealConfig, Fin.sum_univ_two, minkowskiSignature]

lemma d1S01R_realConfig (a b c d : ℝ) :
    d1S01R (d1N2RealConfig a b c d) = (-2 : ℝ) * (a * d - b * c) := by
  simp [d1S01R, d1N2RealConfig]

/-- Real invariant quadruple `(Q₀,Q₁,P,S)` for a `d=1,n=2` real configuration. -/
def d1InvariantQuadR (x : Fin 2 → Fin (1 + 1) → ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (d1Q0R x, d1Q1R x, d1P01R x, d1S01R x)

lemma d1InvariantQuadR_realConfig (a b c d : ℝ) :
    d1InvariantQuadR (d1N2RealConfig a b c d) =
      (-(a ^ 2) + b ^ 2, -(c ^ 2) + d ^ 2, -(a * c) + b * d,
        (-2 : ℝ) * (a * d - b * c)) := by
  simp [d1InvariantQuadR, d1Q0R_realConfig, d1Q1R_realConfig,
    d1P01R_realConfig]

lemma d1InvariantQuadR_realConfig_swap (a b c d : ℝ) :
    d1InvariantQuadR (d1N2RealConfig c d a b) =
      (d1Q1R (d1N2RealConfig a b c d),
        d1Q0R (d1N2RealConfig a b c d),
        d1P01R (d1N2RealConfig a b c d),
        -d1S01R (d1N2RealConfig a b c d)) := by
  simp [d1InvariantQuadR, d1Q0R_realConfig, d1Q1R_realConfig,
    d1P01R_realConfig]
  constructor <;> ring

/-- Explicit real probe point for `d=1,n=2` used in invariant-route Jacobian
checks: `x₀=(1,0)`, `x₁=(1,2)`. -/
def d1N2RealProbePoint : Fin 2 → Fin (1 + 1) → ℝ :=
  d1N2RealConfig 1 0 1 2

@[simp] lemma d1N2RealProbePoint_00 : d1N2RealProbePoint 0 0 = (1 : ℝ) := by
  simp [d1N2RealProbePoint]

@[simp] lemma d1N2RealProbePoint_01 : d1N2RealProbePoint 0 1 = (0 : ℝ) := by
  simp [d1N2RealProbePoint]

@[simp] lemma d1N2RealProbePoint_10 : d1N2RealProbePoint 1 0 = (1 : ℝ) := by
  simp [d1N2RealProbePoint]

@[simp] lemma d1N2RealProbePoint_11 : d1N2RealProbePoint 1 1 = (2 : ℝ) := by
  simp [d1N2RealProbePoint]

lemma d1Q0R_realProbePoint :
    d1Q0R d1N2RealProbePoint = (-1 : ℝ) := by
  simpa [d1N2RealProbePoint] using d1Q0R_realConfig 1 0 1 2

lemma d1Q1R_realProbePoint :
    d1Q1R d1N2RealProbePoint = (3 : ℝ) := by
  norm_num [d1N2RealProbePoint, d1Q1R_realConfig]

lemma d1P01R_realProbePoint :
    d1P01R d1N2RealProbePoint = (-1 : ℝ) := by
  simpa [d1N2RealProbePoint] using d1P01R_realConfig 1 0 1 2

lemma d1S01R_realProbePoint :
    d1S01R d1N2RealProbePoint = (-4 : ℝ) := by
  norm_num [d1N2RealProbePoint, d1S01R_realConfig]

lemma d1_realProbePoint_spacelike :
    d1Q0R d1N2RealProbePoint + d1Q1R d1N2RealProbePoint -
      2 * d1P01R d1N2RealProbePoint > 0 := by
  norm_num [d1Q0R_realProbePoint, d1Q1R_realProbePoint, d1P01R_realProbePoint]

/-- Closed-form spacelike expression for the real coordinate chart. -/
lemma d1_adj_spacelike_expr_realConfig (a b c d : ℝ) :
    d1Q0R (d1N2RealConfig a b c d) + d1Q1R (d1N2RealConfig a b c d) -
      2 * d1P01R (d1N2RealConfig a b c d) =
      (b - d) ^ 2 - (a - c) ^ 2 := by
  simp [d1Q0R_realConfig, d1Q1R_realConfig, d1P01R_realConfig]
  ring

/-- Explicit `3×3` Jacobian minor value at `d1N2RealProbePoint` for the map
`(Q₀,Q₁,P,S)` viewed in real coordinates `(a,b,c,d)`.
This is the minor from rows `(Q₀,Q₁,S)` and columns `(a,c,d)`. -/
def d1N2InvariantJacobianMinorAtProbe : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => -2
    | 1, 1 => -2
    | 1, 2 => 4
    | 2, 0 => -4
    | 2, 2 => -2
    | _, _ => 0

/-- Symbolic real Jacobian minor (rows `(Q₀,Q₁,S)`, columns `(a,c,d)`) for
the chart `(a,b,c,d) ↦ (Q₀,Q₁,P,S)`. -/
def d1N2InvariantJacobianMinorR (a b c d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => (-2 : ℝ) * a
    | 1, 1 => (-2 : ℝ) * c
    | 1, 2 => (2 : ℝ) * d
    | 2, 0 => (-2 : ℝ) * d
    | 2, 1 => (2 : ℝ) * b
    | 2, 2 => (-2 : ℝ) * a
    | _, _ => 0

lemma d1N2InvariantJacobianMinorR_det (a b c d : ℝ) :
    (d1N2InvariantJacobianMinorR a b c d).det =
      (-8 : ℝ) * a * (a * c - b * d) := by
  simp [d1N2InvariantJacobianMinorR, Matrix.det_fin_three]
  ring

lemma d1N2InvariantJacobianMinorR_det_ne_zero_of
    {a b c d : ℝ}
    (ha : a ≠ 0)
    (hminor : a * c - b * d ≠ 0) :
    (d1N2InvariantJacobianMinorR a b c d).det ≠ 0 := by
  rw [d1N2InvariantJacobianMinorR_det]
  exact mul_ne_zero (mul_ne_zero (by norm_num : (-8 : ℝ) ≠ 0) ha) hminor

lemma d1N2InvariantJacobianMinorR_atProbe :
    d1N2InvariantJacobianMinorR 1 0 1 2 =
      d1N2InvariantJacobianMinorAtProbe := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num
    [d1N2InvariantJacobianMinorR, d1N2InvariantJacobianMinorAtProbe]

lemma d1N2InvariantJacobianMinorAtProbe_det :
    (d1N2InvariantJacobianMinorAtProbe.det : ℝ) = (-8 : ℝ) := by
  calc
    (d1N2InvariantJacobianMinorAtProbe.det : ℝ)
        = (d1N2InvariantJacobianMinorR 1 0 1 2).det := by
            rw [d1N2InvariantJacobianMinorR_atProbe]
    _ = (-8 : ℝ) * (1 : ℝ) * ((1 : ℝ) * 1 - 0 * 2) := by
          simpa using d1N2InvariantJacobianMinorR_det 1 0 1 2
    _ = (-8 : ℝ) := by ring

lemma d1N2InvariantJacobianMinorAtProbe_det_ne_zero :
    (d1N2InvariantJacobianMinorAtProbe.det : ℝ) ≠ 0 := by
  norm_num [d1N2InvariantJacobianMinorAtProbe_det]

lemma d1N2InvariantJacobianMinorAtProbe_linearIndependent_rows :
    LinearIndependent ℝ d1N2InvariantJacobianMinorAtProbe := by
  exact Matrix.linearIndependent_rows_of_det_ne_zero
    (A := d1N2InvariantJacobianMinorAtProbe)
    d1N2InvariantJacobianMinorAtProbe_det_ne_zero

/-- Symbolic complex Jacobian minor (rows `(Q₀,Q₁,S)`, columns `(a,c,d)`) for
the chart `(a,b,c,d) ↦ (Q₀,Q₁,P,S)`. -/
def d1N2InvariantJacobianMinorC (a b c d : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => (-2 : ℂ) * a
    | 1, 1 => (-2 : ℂ) * c
    | 1, 2 => (2 : ℂ) * d
    | 2, 0 => (-2 : ℂ) * d
    | 2, 1 => (2 : ℂ) * b
    | 2, 2 => (-2 : ℂ) * a
    | _, _ => 0

lemma d1N2InvariantJacobianMinorC_det (a b c d : ℂ) :
    (d1N2InvariantJacobianMinorC a b c d).det =
      (-8 : ℂ) * a * (a * c - b * d) := by
  simp [d1N2InvariantJacobianMinorC, Matrix.det_fin_three]
  ring

lemma d1N2InvariantJacobianMinorC_ofReal (a b c d : ℝ) :
    d1N2InvariantJacobianMinorC (a : ℂ) b c d =
      fun i j => ((d1N2InvariantJacobianMinorR a b c d i j : ℝ) : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d1N2InvariantJacobianMinorC, d1N2InvariantJacobianMinorR]

lemma d1N2InvariantJacobianMinorC_det_ofReal (a b c d : ℝ) :
    (d1N2InvariantJacobianMinorC (a : ℂ) b c d).det =
      ((d1N2InvariantJacobianMinorR a b c d).det : ℂ) := by
  rw [d1N2InvariantJacobianMinorC_det, d1N2InvariantJacobianMinorR_det]
  norm_num

lemma d1N2InvariantJacobianMinorC_det_ne_zero_of
    {a b c d : ℂ}
    (ha : a ≠ 0)
    (hminor : a * c - b * d ≠ 0) :
    (d1N2InvariantJacobianMinorC a b c d).det ≠ 0 := by
  rw [d1N2InvariantJacobianMinorC_det]
  exact mul_ne_zero (mul_ne_zero (by norm_num : (-8 : ℂ) ≠ 0) ha) hminor

/-- Complex version of the explicit invariant-route Jacobian minor at the probe
point, with the same numeric entries as the real matrix. -/
def d1N2InvariantJacobianMinorAtProbeC : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => (-2 : ℂ)
    | 1, 1 => (-2 : ℂ)
    | 1, 2 => (4 : ℂ)
    | 2, 0 => (-4 : ℂ)
    | 2, 2 => (-2 : ℂ)
    | _, _ => 0

lemma d1N2InvariantJacobianMinorC_atProbe :
    d1N2InvariantJacobianMinorC (1 : ℂ) 0 1 2 =
      d1N2InvariantJacobianMinorAtProbeC := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num
    [d1N2InvariantJacobianMinorC, d1N2InvariantJacobianMinorAtProbeC]

lemma d1N2InvariantJacobianMinorAtProbeC_det :
    (d1N2InvariantJacobianMinorAtProbeC.det : ℂ) = (-8 : ℂ) := by
  calc
    (d1N2InvariantJacobianMinorAtProbeC.det : ℂ)
        = (d1N2InvariantJacobianMinorC (1 : ℂ) 0 1 2).det := by
            rw [d1N2InvariantJacobianMinorC_atProbe]
    _ = (-8 : ℂ) * (1 : ℂ) * ((1 : ℂ) * 1 - 0 * 2) := by
          simpa using d1N2InvariantJacobianMinorC_det (1 : ℂ) 0 1 2
    _ = (-8 : ℂ) := by ring

lemma d1N2InvariantJacobianMinorAtProbeC_det_ne_zero :
    (d1N2InvariantJacobianMinorAtProbeC.det : ℂ) ≠ 0 := by
  norm_num [d1N2InvariantJacobianMinorAtProbeC_det]

lemma d1N2InvariantJacobianMinorAtProbeC_linearIndependent_rows :
    LinearIndependent ℂ d1N2InvariantJacobianMinorAtProbeC := by
  exact Matrix.linearIndependent_rows_of_det_ne_zero
    (A := d1N2InvariantJacobianMinorAtProbeC)
    d1N2InvariantJacobianMinorAtProbeC_det_ne_zero

/-- `d=1,n=2` local commutativity in invariant form:
if `Q₀ + Q₁ - 2P > 0` on a real configuration, then swapping the two points
does not change the boundary value. -/
theorem d1_n2_local_comm_of_invariant_ineq
    (F : D1N2Config → ℂ)
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (x : Fin 2 → Fin (1 + 1) → ℝ)
    (hsp : d1Q0R x + d1Q1R x - 2 * d1P01R x > 0) :
    F (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ)) =
      F (fun k μ => (x k μ : ℂ)) := by
  have hsp' : ∑ μ, minkowskiSignature 1 μ * (x 1 μ - x 0 μ) ^ 2 > 0 := by
    simpa [d1_adj_spacelike_expr_eq_q0q1p] using hsp
  exact hF_local (0 : Fin 2) (by decide) x hsp'

/-- Local commutativity for explicit real coordinates, expressed through the
chart-level spacelike inequality. -/
theorem d1_n2_local_comm_realConfig_of_spacelike
    (F : D1N2Config → ℂ)
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (a b c d : ℝ)
    (hsp : (b - d) ^ 2 - (a - c) ^ 2 > 0) :
    F (fun k μ => (d1N2RealConfig a b c d (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ)) =
      F (fun k μ => (d1N2RealConfig a b c d k μ : ℂ)) := by
  have hinv :
      d1Q0R (d1N2RealConfig a b c d) + d1Q1R (d1N2RealConfig a b c d) -
        2 * d1P01R (d1N2RealConfig a b c d) > 0 := by
    simpa [d1_adj_spacelike_expr_realConfig] using hsp
  exact d1_n2_local_comm_of_invariant_ineq F hF_local (d1N2RealConfig a b c d) hinv

/-- The signed invariant quadruple lies on the quadric:
`S^2 = 4 (P^2 - Q0*Q1)`. -/
lemma d1_invariant_quadric_relation (z : D1N2Config) :
    (d1S01 z) ^ 2 = 4 * ((d1P01 z) ^ 2 - d1Q0 z * d1Q1 z) := by
  have hS : d1S01 z = d1R01 z - d1T01 z := d1S01_eq_R01_sub_T01 z
  have hP : (2 : ℂ) * d1P01 z = -(d1R01 z + d1T01 z) := d1_two_mul_P01_eq_neg_R01_add_T01 z
  have hRT : d1R01 z * d1T01 z = d1Q0 z * d1Q1 z := d1_R01_mul_T01_eq_Q0_mul_Q1 z
  have hPneg : (-2 : ℂ) * d1P01 z = d1R01 z + d1T01 z := by
    calc
      (-2 : ℂ) * d1P01 z = -((2 : ℂ) * d1P01 z) := by ring
      _ = -(-(d1R01 z + d1T01 z)) := by rw [hP]
      _ = d1R01 z + d1T01 z := by ring
  have hP2 : (4 : ℂ) * (d1P01 z) ^ 2 = (d1R01 z + d1T01 z) ^ 2 := by
    calc
      (4 : ℂ) * (d1P01 z) ^ 2 = ((-2 : ℂ) * d1P01 z) ^ 2 := by ring
      _ = (d1R01 z + d1T01 z) ^ 2 := by
            exact congrArg (fun t : ℂ => t ^ 2) hPneg
  calc
    (d1S01 z) ^ 2 = (d1R01 z - d1T01 z) ^ 2 := by rw [hS]
    _ = (d1R01 z + d1T01 z) ^ 2 - 4 * (d1R01 z * d1T01 z) := by ring
    _ = (4 : ℂ) * (d1P01 z) ^ 2 - 4 * (d1Q0 z * d1Q1 z) := by
          rw [← hP2, hRT]
    _ = 4 * ((d1P01 z) ^ 2 - d1Q0 z * d1Q1 z) := by ring

/-- Invariant-route model for `d=1,n=2`:
on `FT`, `F` factors through `(Q₀,Q₁,P,S)` via a swap-compatible kernel. -/
def d1N2InvariantModel (F : D1N2Config → ℂ) : Prop :=
  ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ,
    (∀ z, z ∈ ForwardTube 1 2 → F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) ∧
    (∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z))

/-- Core reduction for the Lorentz-invariant `d=1,n=2` route:
if `F` has a swap-compatible `(Q₀,Q₁,P,S)` model on `FT`, then the adjacent-swap
forward equality follows for every witness `Γ`. -/
theorem d1_n2_forward_swap_eq_of_invariantModel
    (F : D1N2Config → ℂ)
    (hmodel : d1N2InvariantModel F)
    (w : D1N2Config) (hw : w ∈ ForwardTube 1 2)
    (Γ : ComplexLorentzGroup 1)
    (hΓswap : complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w := by
  rcases hmodel with ⟨f, hf_onFT, hf_swap_forwardizable⟩
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  have hL : F (complexLorentzAction Γ (permAct (d := 1) τ w)) =
      f (d1Q0 (complexLorentzAction Γ (permAct (d := 1) τ w)))
        (d1Q1 (complexLorentzAction Γ (permAct (d := 1) τ w)))
        (d1P01 (complexLorentzAction Γ (permAct (d := 1) τ w)))
        (d1S01 (complexLorentzAction Γ (permAct (d := 1) τ w))) := by
    apply hf_onFT
    simpa [τ] using hΓswap
  have hR : F w = f (d1Q0 w) (d1Q1 w) (d1P01 w) (d1S01 w) := hf_onFT w hw
  calc
    F (complexLorentzAction Γ (permAct (d := 1) τ w))
        = f (d1Q0 (complexLorentzAction Γ (permAct (d := 1) τ w)))
            (d1Q1 (complexLorentzAction Γ (permAct (d := 1) τ w)))
            (d1P01 (complexLorentzAction Γ (permAct (d := 1) τ w)))
            (d1S01 (complexLorentzAction Γ (permAct (d := 1) τ w))) := hL
    _ = f (d1Q0 (permAct (d := 1) τ w))
          (d1Q1 (permAct (d := 1) τ w))
          (d1P01 (permAct (d := 1) τ w))
          (d1S01 (permAct (d := 1) τ w)) := by
            simp [d1Q0_lorentzAction, d1Q1_lorentzAction,
              d1P01_lorentzAction, d1S01_lorentzAction]
    _ = f (d1Q1 w) (d1Q0 w) (d1P01 w) (-d1S01 w) := by
          simpa [τ] using congrArg
            (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) (d1InvariantQuad_swap01 w)
    _ = f (d1Q0 w) (d1Q1 w) (d1P01 w) (d1S01 w) := by
          simpa using (hf_swap_forwardizable w hw Γ hΓswap).symm
    _ = F w := hR.symm

/-- Companion reduction for the `d=1,n=2` invariant route:
if forward-level adjacent-swap equality is available for `F`, then any kernel
`f` representing `F` on `FT` satisfies the swap rule on forwardizable points. -/
theorem d1_n2_invariantKernelSwapRule_of_forwardSwapEq
    (F : D1N2Config → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  intro z hz Γ hΓswap
  let y : D1N2Config :=
    complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
  have hyFT : y ∈ ForwardTube 1 2 := hΓswap
  have hFswap : F y = F z := by
    simpa [y] using hforward z hz Γ hΓswap
  have hleft : f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) = F z := by
    simpa using (hf_onFT z hz).symm
  have hquadY :
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
    dsimp [y]
    calc
      d1InvariantQuad (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z))
          = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
              simp [d1InvariantQuad_lorentzAction]
      _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
  have hright : f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) = F y := by
    calc
      f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z)
          = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := by
              simpa [d1InvariantQuad] using congrArg
                (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadY.symm
      _ = F y := by simpa using (hf_onFT y hyFT).symm
  calc
    f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) = F z := hleft
    _ = F y := hFswap.symm
    _ = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := hright.symm

/-- For fixed `hf_onFT`, the forward-swap equality and kernel swap rule are
equivalent (`d=1,n=2`). -/
theorem d1_n2_forwardSwapEq_iff_invariantKernelSwapRule
    (F : D1N2Config → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) :
    (∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) ↔
    (∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z)) := by
  constructor
  · intro hforward
    exact d1_n2_invariantKernelSwapRule_of_forwardSwapEq F f hf_onFT hforward
  · intro hkernel z hz Γ hΓswap
    let y : D1N2Config :=
      complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
    have hleft : F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
      hf_onFT z hz
    have hquadY :
        d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
      dsimp [y]
      calc
        d1InvariantQuad (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z))
            = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
                simp [d1InvariantQuad_lorentzAction]
        _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
    have hright : F y = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
      calc
        F y = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hf_onFT y hΓswap
        _ = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
              simpa [d1InvariantQuad] using congrArg
                (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadY
    have hker : f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
        f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
      hkernel z hz Γ hΓswap
    calc
      F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z))
          = F y := by rfl
      _ = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := hright
      _ = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hker.symm
      _ = F z := hleft.symm

/-- Same conclusion in the `fun k => w (swap k)` presentation used in the main
permutation-flow theorem statements. -/
theorem d1_n2_forward_swap_eq_of_invariantModel_fun
    (F : D1N2Config → ℂ)
    (hmodel : d1N2InvariantModel F)
    (w : D1N2Config) (hw : w ∈ ForwardTube 1 2)
    (Γ : ComplexLorentzGroup 1)
    (hΓswap : complexLorentzAction Γ
      (fun k => w ((Equiv.swap (0 : Fin 2) 1) k)) ∈ ForwardTube 1 2) :
    F (complexLorentzAction Γ (fun k => w ((Equiv.swap (0 : Fin 2) 1) k))) = F w := by
  simpa [permAct] using
    d1_n2_forward_swap_eq_of_invariantModel F hmodel w hw Γ
      (by simpa [permAct] using hΓswap)

/-- If `Γ·(swap·w)` lies in `FT`, then the swapped-sign invariant quadruple of
`w` is realized by an `FT` point (namely `Γ·(swap·w)`). -/
lemma exists_forward_with_swappedInvariantQuad_of_forwardizedSwap
    (w : D1N2Config)
    (Γ : ComplexLorentzGroup 1)
    (hΓswap : complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    ∃ y : D1N2Config, y ∈ ForwardTube 1 2 ∧
      d1InvariantQuad y = (d1Q1 w, d1Q0 w, d1P01 w, -d1S01 w) := by
  let y : D1N2Config :=
    complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)
  refine ⟨y, hΓswap, ?_⟩
  calc
    d1InvariantQuad y
        = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) := by
            simp [y, d1InvariantQuad_lorentzAction]
    _ = (d1Q1 w, d1Q0 w, d1P01 w, -d1S01 w) := d1InvariantQuad_swap01 w

/-- Global `extendF` swap-equality on `ET ∩ swap(ET)` for `d=1,n=2`,
derived from the invariant model. -/
theorem d1_n2_extendF_swap_eq_on_adjSwapExtendedOverlap_of_invariantModel
    (F : D1N2Config → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : D1N2Config), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hmodel : d1N2InvariantModel F)
    (y : D1N2Config)
    (hyD : y ∈ adjSwapExtendedOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)) :
    extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) y) = extendF F y := by
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  have hyET : y ∈ ExtendedTube 1 2 := hyD.1
  have hτyET : permAct (d := 1) τ y ∈ ExtendedTube 1 2 := by
    simpa [τ] using hyD.2
  rcases Set.mem_iUnion.mp hyET with ⟨Λ1, w1, hw1FT, hy_repr⟩
  rcases Set.mem_iUnion.mp hτyET with ⟨Λ2, w2, hw2FT, hτy_repr⟩
  let Γ : ComplexLorentzGroup 1 := Λ2⁻¹ * Λ1
  have hcomm1 :
      complexLorentzAction Λ1 (permAct (d := 1) τ w1) =
        permAct (d := 1) τ (complexLorentzAction Λ1 w1) :=
    lorentz_perm_commute Λ1 w1 τ
  have hΓswap_eq_w2 :
      complexLorentzAction Γ (permAct (d := 1) τ w1) = w2 := by
    calc
      complexLorentzAction Γ (permAct (d := 1) τ w1)
          = complexLorentzAction Λ2⁻¹
              (complexLorentzAction Λ1 (permAct (d := 1) τ w1)) := by
              simp [Γ, complexLorentzAction_mul]
      _ = complexLorentzAction Λ2⁻¹
            (permAct (d := 1) τ (complexLorentzAction Λ1 w1)) := by
              rw [hcomm1]
      _ = complexLorentzAction Λ2⁻¹ (permAct (d := 1) τ y) := by
            rw [hy_repr]
      _ = complexLorentzAction Λ2⁻¹ (complexLorentzAction Λ2 w2) := by
            rw [hτy_repr]
      _ = w2 := by
            simp [complexLorentzAction_inv]
  have hΓswapFT : complexLorentzAction Γ (permAct (d := 1) τ w1) ∈ ForwardTube 1 2 := by
    simpa [hΓswap_eq_w2] using hw2FT
  have hFw2_eq_Fw1 : F w2 = F w1 := by
    have hcore :=
      d1_n2_forward_swap_eq_of_invariantModel F hmodel w1 hw1FT Γ hΓswapFT
    simpa [τ, hΓswap_eq_w2] using hcore
  have hExt_y : extendF F y = F w1 := by
    have hET_w1 : w1 ∈ ExtendedTube 1 2 := forwardTube_subset_extendedTube hw1FT
    calc
      extendF F y = extendF F (complexLorentzAction Λ1 w1) := by
        rw [hy_repr]
      _ = extendF F w1 :=
          extendF_complex_lorentz_invariant (d := 1) 2 F hF_holo hF_lorentz Λ1 w1 hET_w1
      _ = F w1 := extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz w1 hw1FT
  have hExt_τy : extendF F (permAct (d := 1) τ y) = F w2 := by
    have hET_w2 : w2 ∈ ExtendedTube 1 2 := forwardTube_subset_extendedTube hw2FT
    calc
      extendF F (permAct (d := 1) τ y)
          = extendF F (complexLorentzAction Λ2 w2) := by
              rw [hτy_repr]
      _ = extendF F w2 :=
          extendF_complex_lorentz_invariant (d := 1) 2 F hF_holo hF_lorentz Λ2 w2 hET_w2
      _ = F w2 := extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz w2 hw2FT
  calc
    extendF F (permAct (d := 1) τ y) = F w2 := hExt_τy
    _ = F w1 := hFw2_eq_Fw1
    _ = extendF F y := hExt_y.symm

end BHW
