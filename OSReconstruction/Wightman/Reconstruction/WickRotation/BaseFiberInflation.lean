import OSReconstruction.ComplexLieGroups.GeodesicConvexity
import OSReconstruction.ComplexLieGroups.BHWCore

noncomputable section

open Complex

namespace OSReconstruction

/-- Adding positive time to a forward-cone vector keeps it in `V⁺`. -/
theorem inOpenForwardCone_add_time {d : ℕ} (η : Fin (d + 1) → ℝ) (s : ℝ)
    (hη : BHW.InOpenForwardCone d η) (hs : 0 ≤ s) :
    BHW.InOpenForwardCone d (fun μ => η μ + if μ = 0 then s else 0) := by
  obtain ⟨hη₀, hηQ⟩ := hη
  refine ⟨?_, ?_⟩
  · simp
    linarith
  · rw [BHW.minkowski_sum_decomp] at hηQ ⊢
    simp only [Fin.succ_ne_zero, ite_false, add_zero, ite_true]
    have htime : (η 0 + s) ^ 2 ≥ (η 0) ^ 2 := by
      nlinarith
    linarith

/-- The forward-tube condition is preserved when adding a positive imaginary-time
broadcast to every point of the configuration. -/
theorem forwardTube_add_broadcast_iTime {d n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ) (s : ℝ)
    (hz : z ∈ BHWCore.ForwardTube d n) (hs : 0 ≤ s) :
    (fun k μ => z k μ + if μ = 0 then (s : ℂ) * I else 0) ∈
      BHWCore.ForwardTube d n := by
  intro k
  specialize hz k
  by_cases hk : k.val = 0
  · simp only [hk, dite_true] at hz ⊢
    convert inOpenForwardCone_add_time _ s hz hs using 1
    funext μ
    simp only [Complex.sub_im, Pi.zero_apply, sub_zero, Complex.add_im]
    congr 1
    split
    · simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    · simp
  · simp only [hk, dite_false] at hz ⊢
    convert hz using 1
    funext μ
    simp [Complex.sub_im, Complex.add_im]

/-- The Lorentz action on a broadcast-shifted configuration equals the action
on the original plus the broadcast of the Lorentz-rotated shift. -/
theorem complexLorentzAction_add_broadcast {d n : ℕ}
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (v : Fin (d + 1) → ℂ) :
    BHWCore.complexLorentzAction Λ (fun k μ => z k μ + v μ) =
      fun k μ => BHWCore.complexLorentzAction Λ z k μ +
        ∑ ν, Λ.val μ ν * v ν := by
  ext k μ
  simp [BHWCore.complexLorentzAction, Finset.sum_add_distrib, mul_add]

/-- The inflation direction is fixed by `Λ · Λ⁻¹`. -/
theorem lorentz_action_inflation_dir {d : ℕ}
    (Λ : ComplexLorentzGroup d) :
    (fun μ => ∑ ν, Λ.val μ ν *
      ((Λ⁻¹ : ComplexLorentzGroup d).val ν 0 * I)) =
    (fun μ : Fin (d + 1) => if μ = (0 : Fin (d + 1)) then I else 0) := by
  funext μ
  conv_lhs =>
    arg 2
    ext ν
    rw [show Λ.val μ ν * ((Λ⁻¹ : ComplexLorentzGroup d).val ν 0 * I) =
      (Λ.val μ ν * (Λ⁻¹ : ComplexLorentzGroup d).val ν 0) * I by ring]
  rw [← Finset.sum_mul]
  have hmul : (Λ * (Λ⁻¹ : ComplexLorentzGroup d)).val = (1 : ComplexLorentzGroup d).val := by
    congr 1
    exact mul_inv_cancel Λ
  have hentry : ∑ ν, Λ.val μ ν * (Λ⁻¹ : ComplexLorentzGroup d).val ν 0 =
      if μ = 0 then 1 else 0 := by
    have h := congr_fun (congr_fun hmul μ) 0
    simp only [ComplexLorentzGroup.mul_val, Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  rw [hentry]
  split <;> simp

end OSReconstruction
