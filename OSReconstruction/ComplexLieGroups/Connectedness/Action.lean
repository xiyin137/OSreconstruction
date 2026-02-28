import OSReconstruction.ComplexLieGroups.Complexification

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The action of a complex Lorentz transformation on ℂ^{n×(d+1)}. -/
def complexLorentzAction {d n : ℕ}
    (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => ∑ ν, Λ.val μ ν * z k ν

/-- The complex Lorentz action is compatible with group multiplication. -/
theorem complexLorentzAction_mul {d n : ℕ} (Λ₁ Λ₂ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (Λ₁ * Λ₂) z =
    complexLorentzAction Λ₁ (complexLorentzAction Λ₂ z) := by
  ext k μ
  simp only [complexLorentzAction, ComplexLorentzGroup.mul_val, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext ν
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

/-- The identity acts trivially. -/
theorem complexLorentzAction_one {d n : ℕ} (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (1 : ComplexLorentzGroup d) z = z := by
  ext k μ
  simp only [complexLorentzAction,
    show (1 : ComplexLorentzGroup d).val = (1 : Matrix _ _ ℂ) from rfl,
    Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The inverse acts by the inverse matrix. -/
theorem complexLorentzAction_inv {d n : ℕ} (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ⁻¹ (complexLorentzAction Λ z) = z := by
  rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]

instance instMulActionComplexLorentzCfg {d n : ℕ} :
    MulAction (ComplexLorentzGroup d) (Fin n → Fin (d + 1) → ℂ) where
  smul := complexLorentzAction
  one_smul z := by simpa using complexLorentzAction_one z
  mul_smul g h z := by simpa using (complexLorentzAction_mul g h z)

instance instContinuousSMulComplexLorentzCfg {d n : ℕ} :
    ContinuousSMul (ComplexLorentzGroup d) (Fin n → Fin (d + 1) → ℂ) where
  continuous_smul := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    change Continuous (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
      ∑ ν, p.1.val μ ν * p.2 k ν)
    apply continuous_finset_sum
    intro ν _
    apply Continuous.mul
    · have hval : Continuous
          (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) => p.1.val) :=
        ComplexLorentzGroup.continuous_val.comp continuous_fst
      have hrow : Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M μ) :=
        continuous_apply μ
      have hentry : Continuous (fun r : Fin (d + 1) → ℂ => r ν) :=
        continuous_apply ν
      exact hentry.comp (hrow.comp hval)
    · exact (continuous_apply ν).comp ((continuous_apply k).comp continuous_snd)

end BHW
