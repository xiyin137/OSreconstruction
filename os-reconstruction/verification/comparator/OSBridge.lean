import WightmanBridge
import OSReconstruction.Specification

namespace OSReconstructionAudit
noncomputable section

/-- The independent zero-diagonal type has exactly the production carrier,
linear operations and subspace topology. -/
theorem zeroTest_eq (d n : ℕ) : ZeroTest d n = ZeroDiagonalSchwartz d n := rfl

theorem zeroTest_ofClassical_eq {d n : ℕ} (f : Test d n) :
    ZeroTest.ofClassical f = ZeroDiagonalSchwartz.ofClassical f := rfl

theorem osTensorRelation_iff {d n m : ℕ} [NeZero d]
    (f : Test d n) (g : Test d m) (h : Test d (n + m)) :
    osTensorRelation f g h ↔ h = SchwartzNPoint.osConjTensorProduct f g := by
  constructor
  · intro hh
    ext x
    exact hh x
  · intro hh
    subst h
    intro x
    rfl

/-- Transfer every OS axiom while preserving the Schwinger family by rfl. -/
def OS.toProduction {d : ℕ} [NeZero d] (A : OS d) : OsterwalderSchraderAxioms d where
  S := A.S
  E0_tempered := A.E0_tempered
  E0_linear := A.E0_linear
  E0_reality := A.E0_reality
  E1_translation_invariant := A.E1_translation_invariant
  E1_rotation_invariant := A.E1_rotation_invariant
  E2_reflection_positive := by
    intro F hF
    exact A.E2_reflection_positive (Borchers.ofProduction F) hF
      (fun n m => SchwartzNPoint.osConjTensorProduct (F.funcs n) (F.funcs m)) (by intro n m x; rfl)
  E3_symmetric := A.E3_symmetric
  E4_cluster := A.E4_cluster

/-- Reflection positivity is unchanged: every witness is extensionally the
production reflected tensor, and conversely that tensor is a witness. -/
def OS.ofProduction {d : ℕ} [NeZero d] (A : OsterwalderSchraderAxioms d) : OS d where
  S := A.S
  E0_tempered := A.E0_tempered
  E0_linear := A.E0_linear
  E0_reality := A.E0_reality
  E1_translation_invariant := A.E1_translation_invariant
  E1_rotation_invariant := A.E1_rotation_invariant
  E2_reflection_positive := by
    intro F hF H hH
    have hH' : H = fun n m => SchwartzNPoint.osConjTensorProduct (F.funcs n) (F.funcs m) := by
      funext n m
      exact (osTensorRelation_iff _ _ _).mp (hH n m)
    subst H
    exact A.E2_reflection_positive (Borchers.toProduction F) hF
  E3_symmetric := A.E3_symmetric
  E4_cluster := A.E4_cluster

@[simp] theorem OS.toProduction_S {d : ℕ} [NeZero d] (A : OS d) :
    A.toProduction.S = A.S := rfl
@[simp] theorem OS.ofProduction_S {d : ℕ} [NeZero d] (A : OsterwalderSchraderAxioms d) :
    (OS.ofProduction A).S = A.S := rfl

@[simp] theorem OS.ofProduction_toProduction {d : ℕ} [NeZero d] (A : OS d) :
    OS.ofProduction A.toProduction = A := by cases A; rfl
@[simp] theorem OS.toProduction_ofProduction {d : ℕ} [NeZero d]
    (A : OsterwalderSchraderAxioms d) : (OS.ofProduction A).toProduction = A := by
  cases A; rfl

def arityLinearGrowth.toProduction {d : ℕ} [NeZero d] {A : OS d}
    (h : arityLinearGrowth A) : OSLinearGrowthCondition d A.toProduction where
  normalized_zero := h.normalized_zero
  sobolev_index := h.sobolev_index
  alpha := h.alpha
  beta := h.beta
  gamma := h.gamma
  alpha_pos := h.alpha_pos
  beta_pos := h.beta_pos
  growth_estimate := h.growth_estimate

def arityLinearGrowth.ofProduction {d : ℕ} [NeZero d]
    {A : OsterwalderSchraderAxioms d} (h : OSLinearGrowthCondition d A) :
    arityLinearGrowth (OS.ofProduction A) where
  normalized_zero := h.normalized_zero
  sobolev_index := h.sobolev_index
  alpha := h.alpha
  beta := h.beta
  gamma := h.gamma
  alpha_pos := h.alpha_pos
  beta_pos := h.beta_pos
  growth_estimate := h.growth_estimate

def originalGrowth.toProduction {d : ℕ} [NeZero d] {A : OS d}
    (h : originalGrowth A) : OSReconstruction.OSIIOriginalLinearGrowthCondition d A.toProduction where
  normalized_zero := h.normalized_zero
  sobolev_index := h.sobolev_index
  sobolev_index_pos := h.sobolev_index_pos
  alpha := h.alpha
  gamma := h.gamma
  alpha_pos := h.alpha_pos
  growth_estimate := h.growth_estimate

def originalGrowth.ofProduction {d : ℕ} [NeZero d]
    {A : OsterwalderSchraderAxioms d}
    (h : OSReconstruction.OSIIOriginalLinearGrowthCondition d A) :
    originalGrowth (OS.ofProduction A) where
  normalized_zero := h.normalized_zero
  sobolev_index := h.sobolev_index
  sobolev_index_pos := h.sobolev_index_pos
  alpha := h.alpha
  gamma := h.gamma
  alpha_pos := h.alpha_pos
  growth_estimate := h.growth_estimate

theorem wickPair_iff {d : ℕ} [NeZero d] (S : SchwingerFamily d) (W : Family d) :
    wickPair S W ↔ IsWickRotationPair S W := Iff.rfl

theorem outputGrowth_iff (d : ℕ) (W : Family d) :
    outputGrowth d W ↔ OSReconstruction.OSIIWightmanGrowthCondition d W := Iff.rfl

theorem originalSeminorm_eq (d n r : ℕ) (f : Test d n) :
    originalSeminorm d n r f = OSReconstruction.osiiOriginalNPointSeminorm d n r f := rfl

end
end OSReconstructionAudit
