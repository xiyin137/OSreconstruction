/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.ComplexLieGroups.Connectedness.Action
import OSReconstruction.ComplexLieGroups.DifferenceCoordinates

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

lemma complexLorentzGroup_d0_eq_one (Λ : ComplexLorentzGroup 0) :
    Λ = 1 := by
  apply ComplexLorentzGroup.ext
  ext i j
  fin_cases i
  fin_cases j
  have hdet : Λ.val.det = (1 : ℂ) := Λ.proper
  simpa using hdet

lemma complexLorentzGroup_d0_subsingleton :
    Subsingleton (ComplexLorentzGroup 0) := by
  refine ⟨?_⟩
  intro a b
  calc
    a = 1 := complexLorentzGroup_d0_eq_one a
    _ = b := (complexLorentzGroup_d0_eq_one b).symm

lemma strictMono_perm_eq_one {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (hσ : StrictMono σ) :
    σ = 1 := by
  let e : Fin n ≃o Fin n := hσ.orderIsoOfSurjective σ σ.surjective
  have he : e = OrderIso.refl (Fin n) := Subsingleton.elim _ _
  apply Equiv.ext
  intro i
  have hval : e i = i := by
    simp [he]
  simp [e] at hval
  exact hval

end BHW
