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

lemma forwardTube_d0_step_pos {m : ℕ}
    {z : Fin (m + 1) → Fin (0 + 1) → ℂ}
    (hz : z ∈ ForwardTube 0 (m + 1)) (i : Fin m) :
    0 < (z i.succ 0 - z i.castSucc 0).im := by
  have hk := hz i.succ
  simpa [ForwardTube, InOpenForwardCone] using hk.1

lemma strictMono_imTime_d0 {m : ℕ}
    {z : Fin (m + 1) → Fin (0 + 1) → ℂ}
    (hz : z ∈ ForwardTube 0 (m + 1)) :
    StrictMono (fun k : Fin (m + 1) => (z k 0).im) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hstep : 0 < (z i.succ 0 - z i.castSucc 0).im :=
    forwardTube_d0_step_pos hz i
  have him : (z i.succ 0).im - (z i.castSucc 0).im > 0 := by
    simpa [Complex.sub_im] using hstep
  linarith

lemma strictMono_perm_of_strictMono_comp {m : ℕ}
    {z : Fin (m + 1) → Fin (0 + 1) → ℂ}
    (hy : StrictMono (fun k : Fin (m + 1) => (z k 0).im))
    (σ : Equiv.Perm (Fin (m + 1)))
    (hyσ : StrictMono (fun k : Fin (m + 1) => (z (σ k) 0).im)) :
    StrictMono σ := by
  intro a b hab
  have hlt : (z (σ a) 0).im < (z (σ b) 0).im := hyσ hab
  by_contra hnot
  have hle : σ b ≤ σ a := le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt' | heq
  · exact (lt_asymm hlt (hy hlt')).elim
  · exact (lt_irrefl _) (heq ▸ hlt)

lemma perm_eq_one_of_forwardTube_and_perm_forwardTube_d0 {m : ℕ}
    (σ : Equiv.Perm (Fin (m + 1)))
    {z : Fin (m + 1) → Fin (0 + 1) → ℂ}
    (hz : z ∈ ForwardTube 0 (m + 1))
    (hσz : (fun k => z (σ k)) ∈ ForwardTube 0 (m + 1)) :
    σ = 1 := by
  have hy : StrictMono (fun k : Fin (m + 1) => (z k 0).im) :=
    strictMono_imTime_d0 hz
  have hyσ : StrictMono (fun k : Fin (m + 1) => (z (σ k) 0).im) :=
    strictMono_imTime_d0 hσz
  exact strictMono_perm_eq_one σ (strictMono_perm_of_strictMono_comp hy σ hyσ)

lemma coreExtendedTube_d0_eq_forwardTube (n : ℕ) :
    BHWCore.ExtendedTube 0 n = ForwardTube 0 n := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨Λ, w, hw, hzw⟩
    have hΛ : (Λ : ComplexLorentzGroup 0) = 1 := complexLorentzGroup_d0_eq_one Λ
    subst hΛ
    have hw' : w ∈ ForwardTube 0 n := by
      simpa [ForwardTube, BHWCore.ForwardTube] using hw
    have hz_eq : z = w := by
      simp [hzw, BHWCore.complexLorentzAction_one]
    exact hz_eq ▸ hw'
  · intro hz
    exact BHWCore.forwardTube_subset_extendedTube hz

lemma coreExtendedTube_perm_overlap_d0_forces_perm_one {m : ℕ}
    (σ : Equiv.Perm (Fin (m + 1)))
    {z : Fin (m + 1) → Fin (0 + 1) → ℂ}
    (hz : z ∈ BHWCore.ExtendedTube 0 (m + 1))
    (hσz : (fun k => z (σ k)) ∈ BHWCore.ExtendedTube 0 (m + 1)) :
    σ = 1 := by
  have hzFT : z ∈ ForwardTube 0 (m + 1) := by
    simpa [coreExtendedTube_d0_eq_forwardTube] using hz
  have hσzFT : (fun k => z (σ k)) ∈ ForwardTube 0 (m + 1) := by
    simpa [coreExtendedTube_d0_eq_forwardTube] using hσz
  exact perm_eq_one_of_forwardTube_and_perm_forwardTube_d0 σ hzFT hσzFT

lemma coreExtendedTube_perm_overlap_d0_forces_perm_one_general (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (0 + 1) → ℂ}
    (hz : z ∈ BHWCore.ExtendedTube 0 n)
    (hσz : (fun k => z (σ k)) ∈ BHWCore.ExtendedTube 0 n) :
    σ = 1 := by
  cases n with
  | zero =>
      exact Subsingleton.elim σ 1
  | succ m =>
      exact coreExtendedTube_perm_overlap_d0_forces_perm_one (m := m) σ hz hσz

end BHW
