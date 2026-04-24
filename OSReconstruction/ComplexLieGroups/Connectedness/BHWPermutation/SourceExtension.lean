import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvarianceCore
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeGluing
import OSReconstruction.ComplexLieGroups.JostPoints

/-!
# Source BHW extension on the permuted extended tube

This file contains the theorem-2-facing, source-backed Hall-Wightman input in
local PET language.

The only analytic frontier here is
`hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`.  It is
intentionally pure SCV/BHW: it assumes holomorphicity on the forward tube,
restricted real Lorentz invariance, and permutation symmetry.  It does not
mention Wightman boundary distributions, locality, or
`IsLocallyCommutativeWeak`.

The theorem-2-facing extension theorem below proves the remaining PET algebra
from that source branch law.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

variable {d n : ℕ}

private theorem source_lorentz_perm_commute
    (Γ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ)
    (τ : Equiv.Perm (Fin n)) :
    complexLorentzAction Γ (fun k => w (τ k)) =
      fun k => (complexLorentzAction Γ w) (τ k) := by
  ext k μ
  simp only [complexLorentzAction]

private theorem source_complexLorentzAction_mem_extendedTube
    (n : ℕ)
    (Λ : ComplexLorentzGroup d)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n) :
    complexLorentzAction Λ z ∈ ExtendedTube d n := by
  rcases Set.mem_iUnion.mp hz with ⟨Γ, w, hw, rfl⟩
  exact Set.mem_iUnion.mpr ⟨Λ * Γ, w, hw, by rw [complexLorentzAction_mul]⟩

private theorem source_permutedExtendedTubeSector_complexLorentzAction_iff
    (Λ : ComplexLorentzGroup d)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ z ∈ permutedExtendedTubeSector d n π ↔
      z ∈ permutedExtendedTubeSector d n π := by
  constructor
  · intro h
    have h' : complexLorentzAction Λ⁻¹
        (fun k => (complexLorentzAction Λ z) (π k)) ∈ ExtendedTube d n :=
      source_complexLorentzAction_mem_extendedTube n Λ⁻¹ h
    have hrewrite :
        complexLorentzAction Λ⁻¹
            (fun k => (complexLorentzAction Λ z) (π k)) =
          fun k => z (π k) := by
      calc
        complexLorentzAction Λ⁻¹
            (fun k => (complexLorentzAction Λ z) (π k))
            = complexLorentzAction Λ⁻¹
                (complexLorentzAction Λ (fun k => z (π k))) := by
                simp [source_lorentz_perm_commute]
        _ = fun k => z (π k) := by
                rw [complexLorentzAction_inv]
    simpa [permutedExtendedTubeSector, hrewrite] using h'
  · intro h
    have h' : complexLorentzAction Λ (fun k => z (π k)) ∈ ExtendedTube d n :=
      source_complexLorentzAction_mem_extendedTube n Λ h
    have hrewrite :
        (fun k => (complexLorentzAction Λ z) (π k)) =
          complexLorentzAction Λ (fun k => z (π k)) := by
      simp [source_lorentz_perm_commute]
    simpa [permutedExtendedTubeSector, hrewrite] using h'

/-- Each permuted `extendF` branch is holomorphic on its PET sector.  This is a
local analytic sub-obligation for the source theorem below; it uses only the
forward-tube BHW continuation theorem and derives complex-Lorentz overlap
invariance from restricted real Lorentz invariance. -/
theorem permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (π : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (fun z : Fin n → Fin (d + 1) → ℂ => extendF F (fun k => z (π k)))
      (permutedExtendedTubeSector d n π) := by
  intro z hz
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hz hΛz
  have hExt_at :
      DifferentiableAt ℂ (extendF F) (fun k => z (π k)) := by
    exact
      ((extendF_holomorphicOn n F hF_holo hF_cinv)
        (fun k => z (π k)) hz).differentiableAt
        (isOpen_extendedTube.mem_nhds hz)
  have hperm_diff :
      Differentiable ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π k)) :=
    differentiable_pi.mpr fun k => differentiable_apply (π k)
  have hbranch_at :
      DifferentiableAt ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => extendF F (fun k => w (π k))) z := by
    simpa [Function.comp_def] using hExt_at.comp z hperm_diff.differentiableAt
  exact hbranch_at.differentiableWithinAt

/-- Hall-Wightman source branch law on the permuted extended tube.

This is the single analytic frontier in this file.  It is the local PET form of
the Hall-Wightman/BHW statement that the symmetric permuted-tube datum gives
one holomorphic function on `S''_n`, whose restriction to each explicit sector
is the corresponding ordinary `extendF` branch. -/
theorem hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        F (fun k => z (σ k)) = F z) :
    ∃ Fpet : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fpet (PermutedExtendedTube d n) ∧
      ∀ (π : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        Fpet z = extendF F (fun k => z (π k)) := by
  sorry

/-- Source-backed BHW/Hall-Wightman continuation on the permuted extended tube.

This is the direct local form of the OS I Section 4.5 BHW step: a symmetric
holomorphic datum on the permuted forward-tube family extends single-valuedly
to the permuted extended tube.  The complex-Lorentz and permutation invariance
conclusions are outputs, not source hypotheses.

The remaining proof is not the elementary observation that the original `F` is
permutation-invariant.  On a PET sector overlap the two `extendF` values may be
represented by different complex-Lorentz preimages, and the intermediate
permuted representative need not lie in the base forward tube.  The missing
input is therefore the Hall-Wightman single-valued continuation for the whole
symmetric permuted-tube datum. -/
theorem permutedExtendedTube_extension_of_forwardTube_symmetry
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        F (fun k => z (σ k)) = F z) :
    ∃ Fpet : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fpet (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, Fpet z = F z) ∧
      (∀ (π : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        Fpet z = extendF F (fun k => z (π k))) ∧
      (∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        complexLorentzAction Λ z ∈ PermutedExtendedTube d n →
        Fpet (complexLorentzAction Λ z) = Fpet z) ∧
      (∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        (fun k => z (σ k)) ∈ PermutedExtendedTube d n →
        Fpet (fun k => z (σ k)) = Fpet z) := by
  obtain ⟨Fpet, hFpet_holo, hFpet_branch⟩ :=
    hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry
      (d := d) hd n F hF_holo hF_lorentz hF_perm
  refine ⟨Fpet, hFpet_holo, ?_, hFpet_branch, ?_, ?_⟩
  · intro z hz
    have hz_sector : z ∈ permutedExtendedTubeSector d n (1 : Equiv.Perm (Fin n)) := by
      simpa [permutedExtendedTubeSector] using forwardTube_subset_extendedTube hz
    calc
      Fpet z = extendF F (fun k => z ((1 : Equiv.Perm (Fin n)) k)) :=
        hFpet_branch 1 z hz_sector
      _ = extendF F z := by simp
      _ = F z := extendF_eq_on_forwardTube n F hF_holo hF_lorentz z hz
  · intro Λ z hzPET _hΛzPET
    let π : Equiv.Perm (Fin n) :=
      permutedExtendedTubeBranch (d := d) (n := n) z hzPET
    have hzπ : z ∈ permutedExtendedTubeSector d n π := by
      simpa [π, permutedExtendedTubeSector] using
        permutedExtendedTubeBranch_mem_extendedTube (d := d) (n := n) z hzPET
    have hΛzπ :
        complexLorentzAction Λ z ∈ permutedExtendedTubeSector d n π :=
      (source_permutedExtendedTubeSector_complexLorentzAction_iff
        (d := d) (n := n) Λ π z).2 hzπ
    have hcomm :
        (fun k => (complexLorentzAction Λ z) (π k)) =
          complexLorentzAction Λ (fun k => z (π k)) := by
      simpa using
        (source_lorentz_perm_commute (d := d) (n := n) Λ z π).symm
    calc
      Fpet (complexLorentzAction Λ z) =
          extendF F (fun k => (complexLorentzAction Λ z) (π k)) :=
        hFpet_branch π (complexLorentzAction Λ z) hΛzπ
      _ = extendF F (complexLorentzAction Λ (fun k => z (π k))) := by
        rw [hcomm]
      _ = extendF F (fun k => z (π k)) :=
        extendF_complex_lorentz_invariant n F hF_holo hF_lorentz Λ
          (fun k => z (π k)) hzπ
      _ = Fpet z := (hFpet_branch π z hzπ).symm
  · intro σ z _hzPET hσzPET
    let y : Fin n → Fin (d + 1) → ℂ := fun k => z (σ k)
    let π : Equiv.Perm (Fin n) :=
      permutedExtendedTubeBranch (d := d) (n := n) y hσzPET
    have hyπ : y ∈ permutedExtendedTubeSector d n π := by
      simpa [π, y, permutedExtendedTubeSector] using
        permutedExtendedTubeBranch_mem_extendedTube (d := d) (n := n) y hσzPET
    have hzσπ : z ∈ permutedExtendedTubeSector d n (σ * π) := by
      simpa [y, permutedExtendedTubeSector, Equiv.Perm.mul_apply] using hyπ
    calc
      Fpet (fun k => z (σ k)) = Fpet y := rfl
      _ = extendF F (fun k => y (π k)) :=
        hFpet_branch π y hyπ
      _ = extendF F (fun k => z ((σ * π) k)) := by
        simp [y, Equiv.Perm.mul_apply]
      _ = Fpet z := (hFpet_branch (σ * π) z hzσπ).symm

/-- Sector-branch single-valuedness on PET, derived from the source BHW
extension theorem above. -/
theorem permutedExtendedTube_singleValued_of_forwardTube_symmetry
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        F (fun k => z (σ k)) = F z) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ permutedExtendedTubeSector d n π →
      z ∈ permutedExtendedTubeSector d n ρ →
      extendF F (fun k => z (π k)) =
        extendF F (fun k => z (ρ k)) := by
  intro π ρ z hzπ hzρ
  obtain ⟨Fpet, _hFpet_holo, _hFpet_FT, hFpet_branch,
      _hFpet_lorentz, _hFpet_perm⟩ :=
    permutedExtendedTube_extension_of_forwardTube_symmetry
      (d := d) hd n F hF_holo hF_lorentz hF_perm
  exact (hFpet_branch π z hzπ).symm.trans (hFpet_branch ρ z hzρ)

end BHW
