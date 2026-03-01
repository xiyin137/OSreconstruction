import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d : ℕ}

private lemma permAct_mul_bridge (π τ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    permAct (d := d) (π * τ) z =
      permAct (d := d) τ (permAct (d := d) π z) := by
  ext k μ
  simp [permAct, Equiv.Perm.mul_apply]

/-- Anchor-set nonemptiness for a left-adjacent step can be reduced to a
triple ET-membership witness:
`∃ y, y ∈ ET ∧ τ·y ∈ ET ∧ σ·y ∈ ET` implies
`∃ z, z ∈ D_(τ*σ) ∧ τ·z ∈ ET`. -/
theorem leftAdj_anchor_nonempty_of_ET_triple
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (htriple :
      ({y : Fin n → Fin (d + 1) → ℂ |
          y ∈ ExtendedTube d n ∧
          permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n ∧
          permAct (d := d) σ y ∈ ExtendedTube d n
      }).Nonempty) :
    ({z : Fin n → Fin (d + 1) → ℂ |
        z ∈ ExtendedTube d n ∧
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) z ∈ ExtendedTube d n ∧
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n
    }).Nonempty := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases htriple with ⟨y, hyET, hτyET, hσyET⟩
  refine ⟨permAct (d := d) τ y, ?_⟩
  refine ⟨hτyET, ?_, ?_⟩
  · have hτσ :
      permAct (d := d) (τ * σ) (permAct (d := d) τ y) =
        permAct (d := d) σ (permAct (d := d) τ (permAct (d := d) τ y)) := by
      simpa using permAct_mul_bridge (d := d) τ σ (permAct (d := d) τ y)
    rw [hτσ]
    have hττ : permAct (d := d) τ (permAct (d := d) τ y) = y := by
      ext k μ
      simp [permAct, τ]
    simpa [hττ] using hσyET
  · have hττ : permAct (d := d) τ (permAct (d := d) τ y) = y := by
      ext k μ
      simp [permAct, τ]
    simpa [τ, hττ] using hyET

/-- Converse to `leftAdj_anchor_nonempty_of_ET_triple`:
left-step anchor nonemptiness implies a triple ET-membership witness. -/
theorem ET_triple_nonempty_of_leftAdj_anchor
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (hAnchor :
      ({z : Fin n → Fin (d + 1) → ℂ |
          z ∈ ExtendedTube d n ∧
          permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) z ∈ ExtendedTube d n ∧
          permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n
      }).Nonempty) :
    ({y : Fin n → Fin (d + 1) → ℂ |
        y ∈ ExtendedTube d n ∧
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n ∧
        permAct (d := d) σ y ∈ ExtendedTube d n
    }).Nonempty := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases hAnchor with ⟨z, hzET, hzτσET, hτzET⟩
  refine ⟨permAct (d := d) τ z, ?_⟩
  refine ⟨hτzET, ?_, ?_⟩
  · have hττ : permAct (d := d) τ (permAct (d := d) τ z) = z := by
      ext k μ
      simp [permAct, τ]
    simpa [τ, hττ] using hzET
  · have hτσ :
        permAct (d := d) (τ * σ) z =
          permAct (d := d) σ (permAct (d := d) τ z) := by
      simpa using permAct_mul_bridge (d := d) τ σ z
    simpa [hτσ] using hzτσET

/-- ET triple-witness nonemptiness is equivalent to a forward-triple witness:
`∃ y, y ∈ ET ∧ τ·y ∈ ET ∧ σ·y ∈ ET`
iff
`∃ w, w ∈ FT ∧ τ·w ∈ ET ∧ σ·w ∈ ET`.

This reformulation isolates the remaining geometric burden to an explicit
forward-tube witness search. -/
theorem ET_triple_nonempty_iff_forward_triple_nonempty
    (n : ℕ)
    (τ σ : Equiv.Perm (Fin n)) :
    ({y : Fin n → Fin (1 + 1) → ℂ |
        y ∈ ExtendedTube 1 n ∧
        permAct (d := 1) τ y ∈ ExtendedTube 1 n ∧
        permAct (d := 1) σ y ∈ ExtendedTube 1 n
    }).Nonempty ↔
    ({w : Fin n → Fin (1 + 1) → ℂ |
        w ∈ ForwardTube 1 n ∧
        permAct (d := 1) τ w ∈ ExtendedTube 1 n ∧
        permAct (d := 1) σ w ∈ ExtendedTube 1 n
    }).Nonempty := by
  constructor
  · rintro ⟨y, hyET, hτyET, hσyET⟩
    rcases Set.mem_iUnion.mp hyET with ⟨Λ, w, hwFT, hy_eq⟩
    have hτy_as_action :
        permAct (d := 1) τ y =
          complexLorentzAction Λ (permAct (d := 1) τ w) := by
      calc
        permAct (d := 1) τ y
            = permAct (d := 1) τ (complexLorentzAction Λ w) := by simp [hy_eq]
        _ = complexLorentzAction Λ (permAct (d := 1) τ w) := by
              exact (lorentz_perm_commute Λ w τ).symm
    have hσy_as_action :
        permAct (d := 1) σ y =
          complexLorentzAction Λ (permAct (d := 1) σ w) := by
      calc
        permAct (d := 1) σ y
            = permAct (d := 1) σ (complexLorentzAction Λ w) := by simp [hy_eq]
        _ = complexLorentzAction Λ (permAct (d := 1) σ w) := by
              exact (lorentz_perm_commute Λ w σ).symm
    have hτwET : permAct (d := 1) τ w ∈ ExtendedTube 1 n := by
      have hΛτwET : complexLorentzAction Λ (permAct (d := 1) τ w) ∈ ExtendedTube 1 n := by
        simpa [hτy_as_action] using hτyET
      have := complexLorentzAction_mem_extendedTube (d := 1) (n := n) Λ⁻¹ hΛτwET
      simpa [complexLorentzAction_inv] using this
    have hσwET : permAct (d := 1) σ w ∈ ExtendedTube 1 n := by
      have hΛσwET : complexLorentzAction Λ (permAct (d := 1) σ w) ∈ ExtendedTube 1 n := by
        simpa [hσy_as_action] using hσyET
      have := complexLorentzAction_mem_extendedTube (d := 1) (n := n) Λ⁻¹ hΛσwET
      simpa [complexLorentzAction_inv] using this
    exact ⟨w, hwFT, hτwET, hσwET⟩
  · rintro ⟨w, hwFT, hτwET, hσwET⟩
    exact ⟨w, forwardTube_subset_extendedTube hwFT, hτwET, hσwET⟩

end BHW
