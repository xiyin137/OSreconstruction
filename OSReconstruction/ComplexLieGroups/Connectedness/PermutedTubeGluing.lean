import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube

/-!
# Gluing over the permuted extended tube sector cover

This file contains the purely formal gluing step for the explicit PET sector
cover.  The hard BHW input is not here: callers must supply compatibility on
all sector overlaps.  Adjacent-to-all compatibility is the separate monodromy
problem in the OS route.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Glue a family of branch functions on the explicit PET sector cover by
choosing one sector on PET and returning zero off PET.  Meaningful statements
about this total function are PET-local. -/
noncomputable def gluedPETValue
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if hz : z ∈ PermutedExtendedTube d n then
      G (permutedExtendedTubeBranch (d := d) (n := n) z hz) z
    else
      0

/-- A glued PET value agrees with any sector branch, provided all branches agree
on all sector overlaps. -/
theorem gluedPETValue_eq_of_mem_sector
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hcompat :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n ρ →
        G π z = G ρ z)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ permutedExtendedTubeSector d n π) :
    gluedPETValue (d := d) (n := n) G z = G π z := by
  have hzPET : z ∈ PermutedExtendedTube d n :=
    permutedExtendedTubeSector_subset_permutedExtendedTube (d := d) (n := n) π hzπ
  have hbranch :
      z ∈ permutedExtendedTubeSector d n
        (permutedExtendedTubeBranch (d := d) (n := n) z hzPET) := by
    simpa [permutedExtendedTubeSector] using
      permutedExtendedTubeBranch_mem_extendedTube (d := d) (n := n) z hzPET
  unfold gluedPETValue
  simp only [dif_pos hzPET]
  exact hcompat
    (permutedExtendedTubeBranch (d := d) (n := n) z hzPET) π z hbranch hzπ

/-- If compatible branch functions are holomorphic on every explicit PET
sector, their glued PET value is holomorphic on PET. -/
theorem gluedPETValue_holomorphicOn
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hG_holo :
      ∀ π : Equiv.Perm (Fin n),
        DifferentiableOn ℂ (G π) (permutedExtendedTubeSector d n π))
    (hcompat :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n ρ →
        G π z = G ρ z) :
    DifferentiableOn ℂ (gluedPETValue (d := d) (n := n) G)
      (PermutedExtendedTube d n) := by
  intro z hzPET
  let π : Equiv.Perm (Fin n) :=
    permutedExtendedTubeBranch (d := d) (n := n) z hzPET
  have hzπ : z ∈ permutedExtendedTubeSector d n π := by
    simpa [π, permutedExtendedTubeSector] using
      permutedExtendedTubeBranch_mem_extendedTube (d := d) (n := n) z hzPET
  have hEq :
      gluedPETValue (d := d) (n := n) G =ᶠ[𝓝 z] G π := by
    filter_upwards
      [(isOpen_permutedExtendedTubeSector (d := d) (n := n) π).mem_nhds hzπ]
      with w hw
    exact gluedPETValue_eq_of_mem_sector (d := d) (n := n) G hcompat π w hw
  have hG_at : DifferentiableAt ℂ (G π) z :=
    (hG_holo π z hzπ).differentiableAt
      ((isOpen_permutedExtendedTubeSector (d := d) (n := n) π).mem_nhds hzπ)
  exact (hEq.differentiableAt_iff.mpr hG_at).differentiableWithinAt

end BHW

