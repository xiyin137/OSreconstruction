import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanTubeIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1

noncomputable section

open Complex Topology

namespace BHW

variable {d n : ℕ}

@[simp] theorem permAct_one
    (z : Fin n → Fin (d + 1) → ℂ) :
    permAct (d := d) (1 : Equiv.Perm (Fin n)) z = z := by
  ext k μ
  simp [permAct]

theorem permAct_mul
    (π τ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    permAct (d := d) (π * τ) z =
      permAct (d := d) τ (permAct (d := d) π z) := by
  ext k μ
  simp [permAct, Equiv.Perm.mul_apply]

@[simp] theorem permAct_wickRotatePoint
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    permAct (d := d) σ (fun k => wickRotatePoint (x k)) =
      fun k => wickRotatePoint (x (σ k)) := by
  ext k μ
  simp [permAct]

@[simp] theorem permAct_realEmbed
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) :
    permAct (d := d) σ (realEmbed x) =
      realEmbed (fun k => x (σ k)) := by
  ext k μ
  simp [permAct, realEmbed]

end BHW

variable {d n : ℕ} [NeZero d]

namespace BHW

/-- Adjacent OS45 ordered Euclidean sectors give the two ordered Wick
forward-tube seed memberships used by the OS §4.5 branch-difference route. -/
theorem os45_adjacent_orderedWickSeeds_mem_forwardTube
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n)
    (ρ : Equiv.Perm (Fin n))
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (hx_swap_ordered :
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
    BHW.permAct (d := d) ρ (fun k => wickRotatePoint (x k)) ∈
        ForwardTube d n ∧
    BHW.permAct (d := d)
        ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
          (fun k => wickRotatePoint (x k))) ∈
        ForwardTube d n := by
  have hft_eq : ForwardTube d n = _root_.ForwardTube d n := by
    ext z
    simp only [ForwardTube, _root_.ForwardTube, Set.mem_setOf_eq]
    exact forall_congr' fun k => inOpenForwardCone_iff _
  constructor
  · have hroot :
        (fun k => wickRotatePoint (x (ρ k))) ∈ _root_.ForwardTube d n :=
      wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
        (d := d) (n := n) ρ hx_ordered
    simpa [hft_eq] using hroot
  · have hroot :=
      wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
        (d := d) (n := n) ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        (x := fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))
        hx_swap_ordered
    simpa [hft_eq, permAct, Equiv.Perm.mul_apply] using hroot

/-- Ordinary ordered Euclidean time places the adjacent-relabelled Wick point
in the selected adjacent permuted extended-tube sector.  This is the exact
membership used by the OS I §4.5 compact adjacent-edge boundary packet. -/
theorem os45_adjacentWick_mem_selectedAdjacentSector_of_ordered
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n)
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))) :
    (fun k => wickRotatePoint (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ∈
      BHW.permutedExtendedTubeSector d n
        (Equiv.swap i ⟨i.val + 1, hi⟩) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rw [BHW.permutedExtendedTubeSector]
  change
    (fun k => wickRotatePoint (x (τ (τ k)))) ∈ BHW.ExtendedTube d n
  have hft_eq : BHW.ForwardTube d n = _root_.ForwardTube d n := by
    ext z
    simp only [BHW.ForwardTube, _root_.ForwardTube, Set.mem_setOf_eq]
    exact forall_congr' fun k => inOpenForwardCone_iff _
  have hroot :
      (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
        _root_.ForwardTube d n :=
    wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) hx_ordered
  have hBHW :
      (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
    simpa [hft_eq] using hroot
  have hrewrite :
      (fun k => wickRotatePoint (x (τ (τ k)))) =
        fun k => wickRotatePoint (x k) := by
    ext k μ
    simp [τ, Equiv.swap_apply_self]
  rw [hrewrite]
  exact BHW.forwardTube_subset_extendedTube (d := d) (n := n) hBHW

end BHW
