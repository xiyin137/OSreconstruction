import OSReconstruction.ComplexLieGroups.AdjacentOverlapWitness
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
import OSReconstruction.ComplexLieGroups.Connectedness.Permutation

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

private def lorentzPermSector (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧ z = complexLorentzAction Λ w}

private theorem mem_lorentzPermSector_iff_perm_mem_extendedTube
    (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ) :
    z ∈ lorentzPermSector (d := d) (n := n) π ↔
      (fun k => z (π k)) ∈ ExtendedTube d n := by
  constructor
  · intro hz
    rcases hz with ⟨Λ, w, hw, rfl⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨Λ, (fun k => w (π k)), hw, ?_⟩
    ext k μ
    simp [complexLorentzAction]
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨Λ, w, hw, hzw⟩
    refine ⟨Λ, (fun k => w (π⁻¹ k)), ?_, ?_⟩
    · show (fun k => (fun j => w (π⁻¹ j)) (π k)) ∈ ForwardTube d n
      simpa using hw
    · ext k μ
      have hz_at_inv : z k μ = (complexLorentzAction Λ w) (π⁻¹ k) μ := by
        simpa using congr_arg (fun f => f (π⁻¹ k) μ) hzw
      rw [hz_at_inv]
      simp [complexLorentzAction]

private theorem adjacent_overlap_reduction_right
    (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n) :
    (lorentzPermSector (d := d) (n := n) π ∩
      lorentzPermSector (d := d) (n := n) (π * Equiv.swap i ⟨i.val + 1, hi⟩)).Nonempty ↔
    (∃ x : Fin n → Fin (d + 1) → ℂ,
      x ∈ ExtendedTube d n ∧
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) := by
  constructor
  · rintro ⟨z, hz1, hz2⟩
    have hz1' :=
      (mem_lorentzPermSector_iff_perm_mem_extendedTube (d := d) (n := n) π z).mp hz1
    have hz2' :=
      (mem_lorentzPermSector_iff_perm_mem_extendedTube (d := d) (n := n)
        (π * Equiv.swap i ⟨i.val + 1, hi⟩) z).mp hz2
    refine ⟨(fun k => z (π k)), hz1', ?_⟩
    simpa [Equiv.Perm.mul_apply] using hz2'
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨(fun k => x (π⁻¹ k)), ?_, ?_⟩
    · exact (mem_lorentzPermSector_iff_perm_mem_extendedTube (d := d) (n := n) π _).mpr
        (by simpa)
    · refine (mem_lorentzPermSector_iff_perm_mem_extendedTube (d := d) (n := n)
        (π * Equiv.swap i ⟨i.val + 1, hi⟩) _).mpr ?_
      simpa [Equiv.Perm.mul_apply] using hx2

/-- **Each Lorentz-permutation sector is preconnected.** -/
private theorem lorentzPermSector_isPreconnected (π : Equiv.Perm (Fin n)) :
    IsPreconnected
      ({z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ PermutedForwardTube d n π ∧ z = complexLorentzAction Λ w} :
        Set (Fin n → Fin (d + 1) → ℂ)) := by
  haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
    pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
  have hPFT_pre : IsPreconnected (PermutedForwardTube d n π) := by
    have hPFT : PermutedForwardTube d n π =
        (fun w k => w (π⁻¹ k)) '' ForwardTube d n := by
      ext z
      simp [PermutedForwardTube, Set.mem_image]
      constructor
      · intro hz
        exact ⟨fun k => z (π k), hz, by ext k; simp⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [hPFT]
    exact forwardTube_convex.isPreconnected.image _
      ((continuous_pi (fun k => continuous_apply (π⁻¹ k))).continuousOn)
  have hcont : Continuous (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
      complexLorentzAction p.1 p.2) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    simp only [complexLorentzAction]
    apply continuous_finset_sum
    intro ν _
    apply Continuous.mul
    · have hval : Continuous (fun (p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ)) =>
          p.1.val) := ComplexLorentzGroup.continuous_val.comp continuous_fst
      have hrow : Continuous (fun (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) => M μ) :=
        continuous_apply μ
      have hentry : Continuous (fun (r : Fin (d + 1) → ℂ) => r ν) :=
        continuous_apply ν
      exact hentry.comp (hrow.comp hval)
    · exact (continuous_apply ν).comp
        ((continuous_apply k).comp continuous_snd)
  suffices h : IsPreconnected ((fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
      complexLorentzAction p.1 p.2) '' (Set.univ ×ˢ PermutedForwardTube d n π)) from by
    convert h using 1
    ext z
    constructor
    · rintro ⟨Λ, w, hw, rfl⟩
      exact ⟨⟨Λ, w⟩, ⟨trivial, hw⟩, rfl⟩
    · rintro ⟨p, ⟨-, hw⟩, rfl⟩
      exact ⟨p.1, p.2, hw, rfl⟩
  exact (isPreconnected_univ.prod hPFT_pre).image _ hcont.continuousOn

private theorem extendedTube_eq_core :
    ExtendedTube d n = BHWCore.ExtendedTube d n := rfl

private theorem adjacent_sectors_overlap_right [NeZero d] (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n) :
    (lorentzPermSector (d := d) (n := n) π ∩
      lorentzPermSector (d := d) (n := n) (π * Equiv.swap i ⟨i.val + 1, hi⟩)).Nonempty := by
  rcases (adjacent_overlap_reduction_right (d := d) (n := n) π i hi) with hred
  by_cases hd2 : 2 ≤ d
  · apply hred.mpr
    rcases adjacent_overlap_witness_exists (d := d) (n := n) hd2 i hi with ⟨x, hx, hswapx⟩
    refine ⟨x, ?_, ?_⟩
    · simpa [extendedTube_eq_core (d := d) (n := n)] using hx
    · simpa [extendedTube_eq_core (d := d) (n := n)] using hswapx
  · have hd1 : d = 1 := by
      have hle : d ≤ 1 := Nat.not_lt.mp hd2
      have hge : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
      exact Nat.le_antisymm hle hge
    subst hd1
    apply hred.mpr
    rcases adjacent_overlap_witness_exists_d1 (n := n) i hi with ⟨x, hx, hswapx⟩
    refine ⟨x, ?_, ?_⟩
    · simpa [extendedTube_eq_core (d := 1) (n := n)] using hx
    · simpa [extendedTube_eq_core (d := 1) (n := n)] using hswapx

/-- **The permuted extended tube is preconnected.** -/
theorem permutedExtendedTube_isPreconnected [NeZero d] :
    IsPreconnected (@PermutedExtendedTube d n) := by
  show IsPreconnected (⋃ π : Equiv.Perm (Fin n),
    {z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧ z = complexLorentzAction Λ w})
  apply IsPreconnected.iUnion_of_reflTransGen
  · exact fun π => lorentzPermSector_isPreconnected π
  · intro π₁ π₂
    set τ := π₁⁻¹ * π₂
    suffices h : ∀ (σ : Equiv.Perm (Fin n)),
        Relation.ReflTransGen
          (fun i j => ((lorentzPermSector (d := d) (n := n) i) ∩
            lorentzPermSector (d := d) (n := n) j).Nonempty)
          π₁ (π₁ * σ) by
      have : π₂ = π₁ * τ := by simp [τ]
      rw [this]
      exact h τ
    intro σ
    induction σ using Fin.Perm.adjSwap_induction_right with
    | one =>
      simpa using Relation.ReflTransGen.refl
    | mul_adj σ₀ i₀ hi₀ ih =>
      apply Relation.ReflTransGen.tail ih
      simpa [lorentzPermSector, mul_assoc] using
        adjacent_sectors_overlap_right (π₁ * σ₀) i₀ hi₀

/-- The BHW permuted extended tube is connected: nonempty and preconnected. -/
theorem isConnected_permutedExtendedTube [NeZero d] :
    IsConnected (@PermutedExtendedTube d n) :=
  ⟨(forwardTube_nonempty (d := d) (n := n)).mono forwardTube_subset_permutedExtendedTube,
   permutedExtendedTube_isPreconnected⟩

end BHW
