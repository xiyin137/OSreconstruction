import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency

/-!
# Algebra after PET branch independence

This file contains the formal tail after the hard BHW/PET monodromy theorem.
It does not prove adjacent-to-all branch independence.  Instead it records the
small algebraic consequences once that single-valuedness statement is supplied.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

variable {d n : ℕ}

/-- A point of the ordinary permuted forward tube has at most one sector label.
The nontrivial fixed-fiber problem for PET therefore comes entirely from the
complex Lorentz orbit in `ExtendedTube`. -/
theorem permutedForwardTube_sector_eq_of_mem
    (π ρ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzπ : z ∈ PermutedForwardTube d n π)
    (hzρ : z ∈ PermutedForwardTube d n ρ) :
    π = ρ := by
  let w : Fin n → Fin (d + 1) → ℂ := fun k => z (π k)
  have hw : w ∈ ForwardTube d n := by
    simpa [w, PermutedForwardTube] using hzπ
  have hwσ : w ∈ PermutedForwardTube d n (π⁻¹ * ρ) := by
    simpa [w, PermutedForwardTube, Equiv.Perm.mul_apply] using hzρ
  have hσ :
      π⁻¹ * ρ = (1 : Equiv.Perm (Fin n)) :=
    permutedForwardTube_forces_perm_one (d := d) (n := n)
      (π⁻¹ * ρ) hw hwσ
  have := congr_arg (fun σ : Equiv.Perm (Fin n) => π * σ) hσ
  simpa using this.symm

/-- Extended-tube membership can be read in a forwardizing frame: a point is in
`ExtendedTube` iff some complex Lorentz transform sends it into `ForwardTube`.
This is often the most convenient form for PET fiber geometry. -/
theorem mem_extendedTube_iff_exists_lorentz_mem_forwardTube
    (z : Fin n → Fin (d + 1) → ℂ) :
    z ∈ ExtendedTube d n ↔
      ∃ Λ : ComplexLorentzGroup d,
        complexLorentzAction Λ z ∈ ForwardTube d n := by
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨Λ, w, hw, hzw⟩
    refine ⟨Λ⁻¹, ?_⟩
    rw [hzw, complexLorentzAction_inv]
    exact hw
  · rintro ⟨Λ, hΛz⟩
    refine Set.mem_iUnion.mpr ⟨Λ⁻¹, complexLorentzAction Λ z, hΛz, ?_⟩
    rw [complexLorentzAction_inv]

/-- One adjacent step inside the sector-label fiber over a fixed PET point. -/
def petSectorAdjStep
    (z : Fin n → Fin (d + 1) → ℂ)
    (π ρ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (i : Fin n) (hi : i.val + 1 < n),
    ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      z ∈ permutedExtendedTubeSector d n π ∧
      z ∈ permutedExtendedTubeSector d n ρ

/-- Sector labels reachable from a fixed point by reordering into the extended
tube.  For a forward-tube base point, the desired fixed-fiber theorem is graph
connectivity of this finite label set. -/
def petReachableLabelSet
    (w : Fin n → Fin (d + 1) → ℂ) :
    Set (Equiv.Perm (Fin n)) :=
  {σ | (fun k => w (σ k)) ∈ ExtendedTube d n}

/-- One adjacent edge in the reachable-label graph over a fixed point. -/
def petReachableLabelAdjStep
    (w : Fin n → Fin (d + 1) → ℂ)
    (π ρ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (i : Fin n) (hi : i.val + 1 < n),
    ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      π ∈ petReachableLabelSet (d := d) (n := n) w ∧
      ρ ∈ petReachableLabelSet (d := d) (n := n) w

/-- The identity label is reachable from every forward-tube point. -/
theorem one_mem_petReachableLabelSet_of_forwardTube
    {w : Fin n → Fin (d + 1) → ℂ}
    (hw : w ∈ ForwardTube d n) :
    (1 : Equiv.Perm (Fin n)) ∈
      petReachableLabelSet (d := d) (n := n) w := by
  simpa [petReachableLabelSet] using forwardTube_subset_extendedTube
    (d := d) (n := n) hw

/-- A reachable label is equivalently a permuted forward-tube chamber met by
the complex Lorentz orbit of the fixed point.  This is the orbit/chamber form
of the fixed-fiber geometry problem. -/
theorem mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube
    (w : Fin n → Fin (d + 1) → ℂ)
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ petReachableLabelSet (d := d) (n := n) w ↔
      ∃ Λ : ComplexLorentzGroup d,
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ := by
  change (fun k => w (σ k)) ∈ ExtendedTube d n ↔
    ∃ Λ : ComplexLorentzGroup d,
      complexLorentzAction Λ w ∈ PermutedForwardTube d n σ
  rw [
    mem_extendedTube_iff_exists_lorentz_mem_forwardTube (d := d) (n := n)
      (fun k => w (σ k))]
  constructor
  · rintro ⟨Λ, hΛ⟩
    refine ⟨Λ, ?_⟩
    simpa [PermutedForwardTube, lorentz_perm_commute] using hΛ
  · rintro ⟨Λ, hΛ⟩
    refine ⟨Λ, ?_⟩
    simpa [PermutedForwardTube, lorentz_perm_commute] using hΛ

/-- If every ordinary permuted-forward-tube chamber hit by the complex Lorentz
orbit of a forward-tube point is connected to the identity chamber by adjacent
hit chambers, then the reachable-label graph is connected. -/
theorem petReachableLabelSet_adjacent_connected_of_orbitChamberConnected
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          complexLorentzAction Λ w ∈ PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n →
      ∀ (σ : Equiv.Perm (Fin n)),
        σ ∈ petReachableLabelSet (d := d) (n := n) w →
        Relation.ReflTransGen
          (petReachableLabelAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ := by
  intro w hw σ hσ
  rcases (mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube
      (d := d) (n := n) w σ).mp hσ with ⟨Λ, hΛ⟩
  exact hOrbit w hw σ Λ hΛ

/-- The reachable-label graph is just the sector-fiber graph unfolded at the
fixed point. -/
theorem petSectorAdjStep_iff_petReachableLabelAdjStep
    (w : Fin n → Fin (d + 1) → ℂ)
    (π ρ : Equiv.Perm (Fin n)) :
    petSectorAdjStep (d := d) (n := n) w π ρ ↔
      petReachableLabelAdjStep (d := d) (n := n) w π ρ := by
  rfl

/-- The forward-tube fixed-fiber theorem follows from adjacent connectivity of
the reachable-label set.  This is the corrected replacement for the rejected
suffix-removal monotonicity target. -/
theorem petSectorFiber_forwardTube_chain_of_reachableLabelConnected
    (hReach :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)),
          σ ∈ petReachableLabelSet (d := d) (n := n) w →
          Relation.ReflTransGen
            (petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (σ : Equiv.Perm (Fin n))
      (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n →
      (fun k => w (σ k)) ∈ ExtendedTube d n →
      Relation.ReflTransGen
        (petSectorAdjStep (d := d) (n := n) w)
        (1 : Equiv.Perm (Fin n)) σ := by
  intro σ w hw hσ
  have hchain := hReach w hw σ hσ
  exact Relation.ReflTransGen.mono
    (fun α β h =>
      (petSectorAdjStep_iff_petReachableLabelAdjStep
        (d := d) (n := n) w α β).mpr h)
    hchain

/-- It suffices to prove fixed-fiber adjacent connectivity from the identity
sector to an arbitrary sector.  The general two-label statement follows by
reindexing the fixed point. -/
theorem petSectorFiber_adjacent_connected_of_identity_chain
    (hChain :
      ∀ (σ : Equiv.Perm (Fin n))
        (y : Fin n → Fin (d + 1) → ℂ),
        y ∈ ExtendedTube d n →
        (fun k => y (σ k)) ∈ ExtendedTube d n →
        Relation.ReflTransGen
          (petSectorAdjStep (d := d) (n := n) y)
          (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ permutedExtendedTubeSector d n π →
      z ∈ permutedExtendedTubeSector d n ρ →
      Relation.ReflTransGen
        (petSectorAdjStep (d := d) (n := n) z) π ρ := by
  intro π ρ z hzπ hzρ
  let σ : Equiv.Perm (Fin n) := π⁻¹ * ρ
  let y : Fin n → Fin (d + 1) → ℂ := fun k => z (π k)
  have hy : y ∈ ExtendedTube d n := by
    simpa [y, permutedExtendedTubeSector] using hzπ
  have hyσ : (fun k => y (σ k)) ∈ ExtendedTube d n := by
    simpa [y, σ, Equiv.Perm.mul_apply, permutedExtendedTubeSector] using hzρ
  have hσchain := hChain σ y hy hyσ
  have hlift :
      ∀ {τ : Equiv.Perm (Fin n)},
        Relation.ReflTransGen
          (petSectorAdjStep (d := d) (n := n) y)
          (1 : Equiv.Perm (Fin n)) τ →
        Relation.ReflTransGen
          (petSectorAdjStep (d := d) (n := n) z) π (π * τ) := by
    intro τ h
    induction h with
    | refl =>
        simpa using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen
              (petSectorAdjStep (d := d) (n := n) z) π π)
    | @tail α β hprev hlast ih =>
        rcases hlast with ⟨i, hi, hβ, hα_mem, hβ_mem⟩
        have hstep :
            petSectorAdjStep (d := d) (n := n) z (π * α) (π * β) := by
          refine ⟨i, hi, ?_, ?_, ?_⟩
          · simp [hβ, mul_assoc]
          · simpa [y, permutedExtendedTubeSector, Equiv.Perm.mul_apply] using hα_mem
          · simpa [y, permutedExtendedTubeSector, Equiv.Perm.mul_apply] using hβ_mem
        exact Relation.ReflTransGen.tail ih hstep
  simpa [σ, mul_assoc] using hlift hσchain

/-- Sector-label membership is invariant under complex Lorentz action. -/
theorem permutedExtendedTubeSector_complexLorentzAction_iff
    (Λ : ComplexLorentzGroup d)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction Λ z ∈ permutedExtendedTubeSector d n π ↔
      z ∈ permutedExtendedTubeSector d n π := by
  constructor
  · intro h
    have h' : complexLorentzAction Λ⁻¹ (fun k => (complexLorentzAction Λ z) (π k)) ∈
        ExtendedTube d n :=
      complexLorentzAction_mem_extendedTube n Λ⁻¹ h
    have hrewrite :
        complexLorentzAction Λ⁻¹ (fun k => (complexLorentzAction Λ z) (π k)) =
          fun k => z (π k) := by
      calc
        complexLorentzAction Λ⁻¹ (fun k => (complexLorentzAction Λ z) (π k))
            = complexLorentzAction Λ⁻¹
                (complexLorentzAction Λ (fun k => z (π k))) := by
                simp [lorentz_perm_commute]
        _ = fun k => z (π k) := by
                rw [complexLorentzAction_inv]
    rw [hrewrite] at h'
    simpa [permutedExtendedTubeSector] using h'
  · intro h
    have h' : complexLorentzAction Λ (fun k => z (π k)) ∈ ExtendedTube d n :=
      complexLorentzAction_mem_extendedTube n Λ h
    have hrewrite :
        (fun k => (complexLorentzAction Λ z) (π k)) =
          complexLorentzAction Λ (fun k => z (π k)) := by
      simp [lorentz_perm_commute]
    simpa [permutedExtendedTubeSector, hrewrite] using h'

/-- It suffices to prove the identity-chain geometry for points already in the
forward tube.  Any identity-chain problem in `ExtendedTube` can be moved into
the forward tube by a complex Lorentz transform, and sector labels are
Lorentz-invariant. -/
theorem petSectorFiber_identity_chain_of_forwardTube_chain
    (hChainFT :
      ∀ (σ : Equiv.Perm (Fin n))
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n →
        (fun k => w (σ k)) ∈ ExtendedTube d n →
        Relation.ReflTransGen
          (petSectorAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (σ : Equiv.Perm (Fin n))
      (y : Fin n → Fin (d + 1) → ℂ),
      y ∈ ExtendedTube d n →
      (fun k => y (σ k)) ∈ ExtendedTube d n →
      Relation.ReflTransGen
        (petSectorAdjStep (d := d) (n := n) y)
        (1 : Equiv.Perm (Fin n)) σ := by
  intro σ y hy hσy
  rcases Set.mem_iUnion.mp hy with ⟨Λ, w, hw, hy_eq⟩
  have hwσ : (fun k => w (σ k)) ∈ ExtendedTube d n := by
    have hmove : complexLorentzAction Λ⁻¹ (fun k => y (σ k)) ∈ ExtendedTube d n :=
      complexLorentzAction_mem_extendedTube n Λ⁻¹ hσy
    have hrewrite :
        complexLorentzAction Λ⁻¹ (fun k => y (σ k)) =
          fun k => w (σ k) := by
      calc
        complexLorentzAction Λ⁻¹ (fun k => y (σ k))
            = complexLorentzAction Λ⁻¹
                (fun k => (complexLorentzAction Λ w) (σ k)) := by
                rw [hy_eq]
        _ = complexLorentzAction Λ⁻¹
              (complexLorentzAction Λ (fun k => w (σ k))) := by
                simp [lorentz_perm_commute]
        _ = fun k => w (σ k) := by
                rw [complexLorentzAction_inv]
    simpa [hrewrite] using hmove
  have hchain := hChainFT σ w hw hwσ
  have hlift :
      ∀ {τ : Equiv.Perm (Fin n)},
        Relation.ReflTransGen
          (petSectorAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) τ →
        Relation.ReflTransGen
          (petSectorAdjStep (d := d) (n := n) y)
          (1 : Equiv.Perm (Fin n)) τ := by
    intro τ h
    induction h with
    | refl =>
        exact Relation.ReflTransGen.refl
    | @tail α β hprev hlast ih =>
        rcases hlast with ⟨i, hi, hβ, hα, hβmem⟩
        have hstep : petSectorAdjStep (d := d) (n := n) y α β := by
          refine ⟨i, hi, hβ, ?_, ?_⟩
          · rw [hy_eq]
            exact (permutedExtendedTubeSector_complexLorentzAction_iff
              (d := d) (n := n) Λ α w).mpr hα
          · rw [hy_eq]
            exact (permutedExtendedTubeSector_complexLorentzAction_iff
              (d := d) (n := n) Λ β w).mpr hβmem
        exact Relation.ReflTransGen.tail ih hstep
  exact hlift hchain

/-- Reachable-label graph connectivity is enough to prove the full fixed-fiber
adjacent connectivity theorem.  This is the checked route from the current
orbit/chamber geometry target to the PET sector-fiber statement. -/
theorem petSectorFiber_adjacent_connected_of_reachableLabelConnected
    (hReach :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)),
          σ ∈ petReachableLabelSet (d := d) (n := n) w →
          Relation.ReflTransGen
            (petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ permutedExtendedTubeSector d n π →
      z ∈ permutedExtendedTubeSector d n ρ →
      Relation.ReflTransGen
        (petSectorAdjStep (d := d) (n := n) z) π ρ := by
  exact
    petSectorFiber_adjacent_connected_of_identity_chain
      (d := d) (n := n)
      (petSectorFiber_identity_chain_of_forwardTube_chain
        (d := d) (n := n)
        (petSectorFiber_forwardTube_chain_of_reachableLabelConnected
          (d := d) (n := n) hReach))

/-- Diagnostic adapter: the forward-tube fixed-fiber chain would follow from a
suffix-removal geometry lemma.  The proof docs record that the unrestricted
suffix-removal hypothesis is too strong, so this theorem should not be treated
as the active geometry target. -/
theorem petSectorFiber_forwardTube_chain_of_suffixRemoval
    (hSuffix :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
          (fun k => w ((σ * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈
            ExtendedTube d n →
          (fun k => w (σ k)) ∈ ExtendedTube d n) :
    ∀ (σ : Equiv.Perm (Fin n))
      (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ ForwardTube d n →
      (fun k => w (σ k)) ∈ ExtendedTube d n →
      Relation.ReflTransGen
        (petSectorAdjStep (d := d) (n := n) w)
        (1 : Equiv.Perm (Fin n)) σ := by
  intro σ w hw
  revert σ
  refine Fin.Perm.adjSwap_induction_right (n := n)
    (motive := fun σ =>
      (fun k => w (σ k)) ∈ ExtendedTube d n →
      Relation.ReflTransGen
        (petSectorAdjStep (d := d) (n := n) w)
        (1 : Equiv.Perm (Fin n)) σ)
    ?base ?step
  · intro _h
    exact Relation.ReflTransGen.refl
  · intro σ i hi ih hσswap
    have hσ : (fun k => w (σ k)) ∈ ExtendedTube d n :=
      hSuffix w hw σ i hi hσswap
    have hchainσ := ih hσ
    have htail :
        petSectorAdjStep (d := d) (n := n) w σ
          (σ * Equiv.swap i ⟨i.val + 1, hi⟩) := by
      refine ⟨i, hi, rfl, ?_, ?_⟩
      · simpa [permutedExtendedTubeSector] using hσ
      · simpa [permutedExtendedTubeSector] using hσswap
    exact Relation.ReflTransGen.tail hchainσ htail

/-- If the sector-label fiber over each PET point is adjacent-connected, then
adjacent sector equality promotes to all-overlap PET branch independence.  The
hard geometry is isolated in `hFiber`; this theorem is only the algebraic
chain induction. -/
theorem extendF_pet_branch_independence_of_adjacent_of_sectorFiberConnected
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAdj :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) →
        extendF F (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
          extendF F (fun k => z (π k)))
    (hFiber :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n ρ →
        Relation.ReflTransGen (petSectorAdjStep (d := d) (n := n) z) π ρ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ permutedExtendedTubeSector d n π →
      z ∈ permutedExtendedTubeSector d n ρ →
      extendF F (fun k => z (π k)) =
        extendF F (fun k => z (ρ k)) := by
  intro π ρ z hzπ hzρ
  have hchain := hFiber π ρ z hzπ hzρ
  have hchain_eq :
      ∀ {ρ' : Equiv.Perm (Fin n)},
        Relation.ReflTransGen (petSectorAdjStep (d := d) (n := n) z) π ρ' →
        z ∈ permutedExtendedTubeSector d n ρ' →
        extendF F (fun k => z (π k)) =
          extendF F (fun k => z (ρ' k)) := by
    intro ρ' h
    induction h with
    | refl =>
        intro _hz
        rfl
    | tail hprev hlast ih =>
        intro _hz
        rcases hlast with ⟨i, hi, rfl, hleft, hright⟩
        exact (ih hleft).trans (hAdj _ i hi z hleft hright).symm
  exact hchain_eq hchain hzρ

/-- Reachable-label graph connectivity is the current honest geometry target
for adjacent-to-all PET branch independence.  Once that target is supplied,
the all-overlap branch equality follows by the checked fixed-fiber and chain
adapters. -/
theorem extendF_pet_branch_independence_of_adjacent_of_reachableLabelConnected
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAdj :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) →
        extendF F (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
          extendF F (fun k => z (π k)))
    (hReach :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)),
          σ ∈ petReachableLabelSet (d := d) (n := n) w →
          Relation.ReflTransGen
            (petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ permutedExtendedTubeSector d n π →
      z ∈ permutedExtendedTubeSector d n ρ →
      extendF F (fun k => z (π k)) =
        extendF F (fun k => z (ρ k)) := by
  exact
    extendF_pet_branch_independence_of_adjacent_of_sectorFiberConnected
      (d := d) (n := n) F hAdj
      (petSectorFiber_adjacent_connected_of_reachableLabelConnected
        (d := d) (n := n) hReach)

/-- Concrete orbit/chamber form of the current route: if the complex Lorentz
orbit of every forward-tube point hits a Cayley-connected set of ordinary
permuted-forward-tube chambers, then adjacent branch equality promotes to
all-overlap PET branch equality. -/
theorem extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAdj :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) →
        extendF F (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
          extendF F (fun k => z (π k)))
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          complexLorentzAction Λ w ∈ PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ permutedExtendedTubeSector d n π →
      z ∈ permutedExtendedTubeSector d n ρ →
      extendF F (fun k => z (π k)) =
        extendF F (fun k => z (ρ k)) := by
  exact
    extendF_pet_branch_independence_of_adjacent_of_reachableLabelConnected
      (d := d) (n := n) F hAdj
      (petReachableLabelSet_adjacent_connected_of_orbitChamberConnected
        (d := d) (n := n) hOrbit)

/-- PET branch independence implies the extended-tube permutation hypothesis
used by the public forward-tube permutation-invariance reduction. -/
theorem extendF_perm_eq_on_extendedTube_of_petBranchIndependence
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hPET :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n ρ →
        extendF F (fun k => z (π k)) =
          extendF F (fun k => z (ρ k))) :
    ∀ (τ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (τ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (τ k)) = extendF F z := by
  intro τ z hz hzτ
  have hzτ_sector : z ∈ permutedExtendedTubeSector d n τ := by
    simpa [permutedExtendedTubeSector] using hzτ
  have hz_id_sector : z ∈
      permutedExtendedTubeSector d n (1 : Equiv.Perm (Fin n)) := by
    simpa [permutedExtendedTubeSector] using hz
  simpa using
    hPET τ (1 : Equiv.Perm (Fin n)) z hzτ_sector hz_id_sector

/-- Once PET branches are single-valued, the selected forward-tube branch is
permutation invariant after any complex Lorentz move that lands back in the
forward tube. -/
theorem F_permutation_invariance_of_petBranchIndependence
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hPET :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n ρ →
        extendF F (fun k => z (π k)) =
          extendF F (fun k => z (ρ k)))
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {τ : Equiv.Perm (Fin n)} {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  exact
    permutation_invariance_of_extendF_on_extendedTube
      (d := d) n F hF_holo hF_lorentz
      (extendF_perm_eq_on_extendedTube_of_petBranchIndependence
        (d := d) (n := n) F hPET)
      hw h

/-- The witness-choice algebra for `fullExtendF` becomes non-circular once the
PET branch-independence theorem supplies `hPET`. -/
theorem fullExtendF_well_defined_of_petBranchIndependence
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hPET :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ permutedExtendedTubeSector d n π →
        z ∈ permutedExtendedTubeSector d n ρ →
        extendF F (fun k => z (π k)) =
          extendF F (fun k => z (ρ k)))
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ}
    (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {π₁ π₂ : Equiv.Perm (Fin n)} {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ (fun k => w₁ (π₁ k)) =
         complexLorentzAction Λ₂ (fun k => w₂ (π₂ k))) :
    F w₁ = F w₂ := by
  have step1 := congr_arg (complexLorentzAction Λ₁⁻¹) h
  rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one,
      ← complexLorentzAction_mul] at step1
  have hw₁_eq :
      w₁ = complexLorentzAction (Λ₁⁻¹ * Λ₂)
        (fun k => w₂ ((π₂ * π₁⁻¹) k)) := by
    ext m μ
    have := congr_fun (congr_fun step1 (π₁⁻¹ m)) μ
    rw [show π₁ (π₁⁻¹ m) = m from Equiv.apply_symm_apply π₁ m] at this
    rw [this]
    simp only [complexLorentzAction, Equiv.Perm.mul_apply]
  rw [hw₁_eq]
  exact
    F_permutation_invariance_of_petBranchIndependence
      (d := d) n F hF_holo hF_lorentz hPET hw₂ (hw₁_eq ▸ hw₁)

end BHW
