import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.JostWitnessGeneralSigma
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.ComplexLieGroups.D1OrbitSet

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-- `π`-sector of points whose `π`-pullback lies in the extended tube. -/
private def permSector (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | permAct (d := d) π z ∈ ExtendedTube d n}

private lemma permAct_mul (π τ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    permAct (d := d) (π * τ) z =
      permAct (d := d) τ (permAct (d := d) π z) := by
  ext k μ
  simp [permAct, Equiv.Perm.mul_apply]

private lemma permAct_comp_inv (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    permAct (d := d) π (permAct (d := d) π⁻¹ z) = z := by
  ext k μ
  simp [permAct]

private theorem permSector_eq_image_extendedTube (n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    permSector (d := d) n π =
      (permAct (d := d) π⁻¹) '' (ExtendedTube d n) := by
  ext z
  constructor
  · intro hz
    exact ⟨permAct (d := d) π z, hz, by
      ext k μ
      simp [permAct]
    ⟩
  · rintro ⟨x, hxET, rfl⟩
    simpa [permSector, permAct_comp_inv (d := d) π x] using hxET

private theorem isConnected_permSector (n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    IsConnected (permSector (d := d) n π) := by
  have hcont : Continuous (permAct (d := d) π⁻¹) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (π⁻¹ k))
  have himage :
      IsConnected ((permAct (d := d) π⁻¹) '' (ExtendedTube d n)) :=
    isConnected_extendedTube (d := d) (n := n) |>.image _ hcont.continuousOn
  simpa [permSector_eq_image_extendedTube (d := d) n π] using himage

private theorem adjacent_permSector_overlap_nonempty [NeZero d]
    (n : ℕ) (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n) :
    (permSector (d := d) n π ∩
      permSector (d := d) n (π * Equiv.swap i ⟨i.val + 1, hi⟩)).Nonempty := by
  by_cases hd2 : 2 ≤ d
  · rcases adjacent_overlap_witness_exists (d := d) (n := n) hd2 i hi with
      ⟨x, hxET, hswapET⟩
    refine ⟨permAct (d := d) π⁻¹ x, ?_, ?_⟩
    · have hxET' : x ∈ ExtendedTube d n := by
        simpa [ExtendedTube, BHWCore.ExtendedTube] using hxET
      simpa [permSector, permAct_comp_inv (d := d) π x] using hxET'
    · have hswapET' : (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n := by
        simpa [ExtendedTube, BHWCore.ExtendedTube] using hswapET
      have hmul :
          permAct (d := d) (π * Equiv.swap i ⟨i.val + 1, hi⟩) (permAct (d := d) π⁻¹ x) =
            fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k) := by
        calc
          permAct (d := d) (π * Equiv.swap i ⟨i.val + 1, hi⟩) (permAct (d := d) π⁻¹ x)
              = permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                  (permAct (d := d) π (permAct (d := d) π⁻¹ x)) := by
                    simpa using
                      (permAct_mul (d := d) π (Equiv.swap i ⟨i.val + 1, hi⟩)
                        (permAct (d := d) π⁻¹ x))
          _ = permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) x := by
                simp [permAct_comp_inv (d := d) π x]
          _ = (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := rfl
      simpa [permSector, hmul] using hswapET'
  · have hd1 : d = 1 := by
      have hle : d ≤ 1 := Nat.not_lt.mp hd2
      have hge : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
      exact Nat.le_antisymm hle hge
    subst hd1
    rcases adjacent_overlap_witness_exists_d1 (n := n) i hi with
      ⟨x, hxET, hswapET⟩
    refine ⟨permAct (d := 1) π⁻¹ x, ?_, ?_⟩
    · have hxET' : x ∈ ExtendedTube 1 n := by
        simpa [ExtendedTube, BHWCore.ExtendedTube] using hxET
      simpa [permSector, permAct_comp_inv (d := 1) π x] using hxET'
    · have hswapET' : (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube 1 n := by
        simpa [ExtendedTube, BHWCore.ExtendedTube] using hswapET
      have hmul :
          permAct (d := 1) (π * Equiv.swap i ⟨i.val + 1, hi⟩) (permAct (d := 1) π⁻¹ x) =
            fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k) := by
        calc
          permAct (d := 1) (π * Equiv.swap i ⟨i.val + 1, hi⟩) (permAct (d := 1) π⁻¹ x)
              = permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩)
                  (permAct (d := 1) π (permAct (d := 1) π⁻¹ x)) := by
                    simpa using
                      (permAct_mul (d := 1) π (Equiv.swap i ⟨i.val + 1, hi⟩)
                        (permAct (d := 1) π⁻¹ x))
          _ = permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) x := by
                simp [permAct_comp_inv (d := 1) π x]
          _ = (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := rfl
      simpa [permSector, hmul] using hswapET'

/-- Adjacent-swap equality for `extendF` on neighboring permutation sectors,
specialized to the `d ≥ 2` connected-overlap route. -/
private theorem extendF_perm_adjacent_eq_on_sector_overlap_hd2
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (hd2 : 2 ≤ d)
    (hFwd_conn : ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected (adjSwapForwardOverlapSet (d := d) n i hi))
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzπ : z ∈ permSector (d := d) n π)
    (hzπs : z ∈ permSector (d := d) n (π * Equiv.swap i ⟨i.val + 1, hi⟩)) :
    extendF F (permAct (d := d) (π * Equiv.swap i ⟨i.val + 1, hi⟩) z) =
      extendF F (permAct (d := d) π z) := by
  let y : Fin n → Fin (d + 1) → ℂ := permAct (d := d) π z
  have hyET : y ∈ ExtendedTube d n := hzπ
  have hswapET : (fun k => y (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n := by
    have hyMul : permAct (d := d) (π * Equiv.swap i ⟨i.val + 1, hi⟩) z =
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) y := by
      simpa [y] using
        (permAct_mul (d := d) π (Equiv.swap i ⟨i.val + 1, hi⟩) z)
    have hEtMul : permAct (d := d) (π * Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n :=
      hzπs
    simpa [hyMul, permAct] using hEtMul
  have hswap :=
    extendF_adjSwap_eq_of_connected_forwardOverlap_hd2
      (d := d) n F hF_holo hF_lorentz hF_bv hF_local hd2 i hi (hFwd_conn i hi)
      y hyET hswapET
  simpa [y, permAct, Equiv.Perm.mul_apply] using hswap

/-- One adjacent-swap step in permutation space that preserves ET-membership
for the fixed configuration `z`. -/
private def etAdjStep (z : Fin n → Fin (d + 1) → ℂ)
    (π₁ π₂ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (i : Fin n) (hi : i.val + 1 < n),
    π₂ = π₁ * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      permAct (d := d) π₁ z ∈ ExtendedTube d n ∧
      permAct (d := d) π₂ z ∈ ExtendedTube d n

/-- Build an adjacent-swap chain from a one-step midpoint implication. -/
private theorem etAdj_chain_of_midCond
    (n : ℕ)
    (y : Fin n → Fin (d + 1) → ℂ)
    (hmidCond :
      ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
        permAct (d := d) σ y ∈ ExtendedTube d n)
    (τ : Equiv.Perm (Fin n))
    (_hy : y ∈ ExtendedTube d n)
    (hτy : permAct (d := d) τ y ∈ ExtendedTube d n) :
    Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ := by
  revert hτy
  refine Fin.Perm.adjSwap_induction_right (n := n)
    (motive := fun τ =>
      permAct (d := d) τ y ∈ ExtendedTube d n →
      Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ)
    ?base ?step τ
  · intro h1
    simpa [permAct] using Relation.ReflTransGen.refl
  · intro σ i hi ih hσswap
    have hσ : permAct (d := d) σ y ∈ ExtendedTube d n :=
      hmidCond σ i hi hσswap
    have hchainσ :
        Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 σ := ih hσ
    have htail :
        etAdjStep (d := d) (n := n) y σ (σ * Equiv.swap i ⟨i.val + 1, hi⟩) :=
      ⟨i, hi, rfl, hσ, hσswap⟩
    exact Relation.ReflTransGen.tail hchainσ htail

/-- Reduction wrapper: if adjacent-swap overlap invariance is available in each
forward-overlap slice and a permutation chain staying in ET-overlaps is provided,
then `extendF` is permutation-invariant on ET-overlaps. -/
private theorem extendF_perm_overlap_of_adjSwap_connected_and_chain_hd2
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (hd2 : 2 ≤ d)
    (hFwd_conn : ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected (adjSwapForwardOverlapSet (d := d) n i hi))
    (hChain :
      ∀ (τ : Equiv.Perm (Fin n)) (y : Fin n → Fin (d + 1) → ℂ),
        y ∈ ExtendedTube d n →
        permAct (d := d) τ y ∈ ExtendedTube d n →
        Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ) :
    ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  intro σ z hz hσz
  have hstep_eq :
      ∀ {π₁ π₂ : Equiv.Perm (Fin n)},
        etAdjStep (d := d) (n := n) z π₁ π₂ →
        extendF F (permAct (d := d) π₂ z) =
          extendF F (permAct (d := d) π₁ z) := by
    intro π₁ π₂ hstep
    rcases hstep with ⟨i, hi, hπ₂, hπ₁ET, hπ₂ET⟩
    have hzπ : z ∈ permSector (d := d) n π₁ := hπ₁ET
    have hzπs : z ∈ permSector (d := d) n (π₁ * Equiv.swap i ⟨i.val + 1, hi⟩) := by
      simpa [permSector, hπ₂] using hπ₂ET
    have hswap_eq :=
      extendF_perm_adjacent_eq_on_sector_overlap_hd2
        (d := d) n F hF_holo hF_lorentz hF_bv hF_local hd2 hFwd_conn π₁ i hi hzπ hzπs
    simpa [hπ₂] using hswap_eq
  have hchain := hChain σ z hz hσz
  have hchain_eq :
      ∀ {π : Equiv.Perm (Fin n)},
        Relation.ReflTransGen (etAdjStep (d := d) (n := n) z) 1 π →
        extendF F (permAct (d := d) π z) = extendF F z := by
    intro π h
    induction h with
    | refl =>
        change extendF F z = extendF F z
        rfl
    | @tail a b hprev hlast ih =>
        exact (hstep_eq hlast).trans ih
  exact hchain_eq hchain

/-- Reduction wrapper for the nontrivial (`d ≥ 2`) permutation branch:
if all adjacent forward-overlap slices are connected and one can always drop a
final adjacent swap while staying in ET, then overlap permutation-invariance of
`extendF` follows. -/
private theorem extendF_perm_overlap_of_adjSwap_connected_and_midCond_hd2
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (hd2 : 2 ≤ d)
    (hFwd_conn : ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected (adjSwapForwardOverlapSet (d := d) n i hi))
    (hmidCond :
      ∀ (y : Fin n → Fin (d + 1) → ℂ)
        (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
        permAct (d := d) σ y ∈ ExtendedTube d n) :
    ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hChain :
      ∀ (τ : Equiv.Perm (Fin n)) (y : Fin n → Fin (d + 1) → ℂ),
        y ∈ ExtendedTube d n →
        permAct (d := d) τ y ∈ ExtendedTube d n →
        Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ := by
    intro τ y hy hτy
    have hmidCond_y :
        ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
          permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n →
          permAct (d := d) σ y ∈ ExtendedTube d n := by
      intro σ i hi h
      exact hmidCond y σ i hi h
    exact etAdj_chain_of_midCond (d := d) n y hmidCond_y τ hy hτy
  exact extendF_perm_overlap_of_adjSwap_connected_and_chain_hd2
    (d := d) n F hF_holo hF_lorentz hF_bv hF_local hd2 hFwd_conn hChain

/-- One right-adjacent permutation step on forward-tube invariance, assuming the
intermediate point `Γ · (σ · w)` already lies in `FT`.

This isolates the exact missing geometric input in permutation-chain arguments:
to advance from `σ` to `σ * swap(i,i+1)`, it is enough to provide midpoint
forward-tube membership for the same `w, Γ`. -/
private theorem eow_chain_adj_swap_of_midpoint
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ₀ : Equiv.Perm (Fin n)) (i₀ : Fin n) (hi₀ : i₀.val + 1 < n)
    (ih_σ : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (σ₀ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (σ₀ k))) = F w)
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {Γ : ComplexLorentzGroup d}
    (hmid : complexLorentzAction Γ (fun k => w (σ₀ k)) ∈ ForwardTube d n)
    (h : complexLorentzAction Γ
      (fun k => w ((σ₀ * Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩) k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ
      (fun k => w ((σ₀ * Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩) k))) = F w := by
  set swap : Equiv.Perm (Fin n) := Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩
  set z : Fin n → Fin (d + 1) → ℂ :=
    complexLorentzAction Γ (fun k => w (σ₀ k))
  have hz : z ∈ ForwardTube d n := hmid
  have hswapz : (fun k => z (swap k)) ∈ ForwardTube d n := by
    simpa [z, swap, Equiv.Perm.mul_apply, lorentz_perm_commute] using h
  have hswap : F (fun k => z (swap k)) = F z :=
    eow_adj_swap_on_overlap n F hF_holo hF_lorentz hF_bv hF_local i₀ hi₀ hz hswapz
  have hσ : F z = F w := ih_σ w hw Γ hmid
  simpa [z, swap, Equiv.Perm.mul_apply, lorentz_perm_commute] using hswap.trans hσ

/-- Right-adjacent permutation step from a midpoint implication.

If every witness `Γ · ((σ * swap) · w) ∈ FT` implies
`Γ · (σ · w) ∈ FT`, then one adjacent step in permutation-invariance follows. -/
private theorem eow_chain_adj_swap_of_midCond
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ₀ : Equiv.Perm (Fin n)) (i₀ : Fin n) (hi₀ : i₀.val + 1 < n)
    (hmidCond :
      ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
        ∀ (Γ : ComplexLorentzGroup d),
          complexLorentzAction Γ
            (fun k => w ((σ₀ * Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩) k)) ∈ ForwardTube d n →
          complexLorentzAction Γ (fun k => w (σ₀ k)) ∈ ForwardTube d n)
    (ih_σ : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (σ₀ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (σ₀ k))) = F w)
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ
      (fun k => w ((σ₀ * Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩) k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ
      (fun k => w ((σ₀ * Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩) k))) = F w := by
  have hmid : complexLorentzAction Γ (fun k => w (σ₀ k)) ∈ ForwardTube d n :=
    hmidCond w hw Γ h
  exact eow_chain_adj_swap_of_midpoint n F hF_holo hF_lorentz hF_bv hF_local
    σ₀ i₀ hi₀ ih_σ hw hmid h

/-- Extended-tube overlap domain for a fixed permutation `σ`. -/
private def permExtendedOverlapSet (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | z ∈ ExtendedTube d n ∧ permAct (d := d) σ z ∈ ExtendedTube d n}

/-- In this file we reuse the shared seed-set definition from `SeedSlices`. -/
private abbrev permOrbitSeedSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → Fin (d + 1) → ℂ) :=
  permSeedSet (d := d) n σ

/-- Fixed-`Λ` slice for permutation forward-overlap witnesses. -/
private def permForwardOverlapSlice
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {w | w ∈ ForwardTube d n ∧ complexLorentzAction Λ (permAct (d := d) σ w) ∈ ForwardTube d n}

/-- Membership in `permForwardOverlapSet` is equivalent to existence of a fixed-`Λ`
forward-overlap slice witness. -/
private theorem mem_permForwardOverlapSet_iff_exists_lorentz
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : Fin n → Fin (d + 1) → ℂ) :
    w ∈ permForwardOverlapSet (d := d) n σ ↔
      ∃ Λ : ComplexLorentzGroup d, w ∈ permForwardOverlapSlice (d := d) n σ Λ := by
  constructor
  · intro hw
    rcases hw with ⟨hwFT, hwET⟩
    rcases Set.mem_iUnion.mp hwET with ⟨Λ, u, huFT, hu_eq⟩
    refine ⟨Λ⁻¹, ⟨hwFT, ?_⟩⟩
    simpa [hu_eq, complexLorentzAction_inv] using huFT
  · rintro ⟨Λ, hw⟩
    refine ⟨hw.1, ?_⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨Λ⁻¹, complexLorentzAction Λ (permAct (d := d) σ w), hw.2, ?_⟩
    simp [complexLorentzAction_inv]

/-- `permForwardOverlapSet` is the union of fixed-`Λ` slices. -/
private theorem permForwardOverlapSet_eq_iUnion_slices
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permForwardOverlapSet (d := d) n σ =
      ⋃ Λ : ComplexLorentzGroup d, permForwardOverlapSlice (d := d) n σ Λ := by
  ext w
  constructor
  · intro hw
    rcases (mem_permForwardOverlapSet_iff_exists_lorentz (d := d) n σ w).mp hw with ⟨Λ, hΛ⟩
    exact Set.mem_iUnion.mpr ⟨Λ, hΛ⟩
  · intro hw
    rcases Set.mem_iUnion.mp hw with ⟨Λ, hΛ⟩
    exact (mem_permForwardOverlapSet_iff_exists_lorentz (d := d) n σ w).mpr ⟨Λ, hΛ⟩

/-- A witness in a fixed `permForwardOverlapSlice` persists for `Λ'` in a neighborhood
of `Λ` (openness in the Lorentz variable). -/
private theorem permForwardOverlapSlice_nonempty_nhds
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {Λ : ComplexLorentzGroup d}
    {w : Fin n → Fin (d + 1) → ℂ}
    (hw : w ∈ permForwardOverlapSlice (d := d) n σ Λ) :
    ∃ V : Set (ComplexLorentzGroup d), IsOpen V ∧ Λ ∈ V ∧
      ∀ Λ' ∈ V, w ∈ permForwardOverlapSlice (d := d) n σ Λ' := by
  refine ⟨{Λ' : ComplexLorentzGroup d |
      complexLorentzAction Λ' (permAct (d := d) σ w) ∈ ForwardTube d n},
    ?_, hw.2, ?_⟩
  · have hcont : Continuous (fun Λ' : ComplexLorentzGroup d =>
        complexLorentzAction Λ' (permAct (d := d) σ w)) :=
      continuous_complexLorentzAction_fst _
    exact isOpen_forwardTube.preimage hcont
  · intro Λ' hΛ'
    exact ⟨hw.1, hΛ'⟩

/-- Equivalent form of `permOrbitSeedSet` as an ET/permuted-FT intersection. -/
private theorem permOrbitSeedSet_eq_inter_permutedForwardTube
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permOrbitSeedSet (d := d) n σ =
      ExtendedTube d n ∩ PermutedForwardTube d n σ⁻¹ := by
  simpa [permOrbitSeedSet] using
    permSeedSet_eq_inter_permutedForwardTube (d := d) n σ

/-- The seed set is open as an ET/permuted-FT intersection. -/
private theorem isOpen_permOrbitSeedSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsOpen (permOrbitSeedSet (d := d) n σ) := by
  simpa [permOrbitSeedSet] using isOpen_permSeedSet (d := d) n σ

/-- Reduction of seed-orbit preconnectedness to FT-family assumptions.

If each FT witness has Baire orbit subtype and preconnected orbit image, and
stabilizers are connected on the seed set, then every seed orbit set is
preconnected. -/
private theorem seedOrbitPreconnected_of_forwardTube_families
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hStabSeed : ∀ z ∈ permOrbitSeedSet (d := d) n σ,
      IsConnected (stabilizer (d := d) (n := n) z))
    (hBaireFT : ∀ u : Fin n → Fin (d + 1) → ℂ,
      u ∈ ForwardTube d n → BaireSpace (orbitSubtype (d := d) (n := n) u))
    (hPreImgFT : ∀ u : Fin n → Fin (d + 1) → ℂ,
      u ∈ ForwardTube d n →
      PreconnectedSpace (orbitMap (d := d) (n := n) u '' orbitSet (d := d) (n := n) u)) :
    ∀ z ∈ permOrbitSeedSet (d := d) n σ,
      IsPreconnected (orbitSet (d := d) z) := by
  intro z hzSeed
  rcases Set.mem_iUnion.mp hzSeed.1 with ⟨Δ, u, huFT, hz_eq⟩
  letI : BaireSpace (orbitSubtype (d := d) (n := n) u) := hBaireFT u huFT
  letI : PreconnectedSpace (orbitMap (d := d) (n := n) u '' orbitSet (d := d) (n := n) u) :=
    hPreImgFT u huFT
  exact orbitSet_isPreconnected_of_forwardTube_witness (d := d) (n := n)
    z u Δ huFT hz_eq (hStabSeed z hzSeed)

private theorem permOrbitSeedSet_eq_image_permForwardOverlapSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permOrbitSeedSet (d := d) n σ =
      (permAct (d := d) σ) '' (permForwardOverlapSet (d := d) n σ) := by
  simpa [permOrbitSeedSet] using
    permSeedSet_eq_image_permForwardOverlapSet (d := d) n σ

private theorem permForwardOverlapSet_eq_image_permOrbitSeedSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permForwardOverlapSet (d := d) n σ =
      (permAct (d := d) σ⁻¹) '' (permOrbitSeedSet (d := d) n σ) := by
  simpa [permOrbitSeedSet] using
    permForwardOverlapSet_eq_image_permSeedSet (d := d) n σ

private theorem isConnected_permOrbitSeedSet_iff_permForwardOverlapSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsConnected (permOrbitSeedSet (d := d) n σ) ↔
      IsConnected (permForwardOverlapSet (d := d) n σ) := by
  simpa [permOrbitSeedSet] using
    isConnected_permSeedSet_iff_permForwardOverlapSet (d := d) n σ

/-- Membership in the permutation index set is equivalent to existence of an ET seed
whose Lorentz image lies in the forward tube. -/
private theorem mem_permForwardOverlapIndexSet_iff_exists_seed
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    Λ ∈ permForwardOverlapIndexSet (d := d) n σ ↔
      ∃ z ∈ permOrbitSeedSet (d := d) n σ,
        complexLorentzAction Λ z ∈ ForwardTube d n := by
  constructor
  · rintro ⟨w, hwFT, hΛσwFT⟩
    refine ⟨permAct (d := d) σ w, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine Set.mem_iUnion.mpr ?_
        refine ⟨Λ⁻¹, complexLorentzAction Λ (permAct (d := d) σ w), hΛσwFT, ?_⟩
        simp [complexLorentzAction_inv]
      · show (fun k => (permAct (d := d) σ w) (σ⁻¹ k)) ∈ ForwardTube d n
        simpa [permAct] using hwFT
    · simpa using hΛσwFT
  · rintro ⟨z, hzSeed, hΛzFT⟩
    refine ⟨permAct (d := d) σ⁻¹ z, ?_, ?_⟩
    · simpa [permOrbitSeedSet, permSeedSet, PermutedForwardTube, permAct] using hzSeed.2
    · have hcancel : permAct (d := d) σ (permAct (d := d) σ⁻¹ z) = z := by
        ext k μ
        simp [permAct]
      simpa [hcancel] using hΛzFT

/-- The permutation index set is a union of orbit sets over ET seeds of the form
`permAct σ w` with `w ∈ FT`. -/
private theorem permForwardOverlapIndexSet_eq_iUnion_orbitSet_seed
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permForwardOverlapIndexSet (d := d) n σ
      = ⋃ z : {z : Fin n → Fin (d + 1) → ℂ | z ∈ permOrbitSeedSet (d := d) n σ},
          orbitSet (d := d) z.1 := by
  ext Λ
  constructor
  · intro hΛ
    rcases (mem_permForwardOverlapIndexSet_iff_exists_seed (d := d) n σ Λ).1 hΛ with
      ⟨z, hzSeed, hΛzFT⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨⟨z, hzSeed⟩, ?_⟩
    simpa [orbitSet] using hΛzFT
  · intro hΛ
    rcases Set.mem_iUnion.mp hΛ with ⟨z, hΛorbit⟩
    have hΛzFT : complexLorentzAction Λ z.1 ∈ ForwardTube d n := by
      simpa [orbitSet] using hΛorbit
    exact (mem_permForwardOverlapIndexSet_iff_exists_seed (d := d) n σ Λ).2
      ⟨z.1, z.2, hΛzFT⟩

/-- Any ET point can be moved into the forward tube by some complex Lorentz element. -/
private theorem exists_lorentz_to_forward_of_mem_extendedTube
    (n : ℕ) {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n) :
    ∃ Λ : ComplexLorentzGroup d, complexLorentzAction Λ z ∈ ForwardTube d n := by
  rcases Set.mem_iUnion.mp hz with ⟨Λ, w, hwFT, hz_eq⟩
  refine ⟨Λ⁻¹, ?_⟩
  simpa [hz_eq, complexLorentzAction_inv] using hwFT

/-- If the ET seed set is connected, then any two seeds are linked by a
refl-transitive chain whose successive orbit sets overlap nontrivially. -/
private theorem reflTransGen_seed_orbit_overlap_of_seedConnected
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hseed_conn : IsConnected (permOrbitSeedSet (d := d) n σ)) :
    ∀ (a b : {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z}),
      Relation.ReflTransGen
        (fun x y : {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} =>
          ((orbitSet (d := d) x.1) ∩ (orbitSet (d := d) y.1)).Nonempty)
        a b := by
  intro a b
  let R :
      {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} →
      {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} → Prop :=
    fun x y =>
      ((orbitSet (d := d) x.1) ∩ (orbitSet (d := d) y.1)).Nonempty
  let U :
      Set {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} :=
    {x | Relation.ReflTransGen R a x}

  have hU_open : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hxU
    have hxET : x.1 ∈ ExtendedTube d n := x.2.1
    rcases exists_lorentz_to_forward_of_mem_extendedTube (d := d) n hxET with ⟨Λ0, hΛ0xFT⟩
    let W :
        Set {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} :=
      {y | complexLorentzAction Λ0 y.1 ∈ ForwardTube d n}
    have hW_open : IsOpen W := by
      have hcont : Continuous (fun y :
          {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} =>
            complexLorentzAction Λ0 y.1) :=
        (continuous_complexLorentzAction_snd Λ0).comp continuous_subtype_val
      exact isOpen_forwardTube.preimage hcont
    have hxW : x ∈ W := hΛ0xFT
    refine Filter.mem_of_superset (hW_open.mem_nhds hxW) ?_
    intro y hyW
    have hxy : R x y := ⟨Λ0, hΛ0xFT, hyW⟩
    exact Relation.ReflTransGen.tail hxU hxy

  have hU_closed : IsClosed U := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro x hxU
    have hxET : x.1 ∈ ExtendedTube d n := x.2.1
    rcases exists_lorentz_to_forward_of_mem_extendedTube (d := d) n hxET with ⟨Λ0, hΛ0xFT⟩
    let W :
        Set {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} :=
      {y | complexLorentzAction Λ0 y.1 ∈ ForwardTube d n}
    have hW_open : IsOpen W := by
      have hcont : Continuous (fun y :
          {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} =>
            complexLorentzAction Λ0 y.1) :=
        (continuous_complexLorentzAction_snd Λ0).comp continuous_subtype_val
      exact isOpen_forwardTube.preimage hcont
    have hxW : x ∈ W := hΛ0xFT
    refine Filter.mem_of_superset (hW_open.mem_nhds hxW) ?_
    intro y hyW hyU
    have hyx : R y x := ⟨Λ0, hyW, hΛ0xFT⟩
    have hx_inU : x ∈ U := Relation.ReflTransGen.tail hyU hyx
    exact hxU hx_inU

  have hU_nonempty : U.Nonempty := ⟨a, Relation.ReflTransGen.refl⟩
  haveI : ConnectedSpace {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z} :=
    Subtype.connectedSpace hseed_conn
  have hU_eq : U = Set.univ := IsClopen.eq_univ ⟨hU_closed, hU_open⟩ hU_nonempty
  have hbU : b ∈ U := by simp [hU_eq]
  exact hbU

/-- Connectedness reduction for permutation index sets through ET seeds:
if the seed set is connected and each seed orbit set is preconnected, then the
index set is connected. -/
private theorem isConnected_permForwardOverlapIndexSet_of_seedConnected_and_seedOrbitPreconnected
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hseed_conn : IsConnected (permOrbitSeedSet (d := d) n σ))
    (hseed_orbit_pre : ∀ z ∈ permOrbitSeedSet (d := d) n σ,
      IsPreconnected (orbitSet (d := d) z)) :
    IsConnected (permForwardOverlapIndexSet (d := d) n σ) := by
  have hpre_union :
      IsPreconnected
        (⋃ z : {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z},
          orbitSet (d := d) z.1) := by
    apply IsPreconnected.iUnion_of_reflTransGen
    · intro z
      exact hseed_orbit_pre z.1 z.2
    · intro z1 z2
      exact reflTransGen_seed_orbit_overlap_of_seedConnected (d := d) n σ hseed_conn z1 z2
  have hUnion_eq :
      (⋃ z : {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z},
        orbitSet (d := d) z.1) =
      permForwardOverlapIndexSet (d := d) n σ := by
    symm
    exact permForwardOverlapIndexSet_eq_iUnion_orbitSet_seed (d := d) n σ
  have hnonempty : (permForwardOverlapIndexSet (d := d) n σ).Nonempty := by
    rcases hseed_conn.1 with ⟨z, hz⟩
    rcases exists_lorentz_to_forward_of_mem_extendedTube (d := d) n hz.1 with ⟨Λ0, hΛ0zFT⟩
    have hΛ0 : Λ0 ∈ orbitSet (d := d) z := by simpa [orbitSet] using hΛ0zFT
    have hΛ0_union :
        Λ0 ∈ ⋃ z : {z : Fin n → Fin (d + 1) → ℂ | permOrbitSeedSet (d := d) n σ z},
          orbitSet (d := d) z.1 := Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hΛ0⟩
    exact ⟨Λ0, hUnion_eq ▸ hΛ0_union⟩
  refine ⟨hnonempty, ?_⟩
  rw [← hUnion_eq]
  exact hpre_union

/-- `d = 1` specialization: connected ET seed set implies connected permutation
index set, using the `d = 1` orbit-preconnectedness theorem. -/
private theorem isConnected_permForwardOverlapIndexSet_d1_of_seedConnected
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hseed_conn : IsConnected (permOrbitSeedSet (d := 1) n σ)) :
    IsConnected (permForwardOverlapIndexSet (d := 1) n σ) := by
  refine isConnected_permForwardOverlapIndexSet_of_seedConnected_and_seedOrbitPreconnected
    (d := 1) n σ hseed_conn ?_
  intro z hz
  exact orbitSet_isPreconnected_d1_of_mem_extendedTube (n := n) hz.1

/-- Openness of the permutation forward-overlap index set. -/
private theorem isOpen_permForwardOverlapIndexSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsOpen (permForwardOverlapIndexSet (d := d) n σ) := by
  rw [isOpen_iff_mem_nhds]
  intro Λ hΛ
  rcases hΛ with ⟨w, hw⟩
  rcases permForwardOverlapSlice_nonempty_nhds (d := d) (n := n) σ hw with
    ⟨V, hV_open, hΛV, hV_sub⟩
  refine Filter.mem_of_superset (hV_open.mem_nhds hΛV) ?_
  intro Λ' hΛ'V
  exact ⟨w, hV_sub Λ' hΛ'V⟩

/-- Nonemptiness transfer: nonempty forward-overlap set implies nonempty index set. -/
private theorem nonempty_permForwardOverlapIndexSet_of_forwardOverlapNonempty
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hnonempty : (permForwardOverlapSet (d := d) n σ).Nonempty) :
    (permForwardOverlapIndexSet (d := d) n σ).Nonempty := by
  rcases hnonempty with ⟨w, hw⟩
  rw [permForwardOverlapSet_eq_iUnion_slices (d := d) n σ] at hw
  rcases Set.mem_iUnion.mp hw with ⟨Λ, hΛ⟩
  exact ⟨Λ, ⟨w, hΛ⟩⟩

/-- Left multiplication by real Lorentz elements preserves the index set. -/
private theorem permIndexSet_left_mul_ofReal
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ permForwardOverlapIndexSet (d := d) n σ)
    (R : RestrictedLorentzGroup d) :
    ComplexLorentzGroup.ofReal R * Λ ∈ permForwardOverlapIndexSet (d := d) n σ := by
  rcases hΛ with ⟨w, hw⟩
  refine ⟨w, ⟨hw.1, ?_⟩⟩
  have hmul :
      complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ)
        (permAct (d := d) σ w) =
      complexLorentzAction (ComplexLorentzGroup.ofReal R)
        (complexLorentzAction Λ (permAct (d := d) σ w)) := by
    simpa using complexLorentzAction_mul
      (ComplexLorentzGroup.ofReal R) Λ (permAct (d := d) σ w)
  rw [hmul]
  exact ofReal_preserves_forwardTube R _ hw.2

/-- Right multiplication by real Lorentz elements preserves the index set. -/
private theorem permIndexSet_right_mul_ofReal
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ permForwardOverlapIndexSet (d := d) n σ)
    (R : RestrictedLorentzGroup d) :
    Λ * ComplexLorentzGroup.ofReal R ∈ permForwardOverlapIndexSet (d := d) n σ := by
  rcases hΛ with ⟨w, hw⟩
  let w' : Fin n → Fin (d + 1) → ℂ :=
    complexLorentzAction (ComplexLorentzGroup.ofReal R⁻¹) w
  refine ⟨w', ?_⟩
  have hw'_FT : w' ∈ ForwardTube d n := by
    simpa [w'] using ofReal_preserves_forwardTube (R := R⁻¹) w hw.1
  refine ⟨hw'_FT, ?_⟩
  have hcommR :
      complexLorentzAction (ComplexLorentzGroup.ofReal R) (permAct (d := d) σ w') =
      permAct (d := d) σ (complexLorentzAction (ComplexLorentzGroup.ofReal R) w') :=
    lorentz_perm_commute (ComplexLorentzGroup.ofReal R) w' σ
  have hw'_cancel : complexLorentzAction (ComplexLorentzGroup.ofReal R) w' = w := by
    calc
      complexLorentzAction (ComplexLorentzGroup.ofReal R) w'
          = complexLorentzAction
              (ComplexLorentzGroup.ofReal R * ComplexLorentzGroup.ofReal R⁻¹) w := by
                simp [w', complexLorentzAction_mul]
      _ = complexLorentzAction (ComplexLorentzGroup.ofReal (R * R⁻¹)) w := by
            rw [← ofReal_mul_eq]
      _ = complexLorentzAction (ComplexLorentzGroup.ofReal (1 : RestrictedLorentzGroup d)) w := by
            simp
      _ = complexLorentzAction (1 : ComplexLorentzGroup d) w := by
            simp [ofReal_one_eq]
      _ = w := complexLorentzAction_one w
  have hstep :
      complexLorentzAction (Λ * ComplexLorentzGroup.ofReal R) (permAct (d := d) σ w') =
      complexLorentzAction Λ (permAct (d := d) σ w) := by
    calc
      complexLorentzAction (Λ * ComplexLorentzGroup.ofReal R) (permAct (d := d) σ w')
          = complexLorentzAction Λ
              (complexLorentzAction (ComplexLorentzGroup.ofReal R) (permAct (d := d) σ w')) := by
              simpa using complexLorentzAction_mul Λ (ComplexLorentzGroup.ofReal R)
                (permAct (d := d) σ w')
      _ = complexLorentzAction Λ
            (permAct (d := d) σ (complexLorentzAction (ComplexLorentzGroup.ofReal R) w')) := by
            simp [hcommR]
      _ = complexLorentzAction Λ (permAct (d := d) σ w) := by
            simp [hw'_cancel]
  rw [hstep]
  exact hw.2

/-- Left real multiplication yields joining paths in the index set. -/
private theorem permIndexSet_joined_left_ofReal
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ permForwardOverlapIndexSet (d := d) n σ)
    (R : RestrictedLorentzGroup d) :
    JoinedIn (permForwardOverlapIndexSet (d := d) n σ)
      Λ (ComplexLorentzGroup.ofReal R * Λ) := by
  have hj : JoinedIn Set.univ (1 : RestrictedLorentzGroup d) R :=
    (RestrictedLorentzGroup.isPathConnected (d := d)).joinedIn 1
      (Set.mem_univ _) R (Set.mem_univ _)
  rcases joinedIn_univ.mp hj with ⟨γ⟩
  refine ⟨
    { toFun := fun t => ComplexLorentzGroup.ofReal (γ t) * Λ
      continuous_toFun := (continuous_ofReal.comp γ.continuous_toFun).mul continuous_const
      source' := by rw [γ.source, ofReal_one_eq, one_mul]
      target' := by rw [γ.target] },
    ?_⟩
  intro t
  exact permIndexSet_left_mul_ofReal (d := d) n σ hΛ (γ t)

/-- Right real multiplication yields joining paths in the index set. -/
private theorem permIndexSet_joined_right_ofReal
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ permForwardOverlapIndexSet (d := d) n σ)
    (R : RestrictedLorentzGroup d) :
    JoinedIn (permForwardOverlapIndexSet (d := d) n σ)
      Λ (Λ * ComplexLorentzGroup.ofReal R) := by
  have hj : JoinedIn Set.univ (1 : RestrictedLorentzGroup d) R :=
    (RestrictedLorentzGroup.isPathConnected (d := d)).joinedIn 1
      (Set.mem_univ _) R (Set.mem_univ _)
  rcases joinedIn_univ.mp hj with ⟨γ⟩
  refine ⟨
    { toFun := fun t => Λ * ComplexLorentzGroup.ofReal (γ t)
      continuous_toFun := continuous_const.mul (continuous_ofReal.comp γ.continuous_toFun)
      source' := by rw [γ.source, ofReal_one_eq, mul_one]
      target' := by rw [γ.target] },
    ?_⟩
  intro t
  exact permIndexSet_right_mul_ofReal (d := d) n σ hΛ (γ t)

/-- Double-coset generation criterion for connectedness of the permutation
forward-overlap index set. -/
private theorem isConnected_permForwardOverlapIndexSet_of_real_double_coset_generation
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (Λ0 : ComplexLorentzGroup d)
    (hΛ0 : Λ0 ∈ permForwardOverlapIndexSet (d := d) n σ)
    (hgen : ∀ Λ ∈ permForwardOverlapIndexSet (d := d) n σ,
      ∃ R1 R2 : RestrictedLorentzGroup d,
        Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2) :
    IsConnected (permForwardOverlapIndexSet (d := d) n σ) := by
  refine ⟨⟨Λ0, hΛ0⟩, ?_⟩
  refine isPreconnected_of_joinedIn_base hΛ0 ?_
  intro Λ hΛ
  rcases hgen Λ hΛ with ⟨R1, R2, rfl⟩
  have hright :
      JoinedIn (permForwardOverlapIndexSet (d := d) n σ)
        Λ0 (Λ0 * ComplexLorentzGroup.ofReal R2) :=
    permIndexSet_joined_right_ofReal (d := d) n σ hΛ0 R2
  have hmid_mem : Λ0 * ComplexLorentzGroup.ofReal R2 ∈
      permForwardOverlapIndexSet (d := d) n σ :=
    permIndexSet_right_mul_ofReal (d := d) n σ hΛ0 R2
  have hleft :
      JoinedIn (permForwardOverlapIndexSet (d := d) n σ)
        (Λ0 * ComplexLorentzGroup.ofReal R2)
        (ComplexLorentzGroup.ofReal R1 * (Λ0 * ComplexLorentzGroup.ofReal R2)) :=
    permIndexSet_joined_left_ofReal (d := d) n σ hmid_mem R1
  have hleft' :
      JoinedIn (permForwardOverlapIndexSet (d := d) n σ)
        (Λ0 * ComplexLorentzGroup.ofReal R2)
        (ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2) := by
    simpa [mul_assoc] using hleft
  exact hright.trans hleft'

/-- Each fixed-`Λ` permutation forward-overlap slice is convex. -/
private theorem permForwardOverlapSlice_convex
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    Convex ℝ (permForwardOverlapSlice (d := d) n σ Λ) := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab
  refine ⟨forwardTube_convex hw₁.1 hw₂.1 ha hb hab, ?_⟩
  have hperm_linear :
      permAct (d := d) σ (a • w₁ + b • w₂)
        = a • permAct (d := d) σ w₁ + b • permAct (d := d) σ w₂ := by
    ext k μ
    simp [permAct, Pi.smul_apply, Pi.add_apply]
  rw [hperm_linear]
  have hlin :
      complexLorentzAction Λ
          (a • permAct (d := d) σ w₁ + b • permAct (d := d) σ w₂) =
      a • complexLorentzAction Λ (permAct (d := d) σ w₁) +
      b • complexLorentzAction Λ (permAct (d := d) σ w₂) := by
    ext k μ
    simp only [complexLorentzAction, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    trans (↑a * ∑ ν, Λ.val μ ν * (permAct (d := d) σ w₁) k ν +
        ↑b * ∑ ν, Λ.val μ ν * (permAct (d := d) σ w₂) k ν)
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1
      ext ν
      ring
    · rfl
  rw [hlin]
  exact forwardTube_convex hw₁.2 hw₂.2 ha hb hab

/-- Each fixed-`Λ` permutation forward-overlap slice is preconnected. -/
private theorem permForwardOverlapSlice_isPreconnected
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    IsPreconnected (permForwardOverlapSlice (d := d) n σ Λ) :=
  (permForwardOverlapSlice_convex (d := d) n σ Λ).isPreconnected

/-- Connected-index reduction: connectedness of the nonempty-slice index set gives
refl-transitive overlap chains between any two indices. -/
private theorem reflTransGen_permSlice_overlap_of_indexConnected
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hidx_conn : IsConnected (permForwardOverlapIndexSet (d := d) n σ)) :
    ∀ (a b : {Λ : ComplexLorentzGroup d | permForwardOverlapIndexSet (d := d) n σ Λ}),
      Relation.ReflTransGen
        (fun x y : {Λ : ComplexLorentzGroup d |
            permForwardOverlapIndexSet (d := d) n σ Λ} =>
          ((permForwardOverlapSlice (d := d) n σ x.1) ∩
            (permForwardOverlapSlice (d := d) n σ y.1)).Nonempty)
        a b := by
  intro a b
  let R :
      {Λ : ComplexLorentzGroup d | permForwardOverlapIndexSet (d := d) n σ Λ} →
      {Λ : ComplexLorentzGroup d | permForwardOverlapIndexSet (d := d) n σ Λ} → Prop :=
    fun x y =>
      ((permForwardOverlapSlice (d := d) n σ x.1) ∩
        (permForwardOverlapSlice (d := d) n σ y.1)).Nonempty

  let U : Set {Λ : ComplexLorentzGroup d | permForwardOverlapIndexSet (d := d) n σ Λ} :=
    {x | Relation.ReflTransGen R a x}

  have hU_open : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hxU
    rcases x.2 with ⟨w, hwx⟩
    rcases permForwardOverlapSlice_nonempty_nhds (d := d) (n := n) σ hwx with
      ⟨V, hV_open, hxV, hV_sub⟩
    let W : Set {Λ : ComplexLorentzGroup d | permForwardOverlapIndexSet (d := d) n σ Λ} :=
      Subtype.val ⁻¹' V
    have hW_open : IsOpen W := hV_open.preimage continuous_subtype_val
    have hxW : x ∈ W := by simpa [W] using hxV
    refine Filter.mem_of_superset (hW_open.mem_nhds hxW) ?_
    intro y hyW
    have hyV : y.1 ∈ V := by simpa [W] using hyW
    have hwy : w ∈ permForwardOverlapSlice (d := d) n σ y.1 :=
      hV_sub y.1 hyV
    have hxy : R x y := ⟨w, hwx, hwy⟩
    exact Relation.ReflTransGen.tail hxU hxy

  have hU_closed : IsClosed U := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro x hxU
    rcases x.2 with ⟨w, hwx⟩
    rcases permForwardOverlapSlice_nonempty_nhds (d := d) (n := n) σ hwx with
      ⟨V, hV_open, hxV, hV_sub⟩
    let W : Set {Λ : ComplexLorentzGroup d | permForwardOverlapIndexSet (d := d) n σ Λ} :=
      Subtype.val ⁻¹' V
    have hW_open : IsOpen W := hV_open.preimage continuous_subtype_val
    have hxW : x ∈ W := by simpa [W] using hxV
    refine Filter.mem_of_superset (hW_open.mem_nhds hxW) ?_
    intro y hyW hyU
    have hyV : y.1 ∈ V := by simpa [W] using hyW
    have hwy : w ∈ permForwardOverlapSlice (d := d) n σ y.1 :=
      hV_sub y.1 hyV
    have hyx : R y x := ⟨w, hwy, hwx⟩
    have hx_inU : x ∈ U := Relation.ReflTransGen.tail hyU hyx
    exact hxU hx_inU

  have hU_nonempty : U.Nonempty := ⟨a, Relation.ReflTransGen.refl⟩

  haveI : ConnectedSpace {Λ : ComplexLorentzGroup d |
      permForwardOverlapIndexSet (d := d) n σ Λ} :=
    Subtype.connectedSpace hidx_conn

  have hU_eq : U = Set.univ := IsClopen.eq_univ ⟨hU_closed, hU_open⟩ hU_nonempty
  have hbU : b ∈ U := by simp [hU_eq]
  exact hbU

/-- If the permutation nonempty-slice index set is connected, then the full
permutation forward-overlap set is connected. -/
private theorem isConnected_permForwardOverlapSet_of_indexConnected
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hidx_conn : IsConnected (permForwardOverlapIndexSet (d := d) n σ))
    (hnonempty : (permForwardOverlapSet (d := d) n σ).Nonempty) :
    IsConnected (permForwardOverlapSet (d := d) n σ) := by
  let t : Set (ComplexLorentzGroup d) :=
    permForwardOverlapIndexSet (d := d) n σ

  have hpre_union_subtype :
      IsPreconnected
        (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
          permForwardOverlapSlice (d := d) n σ x.1) := by
    apply IsPreconnected.iUnion_of_reflTransGen
    · intro x
      exact (permForwardOverlapSlice_convex (d := d) n σ x.1).isPreconnected
    · intro x y
      exact reflTransGen_permSlice_overlap_of_indexConnected (d := d) (n := n) σ
        hidx_conn x y

  have h_union_eq_all :
      (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
        permForwardOverlapSlice (d := d) n σ x.1)
        = ⋃ Λ : ComplexLorentzGroup d,
            permForwardOverlapSlice (d := d) n σ Λ := by
    ext w
    constructor
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨x, hx⟩
      exact Set.mem_iUnion.mpr ⟨x.1, hx⟩
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨Λ, hΛ⟩
      have hΛt : t Λ := ⟨w, hΛ⟩
      exact Set.mem_iUnion.mpr ⟨⟨Λ, hΛt⟩, hΛ⟩

  have hset_eq :
      permForwardOverlapSet (d := d) n σ =
        (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
          permForwardOverlapSlice (d := d) n σ x.1) := by
    calc
      permForwardOverlapSet (d := d) n σ
          = ⋃ Λ : ComplexLorentzGroup d,
              permForwardOverlapSlice (d := d) n σ Λ :=
            permForwardOverlapSet_eq_iUnion_slices (d := d) n σ
      _ = (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
            permForwardOverlapSlice (d := d) n σ x.1) :=
          h_union_eq_all.symm

  refine ⟨hnonempty, ?_⟩
  simpa [hset_eq] using hpre_union_subtype

/-- Wrapper reduction: real double-coset generation on the permutation index set
implies connectedness of the permutation forward-overlap set. -/
private theorem isConnected_permForwardOverlapSet_of_real_double_coset_generation [NeZero d]
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (Λ0 : ComplexLorentzGroup d)
    (hΛ0 : Λ0 ∈ permForwardOverlapIndexSet (d := d) n σ)
    (hgen : ∀ Λ ∈ permForwardOverlapIndexSet (d := d) n σ,
      ∃ R1 R2 : RestrictedLorentzGroup d,
        Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2)
    (hnonempty : (permForwardOverlapSet (d := d) n σ).Nonempty) :
    IsConnected (permForwardOverlapSet (d := d) n σ) := by
  have hidx_conn :
      IsConnected (permForwardOverlapIndexSet (d := d) n σ) :=
    isConnected_permForwardOverlapIndexSet_of_real_double_coset_generation
      (d := d) n σ Λ0 hΛ0 hgen
  exact isConnected_permForwardOverlapSet_of_indexConnected (d := d) n σ hidx_conn hnonempty

/-- Any element of the permutation forward-overlap index set provides
nonemptiness of the corresponding forward-overlap set. -/
private theorem nonempty_permForwardOverlapSet_of_indexSet_mem
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {Λ : ComplexLorentzGroup d}
    (hΛ : Λ ∈ permForwardOverlapIndexSet (d := d) n σ) :
    (permForwardOverlapSet (d := d) n σ).Nonempty := by
  rcases hΛ with ⟨w, hw⟩
  refine ⟨w, ⟨hw.1, ?_⟩⟩
  refine Set.mem_iUnion.mpr ?_
  refine ⟨Λ⁻¹, complexLorentzAction Λ (permAct (d := d) σ w), hw.2, ?_⟩
  simp [complexLorentzAction_inv]

/-- Nonemptiness of permutation forward overlap from the Jost-to-ET bridge. -/
private theorem nonempty_permForwardOverlapSet_of_jostSetET
    (n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hJostET : ∀ x : Fin n → Fin (d + 1) → ℝ, x ∈ JostSet d n →
      realEmbed x ∈ ExtendedTube d n) :
    (permForwardOverlapSet (d := d) n σ).Nonempty := by
  rcases jostSet_nonempty hn hd with ⟨x, hxJ⟩
  have hxET : realEmbed x ∈ ExtendedTube d n := hJostET x hxJ
  rcases Set.mem_iUnion.mp hxET with ⟨Λ, w, hwFT, hx_eq⟩
  have hσxJ : (fun k => x (σ k)) ∈ JostSet d n :=
    jostSet_permutation_invariant σ hxJ
  have hσxET : realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n :=
    hJostET (fun k => x (σ k)) hσxJ
  have hσx_as_action :
      realEmbed (fun k => x (σ k)) = complexLorentzAction Λ (permAct (d := d) σ w) := by
    calc
      realEmbed (fun k => x (σ k))
          = permAct (d := d) σ (realEmbed x) := by rfl
      _ = permAct (d := d) σ (complexLorentzAction Λ w) := by simp [hx_eq]
      _ = complexLorentzAction Λ (permAct (d := d) σ w) := by
            exact (lorentz_perm_commute Λ w σ).symm
  have hΛσw_ET : complexLorentzAction Λ (permAct (d := d) σ w) ∈ ExtendedTube d n := by
    simpa [hσx_as_action] using hσxET
  have hσw_ET : permAct (d := d) σ w ∈ ExtendedTube d n := by
    have := complexLorentzAction_mem_extendedTube n Λ⁻¹ hΛσw_ET
    simpa [complexLorentzAction_inv] using this
  exact ⟨w, ⟨hwFT, hσw_ET⟩⟩

/-- Nonemptiness of permutation forward overlap from a local Jost witness package. -/
private theorem nonempty_permForwardOverlapSet_of_jostWitness
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n) :
    (permForwardOverlapSet (d := d) n σ).Nonempty := by
  rcases hJostWitness with ⟨x, _hxJ, hxET, hσxET⟩
  rcases Set.mem_iUnion.mp hxET with ⟨Λ, w, hwFT, hx_eq⟩
  have hσx_as_action :
      realEmbed (fun k => x (σ k)) = complexLorentzAction Λ (permAct (d := d) σ w) := by
    calc
      realEmbed (fun k => x (σ k))
          = permAct (d := d) σ (realEmbed x) := by rfl
      _ = permAct (d := d) σ (complexLorentzAction Λ w) := by simp [hx_eq]
      _ = complexLorentzAction Λ (permAct (d := d) σ w) := by
            exact (lorentz_perm_commute Λ w σ).symm
  have hΛσw_ET : complexLorentzAction Λ (permAct (d := d) σ w) ∈ ExtendedTube d n := by
    simpa [hσx_as_action] using hσxET
  have hσw_ET : permAct (d := d) σ w ∈ ExtendedTube d n := by
    have := complexLorentzAction_mem_extendedTube n Λ⁻¹ hΛσw_ET
    simpa [complexLorentzAction_inv] using this
  exact ⟨w, ⟨hwFT, hσw_ET⟩⟩

/-- Basepoint existence in the permutation forward-overlap index set from a
local Jost witness package. -/
private theorem exists_permForwardOverlapIndexSet_basepoint_of_jostWitness
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n) :
    ∃ Λ0, Λ0 ∈ permForwardOverlapIndexSet (d := d) n σ := by
  have hnonempty : (permForwardOverlapSet (d := d) n σ).Nonempty :=
    nonempty_permForwardOverlapSet_of_jostWitness (d := d) n σ hJostWitness
  exact nonempty_permForwardOverlapIndexSet_of_forwardOverlapNonempty
    (d := d) n σ hnonempty

/-- Basepoint existence in the permutation forward-overlap index set, derived
from the Jost-to-ET bridge. -/
private theorem exists_permForwardOverlapIndexSet_basepoint_of_jostSetET
    (n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hJostET : ∀ x : Fin n → Fin (d + 1) → ℝ, x ∈ JostSet d n →
      realEmbed x ∈ ExtendedTube d n) :
    ∃ Λ0, Λ0 ∈ permForwardOverlapIndexSet (d := d) n σ := by
  have hnonempty : (permForwardOverlapSet (d := d) n σ).Nonempty :=
    nonempty_permForwardOverlapSet_of_jostSetET (d := d) n hd hn σ hJostET
  exact nonempty_permForwardOverlapIndexSet_of_forwardOverlapNonempty
    (d := d) n σ hnonempty

/-- The permutation overlap domain is the Lorentz-action image of the corresponding
forward-overlap slice. -/
private theorem permExtendedOverlap_eq_action_image_forwardOverlap
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permExtendedOverlapSet (d := d) n σ =
      (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) ''
      (Set.univ ×ˢ permForwardOverlapSet (d := d) n σ) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzET, hσzET⟩
    rcases Set.mem_iUnion.mp hzET with ⟨Λ, w, hwFT, hz_eq⟩
    have hσz_as_action :
        permAct (d := d) σ z = complexLorentzAction Λ (permAct (d := d) σ w) := by
      calc
        permAct (d := d) σ z
            = permAct (d := d) σ (complexLorentzAction Λ w) := by simp [hz_eq]
        _ = complexLorentzAction Λ (permAct (d := d) σ w) := by
              exact (lorentz_perm_commute Λ w σ).symm
    have hΛσw_ET : complexLorentzAction Λ (permAct (d := d) σ w) ∈ ExtendedTube d n := by
      simpa [hσz_as_action] using hσzET
    have hσw_ET : permAct (d := d) σ w ∈ ExtendedTube d n := by
      have := complexLorentzAction_mem_extendedTube n Λ⁻¹ hΛσw_ET
      simpa [complexLorentzAction_inv] using this
    refine ⟨⟨Λ, w⟩, ⟨trivial, ⟨hwFT, hσw_ET⟩⟩, ?_⟩
    simp [hz_eq]
  · rintro ⟨⟨Λ, w⟩, ⟨_, hwFT, hσw_ET⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact complexLorentzAction_mem_extendedTube n Λ
        (forwardTube_subset_extendedTube hwFT)
    · have hσ_action :
          permAct (d := d) σ (complexLorentzAction Λ w) =
            complexLorentzAction Λ (permAct (d := d) σ w) := by
        exact lorentz_perm_commute Λ w σ
      have hσ_ET : permAct (d := d) σ (complexLorentzAction Λ w) ∈ ExtendedTube d n := by
        simpa [hσ_action] using
          complexLorentzAction_mem_extendedTube n Λ hσw_ET
      exact hσ_ET

/-- Reduction: connectedness of the permutation forward-overlap slice implies
connectedness of the full overlap domain in the extended tube. -/
private theorem isConnected_permExtendedOverlap_of_forwardOverlapConnected
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ)) :
    IsConnected (permExtendedOverlapSet (d := d) n σ) := by
  haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
    pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
  have hprod_conn :
      IsConnected
        ((Set.univ : Set (ComplexLorentzGroup d)) ×ˢ
          permForwardOverlapSet (d := d) n σ) :=
    isConnected_univ.prod hFwd_conn
  have hcont : Continuous
      (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    simp only [complexLorentzAction]
    apply continuous_finset_sum
    intro ν _
    apply Continuous.mul
    · have hval : Continuous
          (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) => p.1.val) :=
        ComplexLorentzGroup.continuous_val.comp continuous_fst
      have hrow :
          Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M μ) :=
        continuous_apply μ
      have hentry : Continuous (fun r : Fin (d + 1) → ℂ => r ν) := continuous_apply ν
      exact hentry.comp (hrow.comp hval)
    · exact (continuous_apply ν).comp ((continuous_apply k).comp continuous_snd)
  have himage_conn :
      IsConnected
        ((fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
          complexLorentzAction p.1 p.2) ''
        ((Set.univ : Set (ComplexLorentzGroup d)) ×ˢ
          permForwardOverlapSet (d := d) n σ)) :=
    hprod_conn.image _ hcont.continuousOn
  simpa [permExtendedOverlap_eq_action_image_forwardOverlap (d := d) n σ] using himage_conn

/-- Real-boundary permutation invariance from local commutativity on adjacent swaps. -/
private theorem F_real_perm_invariance_on_jost
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (x : Fin n → Fin (d + 1) → ℝ)
    (hxJ : x ∈ JostSet d n) :
    ∀ (σ : Equiv.Perm (Fin n)),
      F (realEmbed (fun k => x (σ k))) = F (realEmbed x) := by
  have hx_pair :
      ∀ i j : Fin n, i ≠ j →
        IsSpacelike d (fun μ => x i μ - x j μ) := hxJ.2
  refine Fin.Perm.adjSwap_induction_right (n := n)
    (motive := fun σ =>
      F (realEmbed (fun k => x (σ k))) = F (realEmbed x))
    ?base ?step
  · simp
  · intro σ i hi ih
    let xσ : Fin n → Fin (d + 1) → ℝ := fun k => x (σ k)
    have hneq_idx : (σ ⟨i.val + 1, hi⟩) ≠ σ i := by
      intro h
      have hlt : i < (⟨i.val + 1, hi⟩ : Fin n) := by
        exact Fin.lt_def.2 (Nat.lt_succ_self i.val)
      exact (ne_of_lt hlt) (σ.injective h).symm
    have hsp :
        ∑ μ, minkowskiSignature d μ *
          (xσ ⟨i.val + 1, hi⟩ μ - xσ i μ) ^ 2 > 0 := by
      simpa [xσ, IsSpacelike] using
        hx_pair (σ ⟨i.val + 1, hi⟩) (σ i) hneq_idx
    have hswap :
        F (realEmbed (fun k => xσ (Equiv.swap i ⟨i.val + 1, hi⟩ k))) =
          F (realEmbed xσ) := by
      simpa [xσ] using hF_local i hi xσ hsp
    calc
      F (realEmbed (fun k => x ((σ * Equiv.swap i ⟨i.val + 1, hi⟩) k)))
          = F (realEmbed (fun k => xσ (Equiv.swap i ⟨i.val + 1, hi⟩ k))) := by
              simp [xσ, Equiv.Perm.mul_apply]
      _ = F (realEmbed xσ) := hswap
      _ = F (realEmbed x) := ih

/-- Real Jost-point equality transport for `extendF` under permutation action. -/
private theorem extendF_perm_eq_on_realJost
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (x : Fin n → Fin (d + 1) → ℝ)
    (hxJ : x ∈ JostSet d n)
    (hxET : realEmbed x ∈ ExtendedTube d n)
    (hσxET : realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n) :
    extendF F (fun k => (realEmbed x) (σ k)) = extendF F (realEmbed x) := by
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hz hΛz
  have hbdx : extendF F (realEmbed x) = F (realEmbed x) :=
    extendF_eq_boundary_value_ET n F hF_holo hF_cinv hF_bv x hxET
  have hbdσ : extendF F (realEmbed (fun k => x (σ k))) =
      F (realEmbed (fun k => x (σ k))) :=
    extendF_eq_boundary_value_ET n F hF_holo hF_cinv hF_bv
      (fun k => x (σ k)) hσxET
  have hFperm :
      F (realEmbed (fun k => x (σ k))) = F (realEmbed x) :=
    F_real_perm_invariance_on_jost (d := d) n F hF_local x hxJ σ
  calc
    extendF F (fun k => (realEmbed x) (σ k))
        = extendF F (realEmbed (fun k => x (σ k))) := by rfl
    _ = F (realEmbed (fun k => x (σ k))) := hbdσ
    _ = F (realEmbed x) := hFperm
    _ = extendF F (realEmbed x) := hbdx.symm

/-- Local-witness variant of the permutation-overlap identity-theorem reduction:
connected forward-overlap plus one real Jost witness in the ET overlap suffices. -/
private theorem extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n)
    (hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  let D : Set (Fin n → Fin (d + 1) → ℂ) := permExtendedOverlapSet (d := d) n σ
  have hD_open : IsOpen D := by
    have hperm_cont : Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ => permAct (d := d) σ z) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (σ k))))
    exact isOpen_extendedTube.inter (isOpen_extendedTube.preimage hperm_cont)
  have hD_conn : IsConnected D := by
    simpa [D] using
      isConnected_permExtendedOverlap_of_forwardOverlapConnected (d := d) n σ hFwd_conn
  have hD_sub_ET : D ⊆ ExtendedTube d n := by
    intro z hz
    exact hz.1
  have hD_sub_permET : D ⊆ {z | permAct (d := d) σ z ∈ ExtendedTube d n} := by
    intro z hz
    exact hz.2
  let V : Set (Fin n → Fin (d + 1) → ℝ) := {x | x ∈ JostSet d n ∧ realEmbed x ∈ D}
  have hV_open : IsOpen V := by
    have hrealEmbed_cont :
        Continuous (realEmbed : (Fin n → Fin (d + 1) → ℝ) → (Fin n → Fin (d + 1) → ℂ)) := by
      apply continuous_pi
      intro k
      apply continuous_pi
      intro μ
      exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply k))
    exact isOpen_jostSet.inter (hD_open.preimage hrealEmbed_cont)
  have hV_ne : V.Nonempty := by
    rcases hJostWitness with ⟨x0, hx0J, hx0ET, hσx0ET⟩
    refine ⟨x0, ?_⟩
    refine ⟨hx0J, ?_⟩
    exact ⟨hx0ET, by simpa [D, permAct, realEmbed] using hσx0ET⟩
  have hV_sub_D : ∀ x ∈ V, realEmbed x ∈ D := by
    intro x hxV
    exact hxV.2
  have hV_eq : ∀ x ∈ V,
      extendF F (fun k => (realEmbed x) (σ k)) = extendF F (realEmbed x) := by
    intro x hxV
    have hxJ : x ∈ JostSet d n := hxV.1
    have hxD : realEmbed x ∈ D := hxV.2
    have hxET : realEmbed x ∈ ExtendedTube d n := hxD.1
    have hσxET : realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n := by
      simpa [D, permAct, realEmbed] using hxD.2
    exact extendF_perm_eq_on_realJost (d := d) n F hF_holo hF_lorentz
      hF_bv hF_local σ x hxJ hxET hσxET
  intro z hz hσz
  have hzD : z ∈ D := ⟨hz, hσz⟩
  exact extendF_perm_eq_on_connectedDomain_of_realOpen n F hF_holo hF_lorentz
    σ D hD_open hD_conn hD_sub_ET hD_sub_permET V hV_open hV_ne hV_sub_D hV_eq z hzD

/-- Index-connectedness plus a local Jost witness package yields permutation
overlap invariance of `extendF`. -/
private theorem extendF_perm_overlap_of_jostWitness_and_indexConnected
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n)
    (hidx_conn : IsConnected (permForwardOverlapIndexSet (d := d) n σ)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hnonempty : (permForwardOverlapSet (d := d) n σ).Nonempty :=
    nonempty_permForwardOverlapSet_of_jostWitness (d := d) n σ hJostWitness
  have hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ) :=
    isConnected_permForwardOverlapSet_of_indexConnected (d := d) n σ hidx_conn hnonempty
  exact extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected
    (d := d) n F hF_holo hF_lorentz hF_bv hF_local σ hJostWitness hFwd_conn

/-- If a (strong) `JostSet`-to-ET bridge is available and the
permutation forward-overlap slice is connected, then `extendF` is permutation
invariant on the full ET-overlap domain. -/
private theorem extendF_perm_overlap_of_jostSet_and_forwardOverlapConnected
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (hd : 1 ≤ d) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hJostET : ∀ x : Fin n → Fin (d + 1) → ℝ, x ∈ JostSet d n →
      realEmbed x ∈ ExtendedTube d n)
    (hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n := by
    rcases jostSet_nonempty hn hd with ⟨x, hxJ⟩
    have hxET : realEmbed x ∈ ExtendedTube d n := hJostET x hxJ
    have hσxJ : (fun k => x (σ k)) ∈ JostSet d n :=
      jostSet_permutation_invariant σ hxJ
    have hσxET : realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n :=
      hJostET (fun k => x (σ k)) hσxJ
    exact ⟨x, hxJ, hxET, hσxET⟩
  exact extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected
    (d := d) n F hF_holo hF_lorentz hF_bv hF_local σ hJostWitness hFwd_conn

-- NOTE: the hypothesis
-- `∀ x ∈ JostSet d n, realEmbed x ∈ ExtendedTube d n`
-- is known to be false in general (`test/jostset_et_counterexample_test.lean`).
-- This wrapper remains as a conditional reduction, but the active proof branch
-- below must avoid relying on this hypothesis globally.
/-- Wrapper reduction: if the permutation forward-overlap index set is connected
via real double-coset generation and a (strong) Jost-to-ET bridge holds, then
`extendF` is permutation-invariant on the full ET overlap domain. -/
private theorem extendF_perm_overlap_of_jostWitness_and_real_double_coset_generation
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n)
    (hgenPack : ∃ Λ0, Λ0 ∈ permForwardOverlapIndexSet (d := d) n σ ∧
      (∀ Λ ∈ permForwardOverlapIndexSet (d := d) n σ,
        ∃ R1 R2 : RestrictedLorentzGroup d,
          Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  rcases hgenPack with ⟨Λ0, hΛ0, hgen⟩
  have hidx_conn :
      IsConnected (permForwardOverlapIndexSet (d := d) n σ) :=
    isConnected_permForwardOverlapIndexSet_of_real_double_coset_generation
      (d := d) n σ Λ0 hΛ0 hgen
  exact extendF_perm_overlap_of_jostWitness_and_indexConnected
    (d := d) n F hF_holo hF_lorentz hF_bv hF_local σ hJostWitness hidx_conn

/-- Curried form of
`extendF_perm_overlap_of_jostWitness_and_real_double_coset_generation`. -/
private theorem extendF_perm_overlap_of_jostWitness_and_real_double_coset_generation'
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n)
    (Λ0 : ComplexLorentzGroup d)
    (hΛ0 : Λ0 ∈ permForwardOverlapIndexSet (d := d) n σ)
    (hgen : ∀ Λ ∈ permForwardOverlapIndexSet (d := d) n σ,
      ∃ R1 R2 : RestrictedLorentzGroup d,
        Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  exact extendF_perm_overlap_of_jostWitness_and_real_double_coset_generation
    (d := d) n F hF_holo hF_lorentz hF_bv hF_local σ hJostWitness
    ⟨Λ0, hΛ0, hgen⟩

/-- Wrapper reduction: if the permutation forward-overlap index set is connected
via real double-coset generation and a (strong) Jost-to-ET bridge holds, then
`extendF` is permutation-invariant on the full ET overlap domain. -/
private theorem extendF_perm_overlap_of_jostSet_and_real_double_coset_generation
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (hd : 1 ≤ d) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hJostET : ∀ x : Fin n → Fin (d + 1) → ℝ, x ∈ JostSet d n →
      realEmbed x ∈ ExtendedTube d n)
    (hgenPack : ∃ Λ0, Λ0 ∈ permForwardOverlapIndexSet (d := d) n σ ∧
      (∀ Λ ∈ permForwardOverlapIndexSet (d := d) n σ,
        ∃ R1 R2 : RestrictedLorentzGroup d,
          Λ = ComplexLorentzGroup.ofReal R1 * Λ0 * ComplexLorentzGroup.ofReal R2)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n := by
    rcases jostSet_nonempty hn hd with ⟨x, hxJ⟩
    have hxET : realEmbed x ∈ ExtendedTube d n := hJostET x hxJ
    have hσxJ : (fun k => x (σ k)) ∈ JostSet d n :=
      jostSet_permutation_invariant σ hxJ
    have hσxET : realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n :=
      hJostET (fun k => x (σ k)) hσxJ
    exact ⟨x, hxJ, hxET, hσxET⟩
  exact extendF_perm_overlap_of_jostWitness_and_real_double_coset_generation
    (d := d) n F hF_holo hF_lorentz hF_bv hF_local σ hJostWitness hgenPack

/-- Packaging lemma: a local Jost witness together with connectedness of the
seed set is enough for ET-overlap permutation invariance of `extendF`. -/
private theorem extendF_perm_overlap_of_jostWitness_and_seedConnected
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n)
    (hseed_conn : IsConnected (permOrbitSeedSet (d := d) n σ)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ) :=
    (isConnected_permOrbitSeedSet_iff_permForwardOverlapSet (d := d) n σ).1 hseed_conn
  exact extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected
    (d := d) n F hF_holo hF_lorentz hF_bv hF_local σ hJostWitness hFwd_conn

/-- Specialized d≥2 package: once seed connectedness is available, the
nontrivial `hExtPerm` branch closes immediately. -/
private theorem extendF_perm_overlap_dge2_of_seedConnected
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (hd2 : 2 ≤ d)
    (σ : Equiv.Perm (Fin n))
    (hseed_conn : IsConnected (permOrbitSeedSet (d := d) n σ)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hJostWitness :
      ∃ x : Fin n → Fin (d + 1) → ℝ,
        x ∈ JostSet d n ∧
        realEmbed x ∈ ExtendedTube d n ∧
        realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n := by
    simpa using
      JostWitnessGeneralSigma.jostWitness_exists (d := d) (n := n) hd2 σ
  exact extendF_perm_overlap_of_jostWitness_and_seedConnected
    (d := d) n F hF_holo hF_lorentz hF_bv hF_local σ hJostWitness hseed_conn

/-- d=1 connective chain packaging: seed connectedness plus nonemptiness gives
connected permutation forward overlap. -/
private theorem isConnected_permForwardOverlapSet_d1_of_seedConnected_and_nonempty
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hseed_conn : IsConnected (permOrbitSeedSet (d := 1) n σ))
    (hnonempty : (permForwardOverlapSet (d := 1) n σ).Nonempty) :
    IsConnected (permForwardOverlapSet (d := 1) n σ) := by
  have hidx_conn :
      IsConnected (permForwardOverlapIndexSet (d := 1) n σ) :=
    isConnected_permForwardOverlapIndexSet_d1_of_seedConnected (n := n) σ hseed_conn
  exact isConnected_permForwardOverlapSet_of_indexConnected
    (d := 1) n σ hidx_conn hnonempty

/-- Build a holomorphic extension domain for a fixed permutation `σ` from
    the corresponding permutation-invariance hypothesis.

    If `hperm` says
      `F (Γ·(σ·w)) = F(w)` whenever `w ∈ FT` and `Γ·(σ·w) ∈ FT`,
    then on `U_σ := FT ∪ {z | σ·z ∈ FT}` the piecewise function
      `F_σ z := if z ∈ FT then F z else F (σ·z)`
    is holomorphic, agrees with `F` on `FT`, agrees with `F∘σ` on `σFT`,
    and is complex-Lorentz invariant on `U_σ`.

    This packages the exact extension data needed in EOW chain arguments. -/
private theorem permutation_extension_from_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hperm : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (σ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (σ k))) = F w) :
    ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := by
  set σFT : Set (Fin n → Fin (d + 1) → ℂ) := {z | (fun k => z (σ k)) ∈ ForwardTube d n}
  set U_σ : Set (Fin n → Fin (d + 1) → ℂ) := ForwardTube d n ∪ σFT
  set F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => if z ∈ ForwardTube d n then F z else F (fun k => z (σ k))
  have hFσ_eq_on_σFT :
      ∀ z, z ∈ σFT → F_σ z = F (fun k => z (σ k)) := by
    intro z hzσ
    by_cases hzFT : z ∈ ForwardTube d n
    · have h1 : F (fun k => z (σ k)) = F z := by
        simpa [complexLorentzAction_one] using
          (hperm z hzFT 1 (by
            simpa [σFT, complexLorentzAction_one] using hzσ))
      simp [F_σ, hzFT, h1]
    · simp [F_σ, hzFT]
  refine ⟨U_σ, F_σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_forwardTube.union (isOpen_permutedForwardTube σ)
  · intro z hz
    exact Or.inl hz
  · intro z hz
    exact Or.inr hz
  · intro z hzU
    rcases hzU with hzFT | hzσ
    · have hFz : DifferentiableAt ℂ F z :=
        (hF_holo z hzFT).differentiableAt (isOpen_forwardTube.mem_nhds hzFT)
      have h_eq : F_σ =ᶠ[𝓝 z] F := by
        filter_upwards [isOpen_forwardTube.mem_nhds hzFT] with w hw
        simp [F_σ, hw]
      exact (h_eq.differentiableAt_iff.mpr hFz).differentiableWithinAt
    · have hFσz : DifferentiableAt ℂ F (fun k => z (σ k)) :=
        (hF_holo _ (by simpa [σFT] using hzσ)).differentiableAt
          (isOpen_forwardTube.mem_nhds (by simpa [σFT] using hzσ))
      have hperm_diff : Differentiable ℂ
          (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (σ k)) :=
        differentiable_pi.mpr (fun k => differentiable_apply (σ k))
      have hcomp : DifferentiableAt ℂ (fun w => F (fun k => w (σ k))) z :=
        DifferentiableAt.comp z hFσz (hperm_diff z)
      have h_eq : F_σ =ᶠ[𝓝 z] (fun w => F (fun k => w (σ k))) := by
        filter_upwards [(isOpen_permutedForwardTube σ).mem_nhds hzσ] with w hw
        exact hFσ_eq_on_σFT w hw
      exact (h_eq.differentiableAt_iff.mpr hcomp).differentiableWithinAt
  · intro z hz
    exact if_pos hz.2
  · intro Λ z hzU hΛzU
    rcases hzU with hzFT | hzσ
    · rcases hΛzU with hΛzFT | hΛzσ
      · simp [F_σ, hzFT, hΛzFT]
        exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hzFT hΛzFT
      · have hstep :
            F (complexLorentzAction Λ (fun k => z (σ k))) = F z :=
          hperm z hzFT Λ (by
            simpa [σFT, lorentz_perm_commute] using hΛzσ)
        have hlhs : F_σ (complexLorentzAction Λ z) =
            F (complexLorentzAction Λ (fun k => z (σ k))) := by
          exact (hFσ_eq_on_σFT (complexLorentzAction Λ z) hΛzσ).trans (by
            simp [lorentz_perm_commute])
        simp [F_σ, hzFT]
        exact hlhs.trans hstep
    · rcases hΛzU with hΛzFT | hΛzσ
      · have hzσFT : (fun k => z (σ k)) ∈ ForwardTube d n := by
          simpa [σFT] using hzσ
        have hrewrite : complexLorentzAction Λ⁻¹
            (fun k => (complexLorentzAction Λ z) (σ k)) =
            (fun k => z (σ k)) := by
          calc
            complexLorentzAction Λ⁻¹
              (fun k => (complexLorentzAction Λ z) (σ k))
                = complexLorentzAction Λ⁻¹
                    (complexLorentzAction Λ (fun k => z (σ k))) := by
                      simp [lorentz_perm_commute]
            _ = (fun k => z (σ k)) := by
                  rw [complexLorentzAction_inv]
        have hcond :
            complexLorentzAction Λ⁻¹
              (fun k => (complexLorentzAction Λ z) (σ k)) ∈ ForwardTube d n := by
          simpa [hrewrite] using hzσFT
        have hstep :
            F (complexLorentzAction Λ⁻¹
              (fun k => (complexLorentzAction Λ z) (σ k))) =
            F (complexLorentzAction Λ z) :=
          hperm (complexLorentzAction Λ z) hΛzFT Λ⁻¹ hcond
        have hright : F_σ z = F (fun k => z (σ k)) := hFσ_eq_on_σFT z hzσ
        have hleft : F_σ (complexLorentzAction Λ z) = F (complexLorentzAction Λ z) := by
          simp [F_σ, hΛzFT]
        have hstep' : F (fun k => z (σ k)) = F (complexLorentzAction Λ z) := by
          simpa [hrewrite] using hstep
        exact hleft.trans (hstep'.symm.trans hright.symm)
      · have hzσFT : (fun k => z (σ k)) ∈ ForwardTube d n := by
          simpa [σFT] using hzσ
        have hΛzσFT : (fun k => (complexLorentzAction Λ z) (σ k)) ∈ ForwardTube d n := by
          simpa [σFT] using hΛzσ
        have hstep : F (complexLorentzAction Λ (fun k => z (σ k))) =
            F (fun k => z (σ k)) :=
          complex_lorentz_invariance n F hF_holo hF_lorentz Λ
            (fun k => z (σ k)) hzσFT (by
              simpa [lorentz_perm_commute] using hΛzσFT)
        have hleft : F_σ (complexLorentzAction Λ z) =
            F (complexLorentzAction Λ (fun k => z (σ k))) := by
          exact (hFσ_eq_on_σFT (complexLorentzAction Λ z) hΛzσ).trans (by
            simp [lorentz_perm_commute])
        have hright : F_σ z = F (fun k => z (σ k)) := hFσ_eq_on_σFT z hzσ
        exact hleft.trans (hstep.trans hright.symm)
  · intro z hz
    exact hFσ_eq_on_σFT z hz.2

/-- If `extendF` is permutation-invariant on the extended-tube overlap for `τ`,
    then `F` satisfies the corresponding forward-tube permutation invariance. -/
private theorem permutation_invariance_from_extendF_on_extendedTube (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (τ : Equiv.Perm (Fin n))
    (hExtPerm :
      ∀ (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        (fun k => z (τ k)) ∈ ExtendedTube d n →
        extendF F (fun k => z (τ k)) = extendF F z) :
    ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  intro w hw Γ hΓτw
  set z : Fin n → Fin (d + 1) → ℂ := complexLorentzAction Γ w
  have hcomm : complexLorentzAction Γ (fun k => w (τ k)) = fun k => z (τ k) := by
    simpa [z] using (lorentz_perm_commute Γ w τ)
  have hτz_FT : (fun k => z (τ k)) ∈ ForwardTube d n := by
    simpa [hcomm] using hΓτw
  have hz_ET : z ∈ ExtendedTube d n := by
    refine Set.mem_iUnion.mpr ?_
    refine ⟨Γ, ?_⟩
    exact ⟨w, hw, by simp [z]⟩
  have hτz_ET : (fun k => z (τ k)) ∈ ExtendedTube d n :=
    forwardTube_subset_extendedTube hτz_FT
  have hperm_ext : extendF F (fun k => z (τ k)) = extendF F z :=
    hExtPerm z hz_ET hτz_ET
  have hLorentz_ext : extendF F z = extendF F w := by
    simpa [z] using
      (extendF_complex_lorentz_invariant n F hF_holo hF_real_inv Γ w
        (forwardTube_subset_extendedTube hw))
  have hleft : extendF F (fun k => z (τ k)) = F (fun k => z (τ k)) :=
    extendF_eq_on_forwardTube n F hF_holo hF_real_inv _ hτz_FT
  have hright : extendF F w = F w :=
    extendF_eq_on_forwardTube n F hF_holo hF_real_inv w hw
  calc
    F (complexLorentzAction Γ (fun k => w (τ k)))
        = F (fun k => z (τ k)) := by simp [hcomm]
    _ = extendF F (fun k => z (τ k)) := hleft.symm
    _ = extendF F z := hperm_ext
    _ = extendF F w := hLorentz_ext
    _ = F w := hright

/-- If `z = Λ·w` with `w ∈ FT`, then `extendF F z = F w`.
    This packages the witness-based unfolding used in overlap arguments. -/
private theorem extendF_eq_of_explicit_witness (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (z w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n)
    (Λ : ComplexLorentzGroup d)
    (hz : z = complexLorentzAction Λ w) :
    extendF F z = F w := by
  simp only [extendF]
  have hex : ∃ (w' : Fin n → Fin (d + 1) → ℂ),
      w' ∈ ForwardTube d n ∧ ∃ (Λ' : ComplexLorentzGroup d), z = complexLorentzAction Λ' w' :=
    ⟨w, hw, Λ, hz⟩
  rw [dif_pos hex]
  have hspec := hex.choose_spec
  have hwc : hex.choose ∈ ForwardTube d n := hspec.1
  rcases hspec.2 with ⟨Λc, hzc⟩
  have h_eq : complexLorentzAction Λc hex.choose = complexLorentzAction Λ w := by
    exact hzc.symm.trans hz
  exact extendF_preimage_eq n F hF_holo hF_real_inv hwc hw h_eq

/-- Forward-tube permutation invariance implies permutation invariance of `extendF`
    on the extended-tube overlap for the same permutation. -/
private theorem extendF_perm_overlap_from_forwardTube_permInvariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (τ : Equiv.Perm (Fin n))
    (hperm : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (τ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (τ k)) = extendF F z := by
  intro z hz hzτ
  rcases Set.mem_iUnion.mp hz with ⟨Γ, w, hw, rfl⟩
  have hcomm : complexLorentzAction Γ (fun k => w (τ k)) =
      (fun k => (complexLorentzAction Γ w) (τ k)) := by
    ext k μ
    simp [complexLorentzAction]
  rcases Set.mem_iUnion.mp hzτ with ⟨Δ, u, hu, hu_eq⟩
  have hu_eq' : complexLorentzAction Γ (fun k => w (τ k)) =
      complexLorentzAction Δ u := by
    simpa [hcomm] using hu_eq
  have hcond : complexLorentzAction (Δ⁻¹ * Γ) (fun k => w (τ k)) ∈ ForwardTube d n := by
    rw [complexLorentzAction_mul, hu_eq', complexLorentzAction_inv]
    exact hu
  have hperm_w : F (complexLorentzAction (Δ⁻¹ * Γ) (fun k => w (τ k))) = F w :=
    hperm w hw (Δ⁻¹ * Γ) hcond
  have hu_eq_w : F u = F w := by
    have : complexLorentzAction (Δ⁻¹ * Γ) (fun k => w (τ k)) = u := by
      rw [complexLorentzAction_mul, hu_eq', complexLorentzAction_inv]
    simpa [this] using hperm_w
  have hleft : extendF F (fun k => (complexLorentzAction Γ w) (τ k)) = F u := by
    exact extendF_eq_of_explicit_witness n F hF_holo hF_real_inv
      _ u hu Δ hu_eq
  have hright : extendF F (complexLorentzAction Γ w) = F w := by
    exact extendF_eq_of_explicit_witness n F hF_holo hF_real_inv
      _ w hw Γ rfl
  calc
    extendF F (fun k => (complexLorentzAction Γ w) (τ k)) = F u := hleft
    _ = F w := hu_eq_w
    _ = extendF F (complexLorentzAction Γ w) := hright.symm

/-- `extendF` overlap-invariance and forward-tube permutation-invariance are equivalent
    formulations for a fixed permutation `τ`. -/
private theorem permInvariance_forwardTube_iff_extendF_overlap (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (τ : Equiv.Perm (Fin n)) :
    (∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (τ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (τ k)) = extendF F z) ↔
    (∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w) := by
  constructor
  · intro hExtPerm
    exact permutation_invariance_from_extendF_on_extendedTube n F hF_holo hF_real_inv τ hExtPerm
  · intro hperm
    exact extendF_perm_overlap_from_forwardTube_permInvariance n F hF_holo hF_real_inv τ hperm

/-- Reduced form of `iterated_eow_permutation_extension`: it is enough to prove
    permutation invariance of `extendF` on the extended-tube overlap for each `σ`. -/
private theorem iterated_eow_permutation_extension_of_extendF_perm (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (_hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (_hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (hExtPerm :
      ∀ (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        (fun k => z (σ k)) ∈ ExtendedTube d n →
        extendF F (fun k => z (σ k)) = extendF F z) :
    ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := by
  have hperm :
      ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
        ∀ (Γ : ComplexLorentzGroup d),
          complexLorentzAction Γ (fun k => w (σ k)) ∈ ForwardTube d n →
          F (complexLorentzAction Γ (fun k => w (σ k))) = F w := by
    exact permutation_invariance_from_extendF_on_extendedTube n F hF_holo hF_lorentz σ hExtPerm
  exact permutation_extension_from_invariance n F hF_holo hF_lorentz σ hperm

/-- Global-to-local packaging: if one already has a holomorphic extension on the
full permuted extended tube with the expected agreement/invariance properties,
then the extension data required by `iterated_eow_permutation_extension` follows
immediately for any fixed permutation `σ`. -/
private theorem iterated_eow_permutation_extension_of_global
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hGlobal :
      ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
        (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
        (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ PermutedExtendedTube d n →
          F_ext (complexLorentzAction Λ z) = F_ext z) ∧
        (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ PermutedExtendedTube d n →
          F_ext (fun k => z (π k)) = F_ext z))
    (σ : Equiv.Perm (Fin n)) :
    ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := by
  rcases hGlobal with ⟨F_ext, hF_ext_holo, hF_ext_FT, hF_ext_lor, hF_ext_perm⟩
  refine ⟨PermutedExtendedTube d n, F_ext, isOpen_permutedExtendedTube,
    forwardTube_subset_permutedExtendedTube, ?_, hF_ext_holo, ?_, ?_, ?_⟩
  · intro z hz
    exact Set.mem_iUnion.mpr ⟨σ, ⟨1, z, hz, by simp [complexLorentzAction_one]⟩⟩
  · intro z hz
    exact hF_ext_FT z hz.2
  · intro Λ z hz _
    exact hF_ext_lor Λ z hz
  · intro z hz
    have hzσFT : (fun k => z (σ k)) ∈ ForwardTube d n := hz.2
    calc
      F_ext z = F_ext (fun k => z (σ k)) := by
        exact (hF_ext_perm σ z hz.1).symm
      _ = F (fun k => z (σ k)) := hF_ext_FT _ hzσFT

/-- Bundled extension data for a fixed permutation sector. This is a compact
record form of the output shape required by `iterated_eow_permutation_extension`.
-/
private structure PermExtensionData (n : ℕ) (σ : Equiv.Perm (Fin n))
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  U : Set (Fin n → Fin (d + 1) → ℂ)
  Fσ : (Fin n → Fin (d + 1) → ℂ) → ℂ
  hU_open : IsOpen U
  hFT_sub : ForwardTube d n ⊆ U
  hσFT_sub : {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U
  hFσ_holo : DifferentiableOn ℂ Fσ U
  hFσ_eq_F : ∀ z ∈ U ∩ ForwardTube d n, Fσ z = F z
  hFσ_inv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ U → complexLorentzAction Λ z ∈ U →
      Fσ (complexLorentzAction Λ z) = Fσ z
  hFσ_eq_perm : ∀ z ∈ U ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
      Fσ z = F (fun k => z (σ k))

/-- Convert packed extension data into the existential shape used by
`iterated_eow_permutation_extension`. -/
private def PermExtensionData.toExists
    {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (P : PermExtensionData (d := d) n σ F) :
    ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := by
  refine ⟨P.U, P.Fσ, P.hU_open, P.hFT_sub, P.hσFT_sub, P.hFσ_holo,
    P.hFσ_eq_F, P.hFσ_inv, P.hFσ_eq_perm⟩

/-- Build packed extension data from an existential package. -/
private def PermExtensionData.ofExists
    {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (h : ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k)))) :
    PermExtensionData (d := d) n σ F := by
  classical
  let U_σ : Set (Fin n → Fin (d + 1) → ℂ) := Classical.choose h
  let hU : ∃ (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := Classical.choose_spec h
  let F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ := Classical.choose hU
  let hF : IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := Classical.choose_spec hU
  refine ⟨U_σ, F_σ, hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1,
    hF.2.2.2.2.2.1, hF.2.2.2.2.2.2⟩

/-- Identity-sector extension data packaged as `PermExtensionData`. -/
private def permExtensionData_of_identity (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
    PermExtensionData (d := d) n (1 : Equiv.Perm (Fin n)) F := by
  refine ⟨ForwardTube d n, F, isOpen_forwardTube, ?_, ?_, hF_holo, ?_, ?_, ?_⟩
  · intro z hz
    exact hz
  · intro z hz
    simpa using hz
  · intro z hz
    exact rfl
  · intro Λ z hzU hΛzU
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hzU hΛzU
  · intro z hz
    simp

/-- Combinatorial induction scaffold: once an adjacent-swap constructor is
available for sector extension data, extension data follows for every
permutation by `adjSwap_induction`. -/
private def permExtensionData_all_of_adjSwap
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hStep :
      ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        Nonempty (PermExtensionData (d := d) n σ F) →
        Nonempty (PermExtensionData (d := d) n
          (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) F)) :
    ∀ τ : Equiv.Perm (Fin n), Nonempty (PermExtensionData (d := d) n τ F) := by
  refine Fin.Perm.adjSwap_induction (n := n)
    (motive := fun τ => Nonempty (PermExtensionData (d := d) n τ F))
    ?base
    (fun σ i hi ih => hStep σ i hi ih)
  exact ⟨permExtensionData_of_identity (d := d) n F hF_holo hF_lorentz⟩

/-- Unpack a family of sector-wise `PermExtensionData` into the existential
output format of `iterated_eow_permutation_extension`. -/
private def iteratedExtension_exists_of_allData
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAll : ∀ σ : Equiv.Perm (Fin n), Nonempty (PermExtensionData (d := d) n σ F)) :
    ∀ σ : Equiv.Perm (Fin n),
      ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
        (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        IsOpen U_σ ∧
        ForwardTube d n ⊆ U_σ ∧
        {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
        DifferentiableOn ℂ F_σ U_σ ∧
        (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
        (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
          F_σ (complexLorentzAction Λ z) = F_σ z) ∧
        (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
          F_σ z = F (fun k => z (σ k))) := by
  intro σ
  rcases hAll σ with ⟨hσ⟩
  exact hσ.toExists

/-- Lift an adjacent-swap extension step constructor into full sector-wise
existence data for all permutations, via `PermExtensionData` packing. -/
private theorem iteratedExtension_exists_of_adjSwapStep
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hStep :
      ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        (∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
          (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
          IsOpen U_σ ∧
          ForwardTube d n ⊆ U_σ ∧
          {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
          DifferentiableOn ℂ F_σ U_σ ∧
          (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
          (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
            z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
            F_σ (complexLorentzAction Λ z) = F_σ z) ∧
          (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
            F_σ z = F (fun k => z (σ k)))) →
        (∃ (U_τ : Set (Fin n → Fin (d + 1) → ℂ))
          (F_τ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
          IsOpen U_τ ∧
          ForwardTube d n ⊆ U_τ ∧
          {z | (fun k => z ((Equiv.swap i ⟨i.val + 1, hi⟩ * σ) k)) ∈ ForwardTube d n}
            ⊆ U_τ ∧
          DifferentiableOn ℂ F_τ U_τ ∧
          (∀ z ∈ U_τ ∩ ForwardTube d n, F_τ z = F z) ∧
          (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
            z ∈ U_τ → complexLorentzAction Λ z ∈ U_τ →
            F_τ (complexLorentzAction Λ z) = F_τ z) ∧
          (∀ z ∈ U_τ ∩
              {z | (fun k => z ((Equiv.swap i ⟨i.val + 1, hi⟩ * σ) k)) ∈ ForwardTube d n},
            F_τ z = F (fun k => z ((Equiv.swap i ⟨i.val + 1, hi⟩ * σ) k))))) :
    ∀ σ : Equiv.Perm (Fin n),
      ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
        (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        IsOpen U_σ ∧
        ForwardTube d n ⊆ U_σ ∧
        {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
        DifferentiableOn ℂ F_σ U_σ ∧
        (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
        (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
          F_σ (complexLorentzAction Λ z) = F_σ z) ∧
        (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
          F_σ z = F (fun k => z (σ k))) := by
  have hStepPacked :
      ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        Nonempty (PermExtensionData (d := d) n σ F) →
        Nonempty (PermExtensionData (d := d) n
          (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) F) := by
    intro σ i hi hσ
    rcases hσ with ⟨hσ⟩
    have hσ_ex := hσ.toExists
    exact ⟨PermExtensionData.ofExists (d := d) (n := n)
      (σ := Equiv.swap i ⟨i.val + 1, hi⟩ * σ) (F := F) (hStep σ i hi hσ_ex)⟩
  have hAll : ∀ σ : Equiv.Perm (Fin n), Nonempty (PermExtensionData (d := d) n σ F) :=
    permExtensionData_all_of_adjSwap (d := d) n F hF_holo hF_lorentz hStepPacked
  exact iteratedExtension_exists_of_allData (d := d) n F hAll

/- **Iterated EOW extension for permutations.**
    For any permutation σ of Fin n (decomposed as a product of adjacent swaps),
    the iterated application of eow_adj_swap_extension produces a holomorphic
    function F_σ on an open domain U_σ ⊇ FT ∪ σ·FT such that:
    1. F_σ agrees with F on U_σ ∩ FT
    2. F_σ is complex Lorentz-invariant on U_σ
    3. F_σ(σ·w) = F_σ(w) for w ∈ FT with σ·w ∈ U_σ

    The construction proceeds by induction on the adjacent swap decomposition:
    - Base: F₁ = F, U₁ = FT (for the identity permutation)
    - Step: given F_σ on U_σ, apply eow_adj_swap_extension to F_σ with the
      next swap, obtaining F_{swap·σ} on U_{swap·σ} ⊇ U_σ ∪ swap·U_σ.
      The identity theorem ensures consistency.

    Infrastructure gap: this requires eow_adj_swap_extension to work on
    general holomorphic domains (not just FT), which needs a generalization
    of the EOW theorem to tube-like subsets of the extended domain. -/
/-- Open-anchor propagation on the forward-overlap base set.

If the base identity `extendF F (σ·w) = F w` holds on a nonempty open subset of
the connected base set `{w ∈ FT | σ·w ∈ ET}`, then it holds on the whole base set. -/
private theorem forward_base_eq_of_open_anchor_local
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hΩ_conn : IsConnected (permForwardOverlapSet (d := d) n σ))
    (W : Set (Fin n → Fin (d + 1) → ℂ))
    (hW_open : IsOpen W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ permForwardOverlapSet (d := d) n σ)
    (hW_eq : ∀ w ∈ W, extendF F (permAct (d := d) σ w) = F w) :
    ∀ w ∈ permForwardOverlapSet (d := d) n σ,
      extendF F (permAct (d := d) σ w) = F w := by
  let Ω : Set (Fin n → Fin (d + 1) → ℂ) := permForwardOverlapSet (d := d) n σ
  have hΩ_open : IsOpen Ω := by
    have hperm_cont : Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ => permAct (d := d) σ z) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (σ k))))
    change IsOpen (ForwardTube d n ∩ (permAct (d := d) σ) ⁻¹' ExtendedTube d n)
    exact isOpen_forwardTube.inter (isOpen_extendedTube.preimage hperm_cont)
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hExt_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n) :=
    extendF_holomorphicOn n F hF_holo hF_cinv
  let f : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun w => extendF F (permAct (d := d) σ w)
  let g : (Fin n → Fin (d + 1) → ℂ) → ℂ := F
  have hf : DifferentiableOn ℂ f Ω := by
    intro w hwΩ
    have hperm_diff : Differentiable ℂ (permAct (d := d) σ) :=
      differentiable_pi.mpr (fun k => differentiable_apply (σ k))
    have hcomp : DifferentiableAt ℂ f w := by
      exact ((hExt_holo _ hwΩ.2).differentiableAt
        (isOpen_extendedTube.mem_nhds hwΩ.2)).comp w (hperm_diff w)
    exact hcomp.differentiableWithinAt
  have hg : DifferentiableOn ℂ g Ω := by
    intro w hwΩ
    exact ((hF_holo w hwΩ.1).differentiableAt
      (isOpen_forwardTube.mem_nhds hwΩ.1)).differentiableWithinAt
  rcases hW_ne with ⟨w0, hw0W⟩
  have hw0Ω : w0 ∈ Ω := hW_sub hw0W
  have hagree : f =ᶠ[nhds w0] g := by
    apply Filter.eventuallyEq_of_mem (hW_open.mem_nhds hw0W)
    intro w hwW
    exact hW_eq w hwW
  have hEqOn : Set.EqOn f g Ω :=
    identity_theorem_product hΩ_open hΩ_conn hf hg hw0Ω hagree
  intro w hwΩ
  exact hEqOn hwΩ

/-- Composition on the ET overlap intersection:
if `extendF` is permutation-invariant for `σ` and `τ` on their ET-overlap
domains, then on points where both compositions are ET-valid one gets
invariance for `σ * τ` (the order matching `permAct` composition). -/
private theorem extendF_perm_eq_mul_on_overlap_intersection
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (_hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (_hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ τ : Equiv.Perm (Fin n))
    (hσ :
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n →
        permAct (d := d) σ z ∈ ExtendedTube d n →
        extendF F (permAct (d := d) σ z) = extendF F z)
    (hτ :
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n →
        permAct (d := d) τ z ∈ ExtendedTube d n →
        extendF F (permAct (d := d) τ z) = extendF F z) :
    ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      permAct (d := d) (σ * τ) z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) (σ * τ) z) = extendF F z := by
  intro z hz hσz hστz
  have hτ_on_σz :
      extendF F (permAct (d := d) τ (permAct (d := d) σ z)) =
        extendF F (permAct (d := d) σ z) :=
    hτ (permAct (d := d) σ z) hσz (by
      simpa [permAct, Equiv.Perm.mul_apply] using hστz)
  have hσ_on_z :
      extendF F (permAct (d := d) σ z) = extendF F z :=
    hσ z hz hσz
  have hcomp :
      permAct (d := d) (σ * τ) z =
        permAct (d := d) τ (permAct (d := d) σ z) := by
    ext k μ
    simp [permAct, Equiv.Perm.mul_apply]
  calc
    extendF F (permAct (d := d) (σ * τ) z)
        = extendF F (permAct (d := d) τ (permAct (d := d) σ z)) := by
            rw [hcomp]
    _ = extendF F (permAct (d := d) σ z) := hτ_on_σz
    _ = extendF F z := hσ_on_z

/-- Open-anchor propagation on a connected ET-overlap domain.

If `extendF F (σ·z) = extendF F z` holds on a nonempty open subset of a connected
open domain `D ⊆ ET ∩ σ⁻¹ET`, then it holds on all of `D`. -/
private theorem extendF_perm_eq_on_connected_overlap_of_open_anchor
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (D : Set (Fin n → Fin (d + 1) → ℂ))
    (hD_open : IsOpen D)
    (hD_conn : IsConnected D)
    (hD_sub_ET : D ⊆ ExtendedTube d n)
    (hD_sub_permET : D ⊆ {z | permAct (d := d) σ z ∈ ExtendedTube d n})
    (W : Set (Fin n → Fin (d + 1) → ℂ))
    (hW_open : IsOpen W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ D)
    (hW_eq : ∀ z ∈ W,
      extendF F (permAct (d := d) σ z) = extendF F z) :
    ∀ z ∈ D, extendF F (permAct (d := d) σ z) = extendF F z := by
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hExt_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n) :=
    extendF_holomorphicOn n F hF_holo hF_cinv
  let f : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => extendF F (permAct (d := d) σ z)
  let g : (Fin n → Fin (d + 1) → ℂ) → ℂ := extendF F
  have hf : DifferentiableOn ℂ f D := by
    intro z hzD
    have hperm_diff : Differentiable ℂ (permAct (d := d) σ) :=
      differentiable_pi.mpr (fun k => differentiable_apply (σ k))
    have hcomp : DifferentiableAt ℂ f z := by
      exact ((hExt_holo _ (hD_sub_permET hzD)).differentiableAt
        (isOpen_extendedTube.mem_nhds (hD_sub_permET hzD))).comp z (hperm_diff z)
    exact hcomp.differentiableWithinAt
  have hg : DifferentiableOn ℂ g D := by
    intro z hzD
    exact ((hExt_holo _ (hD_sub_ET hzD)).differentiableAt
      (isOpen_extendedTube.mem_nhds (hD_sub_ET hzD))).differentiableWithinAt
  rcases hW_ne with ⟨z0, hz0W⟩
  have hz0D : z0 ∈ D := hW_sub hz0W
  have hagree : f =ᶠ[nhds z0] g := by
    apply Filter.eventuallyEq_of_mem (hW_open.mem_nhds hz0W)
    intro z hzW
    exact hW_eq z hzW
  have hEqOn : Set.EqOn f g D :=
    identity_theorem_product hD_open hD_conn hf hg hz0D hagree
  intro z hzD
  exact hEqOn hzD

/-- Left-multiplication by one adjacent swap on ET-overlap invariance:
if `extendF` is invariant for `σ` and for the adjacent swap `τ`, and the
target overlap `D_(τ*σ)` is connected with a nonempty intermediate open anchor
`{z ∈ D_(τ*σ) | τ·z ∈ ET}`, then invariance propagates to `τ * σ` on all of
`D_(τ*σ)`. -/
private theorem extendF_perm_eq_leftMul_adjSwap_of_connected_overlap_anchor
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (hσ :
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n →
        permAct (d := d) σ z ∈ ExtendedTube d n →
        extendF F (permAct (d := d) σ z) = extendF F z)
    (hSwap :
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n →
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n →
        extendF F (permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z) = extendF F z)
    (hD_conn : IsConnected
      (permExtendedOverlapSet (d := d) n
        (Equiv.swap i ⟨i.val + 1, hi⟩ * σ)))
    (hAnchor_ne :
      ({z : Fin n → Fin (d + 1) → ℂ |
          z ∈ permExtendedOverlapSet (d := d) n
            (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) ∧
          permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n
      }).Nonempty) :
    ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ExtendedTube d n →
      permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) z) = extendF F z := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let D : Set (Fin n → Fin (d + 1) → ℂ) := permExtendedOverlapSet (d := d) n (τ * σ)
  let W : Set (Fin n → Fin (d + 1) → ℂ) := {z | z ∈ D ∧ permAct (d := d) τ z ∈ ExtendedTube d n}
  have hD_open : IsOpen D := by
    have hperm_cont : Continuous (permAct (d := d) (τ * σ)) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply ((τ * σ) k))))
    change IsOpen (ExtendedTube d n ∩ (permAct (d := d) (τ * σ)) ⁻¹' ExtendedTube d n)
    exact isOpen_extendedTube.inter (isOpen_extendedTube.preimage hperm_cont)
  have hD_sub_ET : D ⊆ ExtendedTube d n := by
    intro z hzD
    exact hzD.1
  have hD_sub_permET : D ⊆ {z | permAct (d := d) (τ * σ) z ∈ ExtendedTube d n} := by
    intro z hzD
    exact hzD.2
  have hW_open : IsOpen W := by
    have hτ_cont : Continuous (permAct (d := d) τ) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (τ k))))
    exact hD_open.inter (isOpen_extendedTube.preimage hτ_cont)
  have hW_sub : W ⊆ D := by
    intro z hzW
    exact hzW.1
  have hW_eq :
      ∀ z ∈ W, extendF F (permAct (d := d) (τ * σ) z) = extendF F z := by
    intro z hzW
    have hzET : z ∈ ExtendedTube d n := hzW.1.1
    have hτzET : permAct (d := d) τ z ∈ ExtendedTube d n := hzW.2
    have hτσzET : permAct (d := d) (τ * σ) z ∈ ExtendedTube d n := hzW.1.2
    exact extendF_perm_eq_mul_on_overlap_intersection (d := d) n F hF_holo hF_real_inv
      τ σ hSwap hσ z hzET hτzET hτσzET
  have hW_ne : W.Nonempty := by
    rcases hAnchor_ne with ⟨z0, hz0⟩
    exact ⟨z0, hz0⟩
  have hEqOnD :
      ∀ z ∈ D, extendF F (permAct (d := d) (τ * σ) z) = extendF F z :=
    extendF_perm_eq_on_connected_overlap_of_open_anchor (d := d) n F
      hF_holo hF_real_inv (τ * σ)
      D hD_open (by simpa [D] using hD_conn)
      hD_sub_ET hD_sub_permET
      W hW_open hW_ne hW_sub hW_eq
  intro z hz hτσz
  exact hEqOnD z ⟨hz, hτσz⟩

/-- Adjacent-left-step composition in the form used by permutation induction:
derive `extendF`-invariance for `swap * σ` from:
1. forward-tube invariance for `σ` (IH),
2. adjacent-swap `extendF`-invariance,
3. connectedness plus nonempty open anchor on the target ET-overlap. -/
private theorem extendF_perm_eq_leftMul_adjSwap_of_forwardIH_and_anchor
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (ih_F : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (permAct (d := d) σ w) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (permAct (d := d) σ w)) = F w)
    (hSwap :
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n →
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n →
        extendF F (permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z) = extendF F z)
    (hD_conn : IsConnected
      (permExtendedOverlapSet (d := d) n
        (Equiv.swap i ⟨i.val + 1, hi⟩ * σ)))
    (hAnchor_ne :
      ({z : Fin n → Fin (d + 1) → ℂ |
          z ∈ permExtendedOverlapSet (d := d) n
            (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) ∧
          permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n
      }).Nonempty) :
    ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ExtendedTube d n →
      permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) z) = extendF F z := by
  have hσ :
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n →
        permAct (d := d) σ z ∈ ExtendedTube d n →
        extendF F (permAct (d := d) σ z) = extendF F z :=
    extendF_perm_overlap_from_forwardTube_permInvariance (d := d) n F
      hF_holo hF_real_inv σ ih_F
  exact extendF_perm_eq_leftMul_adjSwap_of_connected_overlap_anchor (d := d) n F
    hF_holo hF_real_inv σ i hi hσ hSwap hD_conn hAnchor_ne

/-- ET-overlap permutation invariance from a left-adjacent induction scheme.

This packages the full IH-composition architecture:

1. base case `σ = 1`,
2. left-adjacent step via
   `extendF_perm_eq_leftMul_adjSwap_of_connected_overlap_anchor`,

under three geometric inputs supplied externally:

- adjacent-swap ET-overlap invariance (`hSwap`),
- connectedness of each permutation ET-overlap (`hConn`),
- nonempty left-step anchor for each `(σ, i)` (`hAnchor`). -/
private theorem extendF_perm_overlap_of_leftAdjSwap_scheme
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hSwap :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∀ z : Fin n → Fin (d + 1) → ℂ,
          z ∈ ExtendedTube d n →
          permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n →
          extendF F (permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z) = extendF F z)
    (hConn :
      ∀ σ : Equiv.Perm (Fin n),
        IsConnected (permExtendedOverlapSet (d := d) n σ))
    (hAnchor :
      ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        ({z : Fin n → Fin (d + 1) → ℂ |
            z ∈ permExtendedOverlapSet (d := d) n
              (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) ∧
            permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n
        }).Nonempty) :
    ∀ (σ : Equiv.Perm (Fin n)),
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n →
        permAct (d := d) σ z ∈ ExtendedTube d n →
        extendF F (permAct (d := d) σ z) = extendF F z := by
  refine Fin.Perm.adjSwap_induction (n := n)
    (motive := fun σ =>
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ ExtendedTube d n →
        permAct (d := d) σ z ∈ ExtendedTube d n →
        extendF F (permAct (d := d) σ z) = extendF F z)
    ?base ?step
  · intro z _hz _h1z
    have hperm : permAct (d := d) (1 : Equiv.Perm (Fin n)) z = z := by
      ext k μ
      simp [permAct]
    simp [hperm]
  · intro σ i hi ih z hz hτz
    exact extendF_perm_eq_leftMul_adjSwap_of_connected_overlap_anchor (d := d) n F
      hF_holo hF_real_inv σ i hi ih (hSwap i hi)
      (hConn (Equiv.swap i ⟨i.val + 1, hi⟩ * σ))
      (hAnchor σ i hi) z hz hτz

/-- Anchor-set nonemptiness for a left-adjacent step can be reduced to a
triple ET-membership witness:
`∃ y, y ∈ ET ∧ τ·y ∈ ET ∧ σ·y ∈ ET` implies
`∃ z, z ∈ D_(τ*σ) ∧ τ·z ∈ ET`. -/
private theorem leftAdj_anchor_nonempty_of_ET_triple
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
        z ∈ permExtendedOverlapSet (d := d) n
          (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) ∧
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n
    }).Nonempty := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases htriple with ⟨y, hyET, hτyET, hσyET⟩
  refine ⟨permAct (d := d) τ y, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hτyET, ?_⟩
    have hτσ :
        permAct (d := d) (τ * σ) (permAct (d := d) τ y) =
          permAct (d := d) σ (permAct (d := d) τ (permAct (d := d) τ y)) := by
      simpa using permAct_mul (d := d) τ σ (permAct (d := d) τ y)
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
private theorem ET_triple_nonempty_of_leftAdj_anchor
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (hAnchor :
      ({z : Fin n → Fin (d + 1) → ℂ |
          z ∈ permExtendedOverlapSet (d := d) n
            (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) ∧
          permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n
      }).Nonempty) :
    ({y : Fin n → Fin (d + 1) → ℂ |
        y ∈ ExtendedTube d n ∧
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) y ∈ ExtendedTube d n ∧
        permAct (d := d) σ y ∈ ExtendedTube d n
    }).Nonempty := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases hAnchor with ⟨z, hzD, hτzET⟩
  refine ⟨permAct (d := d) τ z, ?_⟩
  refine ⟨hτzET, ?_, ?_⟩
  · have hττ : permAct (d := d) τ (permAct (d := d) τ z) = z := by
      ext k μ
      simp [permAct, τ]
    simpa [τ, hττ] using hzD.1
  · have hτσ :
        permAct (d := d) (τ * σ) z =
          permAct (d := d) σ (permAct (d := d) τ z) := by
      simpa using permAct_mul (d := d) τ σ z
    simpa [hτσ] using hzD.2

/-- Base-step anchor nonemptiness (`σ = 1`) from adjacent sector overlap.

This is the `σ=1` instance of left-adjacent anchor existence and is useful as a
sanity check for the ET-overlap induction architecture. -/
private theorem leftAdj_anchor_nonempty_base
    [NeZero d]
    (n : ℕ)
    (i : Fin n) (hi : i.val + 1 < n) :
    ({z : Fin n → Fin (d + 1) → ℂ |
        z ∈ permExtendedOverlapSet (d := d) n
          (Equiv.swap i ⟨i.val + 1, hi⟩ * (1 : Equiv.Perm (Fin n))) ∧
        permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube d n
    }).Nonempty := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hsec :
      (permSector (d := d) n (1 : Equiv.Perm (Fin n)) ∩
        permSector (d := d) n ((1 : Equiv.Perm (Fin n)) * τ)).Nonempty :=
    adjacent_permSector_overlap_nonempty (d := d) n (1 : Equiv.Perm (Fin n)) i hi
  rcases hsec with ⟨y, hy1, hy1τ⟩
  have hyET : y ∈ ExtendedTube d n := by
    simpa [permSector, permAct] using hy1
  have hτyET : permAct (d := d) τ y ∈ ExtendedTube d n := by
    simpa [permSector] using hy1τ
  have htriple :
      ({y : Fin n → Fin (d + 1) → ℂ |
          y ∈ ExtendedTube d n ∧
          permAct (d := d) τ y ∈ ExtendedTube d n ∧
          permAct (d := d) (1 : Equiv.Perm (Fin n)) y ∈ ExtendedTube d n
      }).Nonempty := ⟨y, hyET, hτyET, by simpa [permAct] using hyET⟩
  simpa [τ] using
    (leftAdj_anchor_nonempty_of_ET_triple (d := d) n (1 : Equiv.Perm (Fin n)) i hi htriple)

/-- Convert a local eventual anchor at one base point into an explicit nonempty
open anchor subset of the forward-overlap base. -/
private theorem exists_forward_open_anchor_of_eventuallyEq_local
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (d + 1) → ℂ)
    (hw0Ω : w0 ∈ permForwardOverlapSet (d := d) n σ)
    (hlocal : ∀ᶠ w in 𝓝 w0,
      w ∈ permForwardOverlapSet (d := d) n σ →
      extendF F (permAct (d := d) σ w) = F w) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := d) n σ ∧
      (∀ w ∈ W, extendF F (permAct (d := d) σ w) = F w) := by
  let Ω : Set (Fin n → Fin (d + 1) → ℂ) := permForwardOverlapSet (d := d) n σ
  have hΩ_open : IsOpen Ω := by
    have hperm_cont : Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ => permAct (d := d) σ z) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (σ k))))
    change IsOpen (ForwardTube d n ∩ (permAct (d := d) σ) ⁻¹' ExtendedTube d n)
    exact isOpen_forwardTube.inter (isOpen_extendedTube.preimage hperm_cont)
  have hnhds_inter :
      (Ω ∩ {w | w ∈ Ω → extendF F (permAct (d := d) σ w) = F w}) ∈ 𝓝 w0 := by
    refine Filter.inter_mem (hΩ_open.mem_nhds ?_) hlocal
    exact hw0Ω
  rcases mem_nhds_iff.mp hnhds_inter with ⟨W, hW_sub, hW_open, hw0W⟩
  have hW_ne : W.Nonempty := ⟨w0, hw0W⟩
  have hW_subΩ : W ⊆ Ω := by
    intro w hwW
    exact (hW_sub hwW).1
  have hW_eq : ∀ w ∈ W, extendF F (permAct (d := d) σ w) = F w := by
    intro w hwW
    exact (hW_sub hwW).2 (hW_subΩ hwW)
  exact ⟨W, hW_open, hW_ne, hW_subΩ, hW_eq⟩

/-- Transport a local eventual equality for `F` with a fixed Lorentz witness to
the corresponding local eventual base equality for `extendF`. -/
private theorem eventually_extendF_base_eq_of_eventually_forward_eq_fixedLorentz
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (d + 1) → ℂ)
    (Γ : ComplexLorentzGroup d)
    (hΓw0_FT : complexLorentzAction Γ (permAct (d := d) σ w0) ∈ ForwardTube d n)
    (hlocalF : ∀ᶠ w in 𝓝 w0,
      w ∈ permForwardOverlapSet (d := d) n σ →
      F (complexLorentzAction Γ (permAct (d := d) σ w)) = F w) :
    ∀ᶠ w in 𝓝 w0,
      w ∈ permForwardOverlapSet (d := d) n σ →
      extendF F (permAct (d := d) σ w) = F w := by
  have hcont : Continuous
      (fun w : Fin n → Fin (d + 1) → ℂ =>
        complexLorentzAction Γ (permAct (d := d) σ w)) := by
    have hperm_cont : Continuous (permAct (d := d) σ) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (σ k))))
    exact (continuous_complexLorentzAction_snd Γ).comp hperm_cont
  have hnearFT :
      ∀ᶠ w in 𝓝 w0,
        complexLorentzAction Γ (permAct (d := d) σ w) ∈ ForwardTube d n := by
    exact (isOpen_forwardTube.preimage hcont).mem_nhds hΓw0_FT
  filter_upwards [hnearFT, hlocalF] with w hwFT hwEq hwΩ
  have hExt :
      extendF F (permAct (d := d) σ w) =
        F (complexLorentzAction Γ (permAct (d := d) σ w)) := by
    have hz :
        permAct (d := d) σ w =
          complexLorentzAction Γ⁻¹
            (complexLorentzAction Γ (permAct (d := d) σ w)) := by
      simp [complexLorentzAction_inv]
    exact extendF_eq_of_explicit_witness (d := d) n F hF_holo hF_real_inv
      (permAct (d := d) σ w)
      (complexLorentzAction Γ (permAct (d := d) σ w))
      hwFT Γ⁻¹ hz
  exact hExt.trans (hwEq hwΩ)

/-- Deferred geometric input (`d ≥ 2`): connectedness of the permutation seed set.
    This isolates the remaining global connectedness obligation from the EOW/identity
    theorem plumbing. -/
private theorem deferred_isConnected_permOrbitSeedSet_dge2
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    IsConnected (permOrbitSeedSet (d := d) n σ) := by
  sorry

/-- Deferred geometric input (`d = 1`): connectedness of the permutation seed set. -/
private theorem deferred_isConnected_permOrbitSeedSet_d1
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsConnected (permOrbitSeedSet (d := 1) n σ) := by
  sorry

/-- Deferred `d=1` connectedness package in ET-overlap form, derived from
the seed-connectedness deferred input. -/
private theorem deferred_isConnected_permExtendedOverlapSet_d1
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsConnected (permExtendedOverlapSet (d := 1) n σ) := by
  have hseed : IsConnected (permOrbitSeedSet (d := 1) n σ) :=
    deferred_isConnected_permOrbitSeedSet_d1 (n := n) σ
  have hFwd : IsConnected (permForwardOverlapSet (d := 1) n σ) :=
    (isConnected_permOrbitSeedSet_iff_permForwardOverlapSet (d := 1) n σ).1 hseed
  exact isConnected_permExtendedOverlap_of_forwardOverlapConnected
    (d := 1) n σ hFwd

/-- `d=1` ET-overlap permutation invariance from the left-adjacent scheme,
assuming two explicit geometric ingredients:

1. adjacent-swap ET-overlap invariance (`hSwap`),
2. nonempty left-step anchors (`hAnchor`) for each induction step. -/
private theorem extendF_perm_overlap_d1_of_leftAdjSwap_scheme_inputs
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hSwap :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∀ z : Fin n → Fin (1 + 1) → ℂ,
          z ∈ ExtendedTube 1 n →
          permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube 1 n →
          extendF F (permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z) = extendF F z)
    (hAnchor :
      ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        ({z : Fin n → Fin (1 + 1) → ℂ |
            z ∈ permExtendedOverlapSet (d := 1) n
              (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) ∧
            permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube 1 n
        }).Nonempty) :
    ∀ (σ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (1 + 1) → ℂ),
      z ∈ ExtendedTube 1 n →
      permAct (d := 1) σ z ∈ ExtendedTube 1 n →
      extendF F (permAct (d := 1) σ z) = extendF F z := by
  have hConn :
      ∀ σ : Equiv.Perm (Fin n),
        IsConnected (permExtendedOverlapSet (d := 1) n σ) := by
    intro σ
    exact deferred_isConnected_permExtendedOverlapSet_d1 (n := n) σ
  exact extendF_perm_overlap_of_leftAdjSwap_scheme (d := 1) n F hF_holo hF_real_inv
    hSwap hConn hAnchor

/-- From seed connectedness (`d = 1`), extract a concrete forward-overlap anchor
point and a fixed Lorentz witness that sends its permuted image back to `FT`. -/
private theorem exists_forward_anchor_with_lorentz_of_seedConnected_d1
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hseed_conn : IsConnected (permOrbitSeedSet (d := 1) n σ)) :
    ∃ w0 : Fin n → Fin (1 + 1) → ℂ,
      ∃ Γ : ComplexLorentzGroup 1,
        w0 ∈ permForwardOverlapSet (d := 1) n σ ∧
        complexLorentzAction Γ (permAct (d := 1) σ w0) ∈ ForwardTube 1 n := by
  have hΩ_conn : IsConnected (permForwardOverlapSet (d := 1) n σ) :=
    (isConnected_permOrbitSeedSet_iff_permForwardOverlapSet (d := 1) n σ).1 hseed_conn
  rcases hΩ_conn.1 with ⟨w0, hw0Ω⟩
  rcases (mem_permForwardOverlapSet_iff_exists_lorentz (d := 1) n σ w0).1 hw0Ω with
    ⟨Γ, hw0slice⟩
  exact ⟨w0, Γ, hw0Ω, hw0slice.2⟩

/-- Deferred local gluing step (`d = 1`, nontrivial branch): around a fixed
forward-overlap anchor `(w0, Γ)`, prove local eventual equality for the
fixed-witness forward identity. -/
private theorem exists_open_nhds_overlap_and_forward_of_anchor_d1
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (hw0Ω : w0 ∈ permForwardOverlapSet (d := 1) n σ)
    (hΓw0_FT : complexLorentzAction Γ (permAct (d := 1) σ w0) ∈ ForwardTube 1 n) :
    ∃ U : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen U ∧
      w0 ∈ U ∧
      (∀ w ∈ U,
        w ∈ permForwardOverlapSet (d := 1) n σ ∧
        complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n) := by
  let Ω : Set (Fin n → Fin (1 + 1) → ℂ) := permForwardOverlapSet (d := 1) n σ
  let φ : (Fin n → Fin (1 + 1) → ℂ) → (Fin n → Fin (1 + 1) → ℂ) :=
    fun w => complexLorentzAction Γ (permAct (d := 1) σ w)
  have hΩ_open : IsOpen Ω := by
    have hperm_cont : Continuous
        (fun z : Fin n → Fin (1 + 1) → ℂ => permAct (d := 1) σ z) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (σ k))))
    change IsOpen (ForwardTube 1 n ∩ (permAct (d := 1) σ) ⁻¹' ExtendedTube 1 n)
    exact isOpen_forwardTube.inter (isOpen_extendedTube.preimage hperm_cont)
  have hφ_cont : Continuous φ := by
    have hperm_cont : Continuous (permAct (d := 1) σ) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (σ k))))
    exact (continuous_complexLorentzAction_snd Γ).comp hperm_cont
  have hΩ_nhds : Ω ∈ 𝓝 w0 := hΩ_open.mem_nhds hw0Ω
  have hFT_nhds : φ ⁻¹' ForwardTube 1 n ∈ 𝓝 w0 :=
    (isOpen_forwardTube.preimage hφ_cont).mem_nhds hΓw0_FT
  have hnhds_inter : (Ω ∩ (φ ⁻¹' ForwardTube 1 n)) ∈ 𝓝 w0 :=
    Filter.inter_mem hΩ_nhds hFT_nhds
  rcases mem_nhds_iff.mp hnhds_inter with ⟨U, hU_sub, hU_open, hw0U⟩
  refine ⟨U, hU_open, hw0U, ?_⟩
  intro w hwU
  exact ⟨(hU_sub hwU).1, (hU_sub hwU).2⟩

/-- `d=1` local identity from a back-witness:
if `Λ` sends `σ·w` exactly back to `w`, and both resulting points are in `FT`,
then the two forward values agree. -/
private theorem forward_eq_of_back_witness_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (w : Fin n → Fin (1 + 1) → ℂ)
    (Γ Λ : ComplexLorentzGroup 1)
    (hwFT : w ∈ ForwardTube 1 n)
    (hΓσwFT : complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (hΛ_back : complexLorentzAction Λ (permAct (d := 1) σ w) = w) :
    F (complexLorentzAction Γ (permAct (d := 1) σ w)) = F w := by
  let z0 : Fin n → Fin (1 + 1) → ℂ :=
    complexLorentzAction Λ (permAct (d := 1) σ w)
  have hz0FT : z0 ∈ ForwardTube 1 n := by
    simpa [z0, hΛ_back] using hwFT
  have htarget :
      complexLorentzAction (Γ * Λ⁻¹) z0 =
        complexLorentzAction Γ (permAct (d := 1) σ w) := by
    calc
      complexLorentzAction (Γ * Λ⁻¹) z0
          = complexLorentzAction Γ (complexLorentzAction Λ⁻¹ z0) := by
              simp [z0, complexLorentzAction_mul]
      _ = complexLorentzAction Γ (permAct (d := 1) σ w) := by
            simp [z0, complexLorentzAction_inv]
  have hcinv :
      F (complexLorentzAction (Γ * Λ⁻¹) z0) = F z0 :=
    complex_lorentz_invariance n F hF_holo hF_lorentz (Γ * Λ⁻¹) z0
      hz0FT (by simpa [htarget] using hΓσwFT)
  calc
    F (complexLorentzAction Γ (permAct (d := 1) σ w))
        = F (complexLorentzAction (Γ * Λ⁻¹) z0) := by
            simp [htarget]
    _ = F z0 := hcinv
    _ = F w := by simp [z0, hΛ_back]

/-- `d=1` slice propagation at fixed `w`:
if one slice point `Λ₀·(σ·w)` in `FT` is already anchored to `F w`, then every
other slice point `Γ·(σ·w)` in `FT` has the same `F` value. -/
private theorem forward_eq_of_slice_anchor_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (w : Fin n → Fin (1 + 1) → ℂ)
    (Γ Λ₀ : ComplexLorentzGroup 1)
    (hΓσwFT : complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (hΛ₀σwFT : complexLorentzAction Λ₀ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (hΛ₀eq : F (complexLorentzAction Λ₀ (permAct (d := 1) σ w)) = F w) :
    F (complexLorentzAction Γ (permAct (d := 1) σ w)) = F w := by
  let z₀ : Fin n → Fin (1 + 1) → ℂ :=
    complexLorentzAction Λ₀ (permAct (d := 1) σ w)
  have htarget :
      complexLorentzAction (Γ * Λ₀⁻¹) z₀ =
        complexLorentzAction Γ (permAct (d := 1) σ w) := by
    calc
      complexLorentzAction (Γ * Λ₀⁻¹) z₀
          = complexLorentzAction Γ (complexLorentzAction Λ₀⁻¹ z₀) := by
              simp [z₀, complexLorentzAction_mul]
      _ = complexLorentzAction Γ (permAct (d := 1) σ w) := by
            simp [z₀, complexLorentzAction_inv]
  have hcinv :
      F (complexLorentzAction (Γ * Λ₀⁻¹) z₀) = F z₀ :=
    complex_lorentz_invariance n F hF_holo hF_lorentz (Γ * Λ₀⁻¹) z₀
      (by simpa [z₀] using hΛ₀σwFT)
      (by simpa [htarget] using hΓσwFT)
  calc
    F (complexLorentzAction Γ (permAct (d := 1) σ w))
        = F (complexLorentzAction (Γ * Λ₀⁻¹) z₀) := by
            simp [htarget]
    _ = F z₀ := hcinv
    _ = F (complexLorentzAction Λ₀ (permAct (d := 1) σ w)) := by simp [z₀]
    _ = F w := hΛ₀eq

/-- Sufficient condition on a prepared neighborhood:
if every prepared point has a back-witness `Λw` with `Λw·(σ·w)=w`, then the
local holomorphic difference `g(w)=F(Γ·(σ·w))-F(w)` vanishes on that neighborhood. -/
private theorem g_zero_on_prepared_of_back_witness_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (g : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hg_def : g = fun w => F (complexLorentzAction Γ (permAct (d := 1) σ w)) - F w)
    (hback : ∀ w ∈ U, ∃ Λ : ComplexLorentzGroup 1,
      complexLorentzAction Λ (permAct (d := 1) σ w) = w) :
    ∀ w ∈ U, g w = 0 := by
  intro w hwU
  rcases hU_good w hwU with ⟨hwΩ, hΓσwFT⟩
  have hwFT : w ∈ ForwardTube 1 n := hwΩ.1
  rcases hback w hwU with ⟨Λ, hΛ_back⟩
  have hEq :
      F (complexLorentzAction Γ (permAct (d := 1) σ w)) = F w :=
    forward_eq_of_back_witness_d1 n F hF_holo hF_lorentz σ
      w Γ Λ hwFT hΓσwFT hΛ_back
  rw [hg_def, sub_eq_zero]
  exact hEq

/-- Eventual local zero follows immediately from a prepared-domain back-witness
pack. This isolates the purely analytic neighborhood step from the geometric
construction of witnesses. -/
private theorem eventually_zero_nhds_of_back_witness_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (g : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hg_def : g = fun w => F (complexLorentzAction Γ (permAct (d := 1) σ w)) - F w)
    (hback : ∀ w ∈ U, ∃ Λ : ComplexLorentzGroup 1,
      complexLorentzAction Λ (permAct (d := 1) σ w) = w) :
    ∀ᶠ w in 𝓝 w0, w ∈ U → g w = 0 := by
  have hzero : ∀ w ∈ U, g w = 0 :=
    g_zero_on_prepared_of_back_witness_d1 n F hF_holo hF_lorentz
      σ Γ U hU_good g hg_def hback
  exact Filter.Eventually.of_forall (fun w hwU => hzero w hwU)

/-- Eventual local zero from an eventual local back-witness condition.

This is the neighborhood-filter version of
`eventually_zero_nhds_of_back_witness_d1`: it isolates the exact geometric
input needed at the blocker site (a back-witness only near the anchor, not on
all of `U`). -/
private theorem eventually_zero_nhds_of_eventually_back_witness_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (g : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hg_def : g = fun w => F (complexLorentzAction Γ (permAct (d := 1) σ w)) - F w)
    (hback_local : ∀ᶠ w in 𝓝 w0, w ∈ U → ∃ Λ : ComplexLorentzGroup 1,
      complexLorentzAction Λ (permAct (d := 1) σ w) = w) :
    ∀ᶠ w in 𝓝 w0, w ∈ U → g w = 0 := by
  filter_upwards [hback_local] with w hwBack hwU
  rcases hU_good w hwU with ⟨hwΩ, hΓσwFT⟩
  have hwFT : w ∈ ForwardTube 1 n := hwΩ.1
  rcases hwBack hwU with ⟨Λ, hΛ_back⟩
  have hEq :
      F (complexLorentzAction Γ (permAct (d := 1) σ w)) = F w :=
    forward_eq_of_back_witness_d1 n F hF_holo hF_lorentz σ
      w Γ Λ hwFT hΓσwFT hΛ_back
  rw [hg_def, sub_eq_zero]
  exact hEq

/-- Eventual local forward equality from an eventual local slice-anchor pack:
near `w₀`, if each prepared `w` admits some `Λ₀` with
`Λ₀·(σ·w) ∈ FT` and `F(Λ₀·(σ·w)) = F(w)`, then the same equality holds for the
fixed prepared witness `Γ`. -/
private theorem eventually_forward_eq_nhds_of_eventually_slice_anchor_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (hanchor_local :
      ∀ᶠ w in 𝓝 w0, w ∈ U →
        ∃ Λ₀ : ComplexLorentzGroup 1,
          complexLorentzAction Λ₀ (permAct (d := 1) σ w) ∈ ForwardTube 1 n ∧
          F (complexLorentzAction Λ₀ (permAct (d := 1) σ w)) = F w) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      F (complexLorentzAction Γ (permAct (d := 1) σ w)) = F w := by
  filter_upwards [hanchor_local] with w hwAnchor hwU
  have hΓσwFT : complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n :=
    (hU_good w hwU).2
  rcases hwAnchor hwU with ⟨Λ₀, hΛ₀σwFT, hΛ₀eq⟩
  exact forward_eq_of_slice_anchor_d1 n F hF_holo hF_lorentz
    σ w Γ Λ₀ hΓσwFT hΛ₀σwFT hΛ₀eq

/-- `d=1` forward equality from a right-adjacent midpoint condition schema.

If every right-adjacent step satisfies the midpoint implication for the fixed
`w, Γ` witness geometry, then one obtains the full permutation equality
`F(Γ·(σ·w)) = F(w)` by adjacent-swap induction. -/
private theorem forward_eq_of_midCond_chain_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    {w : Fin n → Fin (1 + 1) → ℂ}
    (hw : w ∈ ForwardTube 1 n)
    {Γ : ComplexLorentzGroup 1}
    (hΓσwFT : complexLorentzAction Γ (fun k => w (σ k)) ∈ ForwardTube 1 n)
    (hmidCond :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
        complexLorentzAction Γ
          (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
        complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n) :
    F (complexLorentzAction Γ (fun k => w (σ k))) = F w := by
  have hchain :
      ∀ (τ : Equiv.Perm (Fin n)),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube 1 n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
    refine Fin.Perm.adjSwap_induction_right (n := n)
      (motive := fun τ =>
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube 1 n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w)
      ?base ?step
    · intro hΓwFT
      exact complex_lorentz_invariance n F hF_holo hF_lorentz Γ w hw hΓwFT
    · intro σ₀ i hi ih hΓσswapwFT
      set swap : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
      set z : Fin n → Fin (1 + 1) → ℂ :=
        complexLorentzAction Γ (fun k => w (σ₀ k))
      have hz : z ∈ ForwardTube 1 n := by
        exact hmidCond σ₀ i hi hΓσswapwFT
      have hswapz : (fun k => z (swap k)) ∈ ForwardTube 1 n := by
        simpa [z, swap, Equiv.Perm.mul_apply, lorentz_perm_commute] using hΓσswapwFT
      have hswap : F (fun k => z (swap k)) = F z :=
        eow_adj_swap_on_overlap (d := 1) n F hF_holo hF_lorentz hF_bv hF_local i hi hz hswapz
      have hσ : F z = F w := ih hz
      simpa [z, swap, Equiv.Perm.mul_apply, lorentz_perm_commute] using hswap.trans hσ
  exact hchain σ hΓσwFT

/-- d=1 local bad set for midpoint implications at fixed `Γ`.

A point `w` is bad if some right-adjacent step has the swapped-forward condition
but fails the unswapped-forward conclusion. -/
private def midCondBadSet_d1
    (n : ℕ) (Γ : ComplexLorentzGroup 1) :
    Set (Fin n → Fin (1 + 1) → ℂ) :=
  {w | ∃ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
    complexLorentzAction Γ
      (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n ∧
    ¬ complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n}

/-- `d=1` midpoint bad set excluding the already-prepared permutation `σ`.

This removes the trivial impossible branch `π = σ`, which is ruled out on a
prepared domain by `hU_good`. -/
private def midCondBadSetExclSigma_d1
    (n : ℕ) (Γ : ComplexLorentzGroup 1) (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (1 + 1) → ℂ) :=
  {w | ∃ (π : Equiv.Perm (Fin n)), π ≠ σ ∧
      ∃ (i : Fin n) (hi : i.val + 1 < n),
        complexLorentzAction Γ
          (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n ∧
        ¬ complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n}

/-- On a prepared domain `U`, midpoint-bad points automatically satisfy `π ≠ σ`.
Hence `U ∩ bad ⊆ U ∩ badExclSigma`. -/
private theorem inter_midCondBadSet_subset_exclSigma_d1
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n) :
    U ∩ midCondBadSet_d1 n Γ ⊆ U ∩ midCondBadSetExclSigma_d1 n Γ σ := by
  intro w hw
  rcases hw with ⟨hwU, hwBad⟩
  rcases hwBad with ⟨π, i, hi, hswap, hnot⟩
  have hπ_ne : π ≠ σ := by
    intro hπ
    have hσ : complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n := by
      simpa [hπ, permAct] using (hU_good w hwU).2
    exact hnot hσ
  exact ⟨hwU, ⟨π, hπ_ne, i, hi, hswap, hnot⟩⟩

/-- Topological reduction: if `w0` avoids the closure of the d=1 midpoint bad
set, then one gets an open neighborhood where the midpoint implication schema
holds uniformly. -/
private theorem exists_open_midCond_nhds_of_not_mem_closure_bad_d1
    (n : ℕ)
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hsep : w0 ∉ closure (U ∩ midCondBadSet_d1 n Γ)) :
    ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      w0 ∈ W ∧
      W ⊆ U ∧
      (∀ w ∈ W,
        ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
          complexLorentzAction Γ
            (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
          complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n) := by
  let W : Set (Fin n → Fin (1 + 1) → ℂ) := U ∩ (closure (U ∩ midCondBadSet_d1 n Γ))ᶜ
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact hU_open.inter isClosed_closure.isOpen_compl
  · exact ⟨hw0U, hsep⟩
  · intro w hwW
    exact hwW.1
  · intro w hwW π i hi hswap
    have hwNotClosure : w ∉ closure (U ∩ midCondBadSet_d1 n Γ) := hwW.2
    have hwNotBad : w ∉ U ∩ midCondBadSet_d1 n Γ := by
      intro hwBad
      exact hwNotClosure (subset_closure hwBad)
    by_contra hnot
    exact hwNotBad ⟨hwW.1, ⟨π, i, hi, hswap, hnot⟩⟩

/-- Deferred d=1 local geometric separation input (reduced form):
after removing the impossible `π = σ` branch on prepared domains, the anchor
avoids closure of the remaining bad set. -/
private theorem exists_open_midCondExclSigma_nhds_of_not_mem_closure_badExclSigma_d1
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hsep : w0 ∉ closure (U ∩ midCondBadSetExclSigma_d1 n Γ σ)) :
    ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      w0 ∈ W ∧
      W ⊆ U ∧
      (∀ w ∈ W,
        ∀ (π : Equiv.Perm (Fin n)), π ≠ σ →
          ∀ (i : Fin n) (hi : i.val + 1 < n),
            complexLorentzAction Γ
              (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
            complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n) := by
  let W : Set (Fin n → Fin (1 + 1) → ℂ) :=
    U ∩ (closure (U ∩ midCondBadSetExclSigma_d1 n Γ σ))ᶜ
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact hU_open.inter isClosed_closure.isOpen_compl
  · exact ⟨hw0U, hsep⟩
  · intro w hwW
    exact hwW.1
  · intro w hwW π hπ_ne i hi hswap
    have hwNotClosure : w ∉ closure (U ∩ midCondBadSetExclSigma_d1 n Γ σ) := hwW.2
    have hwNotBad : w ∉ U ∩ midCondBadSetExclSigma_d1 n Γ σ := by
      intro hwBad
      exact hwNotClosure (subset_closure hwBad)
    by_contra hnot
    exact hwNotBad ⟨hwW.1, ⟨π, hπ_ne, i, hi, hswap, hnot⟩⟩

/-- Local operational/closure equivalence for the reduced d=1 bad set:
an open neighborhood with uniform `π ≠ σ` midpoint implications is equivalent
to excluding the anchor from the closure of the reduced bad set. -/
private theorem not_mem_closure_midCondBadExclSigma_of_open_midCondExclSigma_nhds_d1
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hstable : ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      w0 ∈ W ∧
      W ⊆ U ∧
      (∀ w ∈ W,
        ∀ (π : Equiv.Perm (Fin n)), π ≠ σ →
          ∀ (i : Fin n) (hi : i.val + 1 < n),
            complexLorentzAction Γ
              (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
            complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n)) :
    w0 ∉ closure (U ∩ midCondBadSetExclSigma_d1 n Γ σ) := by
  rcases hstable with ⟨W, hW_open, hw0W, hW_sub, hW_mid⟩
  have hsub_compl :
      U ∩ midCondBadSetExclSigma_d1 n Γ σ ⊆ Wᶜ := by
    intro w hwBad
    have hwW_not : w ∉ W := by
      intro hwW
      rcases hwBad.2 with ⟨π, hπ_ne, i, hi, hswap, hnot⟩
      have hπ :
          complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n :=
        hW_mid w hwW π hπ_ne i hi hswap
      exact hnot hπ
    exact hwW_not
  have hclosure_sub :
      closure (U ∩ midCondBadSetExclSigma_d1 n Γ σ) ⊆ Wᶜ :=
    closure_minimal hsub_compl hW_open.isClosed_compl
  intro hw0cl
  exact (hclosure_sub hw0cl) hw0W

/-- Deferred d=1 local geometric input (operational form):
produce a local open neighborhood around the prepared anchor where all
`π ≠ σ` right-adjacent midpoint implications hold uniformly. -/
private theorem exists_open_midCondExclSigma_nhds_of_permutation_family_d1
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hfamily : ∀ (π : Equiv.Perm (Fin n)), π ≠ σ →
      ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
        IsOpen W ∧
        w0 ∈ W ∧
        W ⊆ U ∧
        (∀ w ∈ W,
          ∀ (i : Fin n) (hi : i.val + 1 < n),
            complexLorentzAction Γ
              (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
            complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n)) :
    ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      w0 ∈ W ∧
      W ⊆ U ∧
      (∀ w ∈ W,
        ∀ (π : Equiv.Perm (Fin n)), π ≠ σ →
          ∀ (i : Fin n) (hi : i.val + 1 < n),
            complexLorentzAction Γ
              (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
            complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n) := by
  choose V hV_open hw0V hV_sub hV_mid using hfamily
  let Wπ : Equiv.Perm (Fin n) → Set (Fin n → Fin (1 + 1) → ℂ) :=
    fun π => if hπ : π ≠ σ then V π hπ else U
  let W : Set (Fin n → Fin (1 + 1) → ℂ) :=
    ⋂ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), Wπ π
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact isOpen_biInter_finset (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (fun π _ => by
      by_cases hπ : π ≠ σ
      · simpa [Wπ, hπ] using hV_open π hπ
      · have hEq : π = σ := by
          by_contra hNe
          exact hπ hNe
        subst hEq
        simpa [Wπ] using hU_open)
  · refine Set.mem_iInter₂.mpr ?_
    intro π hπmem
    by_cases hπ : π ≠ σ
    · simpa [Wπ, hπ] using hw0V π hπ
    · have hEq : π = σ := by
        by_contra hNe
        exact hπ hNe
      subst hEq
      simpa [Wπ] using hw0U
  · intro w hwW
    have hwσ : w ∈ Wπ σ := by
      exact (Set.mem_iInter₂.mp hwW) σ (Finset.mem_univ σ)
    simpa [Wπ] using hwσ
  · intro w hwW π hπ i hi hswap
    have hwWπ : w ∈ Wπ π := (Set.mem_iInter₂.mp hwW) π (Finset.mem_univ π)
    have hwV : w ∈ V π hπ := by
      simpa [Wπ, hπ] using hwWπ
    exact hV_mid π hπ w hwV i hi hswap

/-- Deferred d=1 local geometric input at fixed permutation prefix `π ≠ σ`:
construct an open neighborhood around the prepared anchor where all right-adjacent
midpoint implications for that single `π` hold uniformly. -/
private theorem exists_open_midCondAtPerm_nhds_of_step_family_d1
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hn : ¬ n ≤ 1)
    (π : Equiv.Perm (Fin n))
    (_hπ_ne : π ≠ σ)
    (hstep :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
          IsOpen W ∧
          w0 ∈ W ∧
          W ⊆ U ∧
          (∀ w ∈ W,
            complexLorentzAction Γ
              (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
            complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n)) :
    ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      w0 ∈ W ∧
      W ⊆ U ∧
      (∀ w ∈ W,
        ∀ (i : Fin n) (hi : i.val + 1 < n),
          complexLorentzAction Γ
            (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
          complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n) := by
  let Adj : Type := {i : Fin n // i.val + 1 < n}
  have hAdj_nonempty : Nonempty Adj := by
    have h1lt : 1 < n := Nat.lt_of_not_ge hn
    refine ⟨⟨⟨0, Nat.lt_trans Nat.zero_lt_one h1lt⟩, ?_⟩⟩
    simpa using h1lt
  have hstep' :
      ∀ j : Adj,
        ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
          IsOpen W ∧
          w0 ∈ W ∧
          W ⊆ U ∧
          (∀ w ∈ W,
            complexLorentzAction Γ
              (fun k => w ((π * Equiv.swap j.1 ⟨j.1.val + 1, j.2⟩) k)) ∈ ForwardTube 1 n →
            complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n) := by
    intro j
    simpa using hstep j.1 j.2
  choose V hV_open hw0V hV_sub hV_mid using hstep'
  let W : Set (Fin n → Fin (1 + 1) → ℂ) := ⋂ j : Adj, V j
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite (fun j => hV_open j)
  · exact Set.mem_iInter.mpr (fun j => hw0V j)
  · intro w hwW
    rcases hAdj_nonempty with ⟨j0⟩
    exact (hV_sub j0) ((Set.mem_iInter.mp hwW) j0)
  · intro w hwW i hi hswap
    let j : Adj := ⟨i, hi⟩
    have hwVj : w ∈ V j := (Set.mem_iInter.mp hwW) j
    have hmidj :
        complexLorentzAction Γ
          (fun k => w ((π * Equiv.swap j.1 ⟨j.1.val + 1, j.2⟩) k)) ∈ ForwardTube 1 n →
        complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n :=
      hV_mid j w hwVj
    simpa [j] using hmidj hswap

/-- Deferred d=1 local geometric input at fixed permutation/step:
construct an open neighborhood around the prepared anchor where the single
right-adjacent midpoint implication for `(π, i)` holds uniformly. -/
private def midCondBadAtPermStepSet_d1
    (n : ℕ)
    (Γ : ComplexLorentzGroup 1)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    Set (Fin n → Fin (1 + 1) → ℂ) :=
  {w |
    complexLorentzAction Γ
      (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n ∧
    ¬ complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n}

/-- Fixed-step antecedent set in the d=1 midpoint implication schema:
points where the swapped-prefix side is in `FT`. -/
private def midCondAntecedentAtPermStepSet_d1
    (n : ℕ)
    (Γ : ComplexLorentzGroup 1)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n) :
    Set (Fin n → Fin (1 + 1) → ℂ) :=
  {w |
    complexLorentzAction Γ
      (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n}

/-- Closure reduction for a fixed d=1 permutation/step midpoint bad set:
if the anchor already avoids closure of the corresponding antecedent set on `U`,
then it avoids closure of the full bad set on `U`. -/
private theorem not_mem_closure_midCondBadAtPermStep_of_not_mem_closure_antecedent_d1
    (n : ℕ)
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hAsep : w0 ∉ closure (U ∩ midCondAntecedentAtPermStepSet_d1 n Γ π i hi)) :
    w0 ∉ closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi) := by
  have hsub :
      U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi ⊆
        U ∩ midCondAntecedentAtPermStepSet_d1 n Γ π i hi := by
    intro w hw
    exact ⟨hw.1, hw.2.1⟩
  exact fun hw0 =>
    hAsep (closure_mono hsub hw0)

/-- If the fixed-step antecedent holds at the anchor but the fixed-step
consequent fails there, then the anchor is already a bad point. -/
private theorem mem_midCondBadAtPermStep_of_anchor_flags_d1
    (n : ℕ)
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hw0U : w0 ∈ U)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hAw0 :
      complexLorentzAction Γ
        (fun k => w0 ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n)
    (hBw0 :
      ¬ complexLorentzAction Γ (fun k => w0 (π k)) ∈ ForwardTube 1 n) :
    w0 ∈ U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi := by
  exact ⟨hw0U, ⟨hAw0, hBw0⟩⟩

/-- If the anchor is already a fixed-step bad point in `U`, it belongs to
the closure of that fixed-step bad set in `U`. -/
private theorem mem_closure_midCondBadAtPermStep_of_anchor_bad_d1
    (n : ℕ)
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hw0Bad : w0 ∈ U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi) :
    w0 ∈ closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi) := by
  exact subset_closure hw0Bad

/-- Obstruction helper for the fixed-step d=1 midpoint-bad set:
if the step composes to the prepared permutation (`π * swap = σ`), then
preparedness gives the antecedent at the anchor. Combined with failure of the
consequent at the anchor, this forces the anchor to be a bad point. -/
private theorem mem_midCondBadAtPermStep_of_mul_swap_eq_sigma_d1
    (n : ℕ)
    (σ π : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hmul : π * Equiv.swap i ⟨i.val + 1, hi⟩ = σ)
    (hBw0 :
      ¬ complexLorentzAction Γ (fun k => w0 (π k)) ∈ ForwardTube 1 n) :
    w0 ∈ U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi := by
  have hAw0 :
      complexLorentzAction Γ
        (fun k => w0 ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n := by
    have hσw0 : complexLorentzAction Γ (permAct (d := 1) σ w0) ∈ ForwardTube 1 n :=
      (hU_good w0 hw0U).2
    simpa [permAct, hmul] using hσw0
  exact mem_midCondBadAtPermStep_of_anchor_flags_d1
    n w0 Γ U hw0U π i hi hAw0 hBw0

/-- In `d=1`, if `π * swap(i,i+1) = σ`, preparedness at the anchor forces
`Γ·(σ·w0) ∈ FT`, which excludes `Γ·(π·w0) ∈ FT` by adjacent-swap obstruction. -/
private theorem not_forward_at_anchor_of_mul_swap_eq_sigma_d1
    (n : ℕ)
    (σ π : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hmul : π * Equiv.swap i ⟨i.val + 1, hi⟩ = σ) :
    ¬ complexLorentzAction Γ (fun k => w0 (π k)) ∈ ForwardTube 1 n := by
  have hσw0FT : complexLorentzAction Γ (fun k => w0 (σ k)) ∈ ForwardTube 1 n := by
    simpa [permAct] using (hU_good w0 hw0U).2
  intro hπFT
  have hpi_eq : π = σ * Equiv.swap i ⟨i.val + 1, hi⟩ := by
    have h := congrArg (fun τ => τ * Equiv.swap i ⟨i.val + 1, hi⟩) hmul
    simpa [mul_assoc] using h
  have hswapFT :
      (fun k =>
        complexLorentzAction Γ (fun t => w0 (σ t)) ((Equiv.swap i ⟨i.val + 1, hi⟩) k))
        ∈ ForwardTube 1 n := by
    simpa [hpi_eq, Equiv.Perm.mul_apply, lorentz_perm_commute] using hπFT
  have hswap_not :
      (fun k =>
        complexLorentzAction Γ (fun t => w0 (σ t)) ((Equiv.swap i ⟨i.val + 1, hi⟩) k))
        ∉ ForwardTube 1 n := by
    intro hswapFT'
    have h1 := hσw0FT ⟨i.val + 1, hi⟩
    have h2 := hswapFT' ⟨i.val + 1, hi⟩
    have hk_ne : ¬ ((⟨i.val + 1, hi⟩ : Fin n).val = 0) := Nat.succ_ne_zero _
    simp only [hk_ne, ↓reduceDIte] at h1 h2
    have hprev : (⟨i.val + 1 - 1, by omega⟩ : Fin n) = i := by
      ext
      simp
    rw [hprev] at h1 h2
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left] at h2
    linarith [h1.1, h2.1,
      Complex.sub_im (complexLorentzAction Γ (fun t => w0 (σ t)) ⟨i.val + 1, hi⟩ 0)
        (complexLorentzAction Γ (fun t => w0 (σ t)) i 0),
      Complex.sub_im (complexLorentzAction Γ (fun t => w0 (σ t)) i 0)
        (complexLorentzAction Γ (fun t => w0 (σ t)) ⟨i.val + 1, hi⟩ 0)]
  exact hswap_not hswapFT

/-- In `d=1`, the branch `π * swap(i,i+1) = σ` is geometrically obstructed:
preparedness forces the fixed-step antecedent at the anchor, while adjacent
swap destroys FT-membership of the consequent branch. Hence the anchor is in
the fixed-step bad set closure. -/
private theorem mem_closure_midCondBadAtPermStep_of_mul_swap_eq_sigma_d1
    (n : ℕ)
    (σ π : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hmul : π * Equiv.swap i ⟨i.val + 1, hi⟩ = σ) :
    w0 ∈ closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi) := by
  have hBw0 :
      ¬ complexLorentzAction Γ (fun k => w0 (π k)) ∈ ForwardTube 1 n :=
    not_forward_at_anchor_of_mul_swap_eq_sigma_d1
      n σ π w0 Γ U hw0U hU_good i hi hmul
  have hw0Bad : w0 ∈ U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi :=
    mem_midCondBadAtPermStep_of_mul_swap_eq_sigma_d1
      n σ π w0 Γ U hw0U hU_good i hi hmul hBw0
  exact mem_closure_midCondBadAtPermStep_of_anchor_bad_d1
    n w0 Γ U π i hi hw0Bad

/-- In the obstructed `d=1` branch `π * swap(i,i+1) = σ`, no open neighborhood
around the prepared anchor can satisfy the fixed-step midpoint implication. -/
private theorem not_exists_open_midCondAtPermStep_nhds_of_mul_swap_eq_sigma_d1
    (n : ℕ)
    (σ π : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n)
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hmul : π * Equiv.swap i ⟨i.val + 1, hi⟩ = σ) :
    ¬ ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      w0 ∈ W ∧
      W ⊆ U ∧
      (∀ w ∈ W,
        complexLorentzAction Γ
          (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
        complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n) := by
  intro hW
  rcases hW with ⟨W, _hW_open, hw0W, _hW_sub, hW_mid⟩
  have hAw0 :
      complexLorentzAction Γ
        (fun k => w0 ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n := by
    have hσw0 : complexLorentzAction Γ (permAct (d := 1) σ w0) ∈ ForwardTube 1 n :=
      (hU_good w0 hw0U).2
    simpa [permAct, hmul] using hσw0
  have hBw0_not :
      ¬ complexLorentzAction Γ (fun k => w0 (π k)) ∈ ForwardTube 1 n :=
    not_forward_at_anchor_of_mul_swap_eq_sigma_d1
      n σ π w0 Γ U hw0U hU_good i hi hmul
  exact hBw0_not (hW_mid w0 hw0W hAw0)

/-- Topological extraction for a fixed d=1 permutation/step midpoint implication:
if the anchor avoids closure of the corresponding fixed bad set, there is an
open neighborhood where the implication holds uniformly. -/
private theorem exists_open_midCondAtPermStep_nhds_of_not_mem_closure_bad_d1
    (n : ℕ)
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hsep : w0 ∉ closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi)) :
    ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      w0 ∈ W ∧
      W ⊆ U ∧
      (∀ w ∈ W,
        complexLorentzAction Γ
          (fun k => w ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈ ForwardTube 1 n →
        complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n) := by
  let W : Set (Fin n → Fin (1 + 1) → ℂ) :=
    U ∩ (closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi))ᶜ
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact hU_open.inter isClosed_closure.isOpen_compl
  · exact ⟨hw0U, hsep⟩
  · intro w hwW
    exact hwW.1
  · intro w hwW hswap
    have hwNotClosure : w ∉ closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi) := hwW.2
    have hwNotBad : w ∉ U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi := by
      intro hwBad
      exact hwNotClosure (subset_closure hwBad)
    by_contra hnot
    exact hwNotBad ⟨hwW.1, ⟨hswap, hnot⟩⟩

/-- Deferred d=1 local geometric closure input for a fixed permutation/step:
at a prepared anchor/domain, the anchor avoids closure of the fixed bad set
for the midpoint implication corresponding to `(π, i)`. -/
private theorem not_mem_closure_midCondBadAtPermStep_of_anchor_forward_d1
    (n : ℕ)
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (π : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hBw0 : complexLorentzAction Γ (fun k => w0 (π k)) ∈ ForwardTube 1 n) :
    w0 ∉ closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi) := by
  let WB : Set (Fin n → Fin (1 + 1) → ℂ) :=
    {w | complexLorentzAction Γ (fun k => w (π k)) ∈ ForwardTube 1 n}
  have hperm_cont : Continuous (fun w : Fin n → Fin (1 + 1) → ℂ => fun k => w (π k)) :=
    continuous_pi (fun k => continuous_pi (fun μ =>
      (continuous_apply μ).comp (continuous_apply (π k))))
  have hWB_open : IsOpen WB :=
    isOpen_forwardTube.preimage ((continuous_complexLorentzAction_snd Γ).comp hperm_cont)
  have hw0WB : w0 ∈ WB := hBw0
  let W : Set (Fin n → Fin (1 + 1) → ℂ) := U ∩ WB
  have hW_open : IsOpen W := hU_open.inter hWB_open
  have hw0W : w0 ∈ W := ⟨hw0U, hw0WB⟩
  have hsub_compl : U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi ⊆ Wᶜ := by
    intro w hwBad hwW
    exact hwBad.2.2 hwW.2
  have hclosure_sub :
      closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi) ⊆ Wᶜ :=
    closure_minimal hsub_compl hW_open.isClosed_compl
  intro hw0cl
  exact (hclosure_sub hw0cl) hw0W

/-- Deferred `d=1` geometric inputs required to instantiate the left-adjacent
ET-overlap induction scheme. This replaces the older local-gluing blocker chain
with explicit global geometric obligations.

Current decomposition:
1. `hSwap`: adjacent-swap ET-overlap invariance for `extendF`,
2. `hAnchor`: nonempty left-step anchors for each induction step.

These are intentionally separated from pure overlap connectedness deferreds.
See `D1_SCHEME_INPUTS_NOTES.md` for the exact mathematical shape. -/
private theorem deferred_d1_leftAdjSwap_scheme_inputs
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    (∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ z : Fin n → Fin (1 + 1) → ℂ,
        z ∈ ExtendedTube 1 n →
        permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube 1 n →
        extendF F (permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z) = extendF F z) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
      ({z : Fin n → Fin (1 + 1) → ℂ |
          z ∈ permExtendedOverlapSet (d := 1) n
            (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) ∧
          permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube 1 n
      }).Nonempty) := by
  by_cases hn : n ≤ 1
  · constructor
    · intro i hi
      have h1lt : 1 < n := by
        have h1le : 1 ≤ i.val + 1 := Nat.succ_le_succ (Nat.zero_le i.val)
        exact lt_of_le_of_lt h1le hi
      exact (False.elim ((Nat.not_lt.mpr hn) h1lt))
    · intro σ i hi
      have h1lt : 1 < n := by
        have h1le : 1 ≤ i.val + 1 := Nat.succ_le_succ (Nat.zero_le i.val)
        exact lt_of_le_of_lt h1le hi
      exact (False.elim ((Nat.not_lt.mpr hn) h1lt))
  · -- Geometric/global d=1 blocker package for the nontrivial regime `n ≥ 2`.
    -- Expected closure path:
    -- 1) adjacent-swap ET-overlap invariance from d=1 adjacent-overlap geometry;
    -- 2) nonempty left-step anchors for each induction step.
    -- Both are strictly geometric and independent of the old local-gluing chain.
    have hSwap :
        ∀ (i : Fin n) (hi : i.val + 1 < n),
          ∀ z : Fin n → Fin (1 + 1) → ℂ,
            z ∈ ExtendedTube 1 n →
            permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube 1 n →
            extendF F (permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z) = extendF F z := by
      -- TODO(d=1): close adjacent-swap ET-overlap equality without a global
      -- real-witness package; this is the `hSwap` geometric input.
      sorry
    have hAnchor :
        ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
          ({z : Fin n → Fin (1 + 1) → ℂ |
              z ∈ permExtendedOverlapSet (d := 1) n
                (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) ∧
              permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈ ExtendedTube 1 n
          }).Nonempty := by
      intro σ i hi
      by_cases hσ : σ = 1
      · subst hσ
        simpa [one_mul] using
          (leftAdj_anchor_nonempty_base (d := 1) (n := n) i hi)
      · -- TODO(d=1): nontrivial-`σ` branch. Equivalently produce a triple ET
        -- witness `y ∈ ET`, `swap·y ∈ ET`, `σ·y ∈ ET`.
        sorry
    exact ⟨hSwap, hAnchor⟩

/-- Deferred `d = 1` bridge: ET-overlap invariance from seed connectedness,
refactored through the left-adjacent ET-overlap induction scheme. -/
private theorem deferred_extendF_perm_overlap_d1_of_seedConnected
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (_hseed_conn : IsConnected (permOrbitSeedSet (d := 1) n σ)) :
    ∀ (z : Fin n → Fin (1 + 1) → ℂ),
      z ∈ ExtendedTube 1 n →
      (fun k => z (σ k)) ∈ ExtendedTube 1 n →
      extendF F (fun k => z (σ k)) = extendF F z := by
  rcases deferred_d1_leftAdjSwap_scheme_inputs
      n F hF_holo hF_lorentz hF_bv hF_local with ⟨hSwap, hAnchor⟩
  simpa [permAct] using
    (extendF_perm_overlap_d1_of_leftAdjSwap_scheme_inputs
      n F hF_holo hF_lorentz hSwap hAnchor σ)

private theorem iterated_eow_permutation_extension (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n)) :
    ∃ (U_σ : Set (Fin n → Fin (d + 1) → ℂ))
      (F_σ : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U_σ ∧
      ForwardTube d n ⊆ U_σ ∧
      {z | (fun k => z (σ k)) ∈ ForwardTube d n} ⊆ U_σ ∧
      DifferentiableOn ℂ F_σ U_σ ∧
      (∀ z ∈ U_σ ∩ ForwardTube d n, F_σ z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ U_σ → complexLorentzAction Λ z ∈ U_σ →
        F_σ (complexLorentzAction Λ z) = F_σ z) ∧
      (∀ z ∈ U_σ ∩ {z | (fun k => z (σ k)) ∈ ForwardTube d n},
        F_σ z = F (fun k => z (σ k))) := by
  by_cases hσ : σ = 1
  · subst hσ
    refine ⟨ForwardTube d n, F, isOpen_forwardTube, ?_, ?_, hF_holo, ?_, ?_, ?_⟩
    · intro z hz
      exact hz
    · intro z hz
      simpa using hz
    · intro z hz
      exact rfl
    · intro Λ z hzU hΛzU
      exact complex_lorentz_invariance n F hF_holo hF_lorentz Λ z hzU hΛzU
    · intro z hz
      simp
  · by_cases hn : n ≤ 1
    · have hsub : Subsingleton (Fin n) := by
        refine ⟨?_⟩
        intro a b
        apply Fin.ext
        have ha0 : a.val = 0 := by omega
        have hb0 : b.val = 0 := by omega
        omega
      haveI : Subsingleton (Fin n) := hsub
      exfalso
      exact hσ (Subsingleton.elim σ 1)
    · -- Remaining blocker: nontrivial permutation iteration (`n ≥ 2` and σ ≠ 1)
      -- reduced to proving `extendF` permutation-invariance on the ET overlap.
      have hExtPerm :
          ∀ (z : Fin n → Fin (d + 1) → ℂ),
            z ∈ ExtendedTube d n →
            (fun k => z (σ k)) ∈ ExtendedTube d n →
            extendF F (fun k => z (σ k)) = extendF F z := by
        by_cases hd0 : d = 0
        · subst hd0
          intro z hz hσz
          have hσ1 : σ = 1 :=
            coreExtendedTube_perm_overlap_d0_forces_perm_one_general n σ
              (by simpa [ExtendedTube, BHWCore.ExtendedTube] using hz)
              (by simpa [ExtendedTube, BHWCore.ExtendedTube] using hσz)
          exact (hσ hσ1).elim
        · have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)
          have hJostWitness_hd2 :
              2 ≤ d →
              (∃ x : Fin n → Fin (d + 1) → ℝ,
                x ∈ JostSet d n ∧
                realEmbed x ∈ ExtendedTube d n ∧
                realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n) := by
            intro hd2
            simpa using
              JostWitnessGeneralSigma.jostWitness_exists (d := d) (n := n) hd2 σ
          by_cases hd2 : 2 ≤ d
          · exact extendF_perm_overlap_dge2_of_seedConnected
              (d := d) n F hF_holo hF_lorentz hF_bv hF_local hd2 σ
              (deferred_isConnected_permOrbitSeedSet_dge2 (d := d) n σ hd2)
          · have hd_eq1 : d = 1 := by
              have hle : d ≤ 1 := Nat.not_lt.mp hd2
              exact Nat.le_antisymm hle hd1
            subst hd_eq1
            have hseed_conn_d1 :
                IsConnected (permOrbitSeedSet (d := 1) n σ) :=
              deferred_isConnected_permOrbitSeedSet_d1 (n := n) σ
            exact deferred_extendF_perm_overlap_d1_of_seedConnected
              n F hF_holo hF_lorentz hF_bv hF_local σ hseed_conn_d1
      exact iterated_eow_permutation_extension_of_extendF_perm n F hF_holo hF_lorentz
        hF_bv hF_local σ hExtPerm

/-- Any extension data of the shape produced by
    `iterated_eow_permutation_extension` yields the corresponding
    permutation-invariance statement. -/
private theorem permInvariance_of_extensionData (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (τ : Equiv.Perm (Fin n))
    (U_τ : Set (Fin n → Fin (d + 1) → ℂ))
    (F_τ : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hFT_sub : ForwardTube d n ⊆ U_τ)
    (hτFT_sub : {z | (fun k => z (τ k)) ∈ ForwardTube d n} ⊆ U_τ)
    (hF_τ_eq_F : ∀ z ∈ U_τ ∩ ForwardTube d n, F_τ z = F z)
    (hF_τ_inv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ U_τ → complexLorentzAction Λ z ∈ U_τ →
      F_τ (complexLorentzAction Λ z) = F_τ z)
    (hF_τ_eq_Fτ : ∀ z ∈ U_τ ∩ {z | (fun k => z (τ k)) ∈ ForwardTube d n},
      F_τ z = F (fun k => z (τ k)))
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  have comm : complexLorentzAction Γ (fun k => w (τ k)) =
      fun k => (complexLorentzAction Γ w) (τ k) :=
    lorentz_perm_commute Γ w τ
  rw [comm] at h ⊢
  have hΓw_τFT : complexLorentzAction Γ w ∈ {z | (fun k => z (τ k)) ∈ ForwardTube d n} := h
  have hw_U : w ∈ U_τ := hFT_sub hw
  have hΓw_U : complexLorentzAction Γ w ∈ U_τ := hτFT_sub hΓw_τFT
  have h_inv : F_τ (complexLorentzAction Γ w) = F_τ w :=
    hF_τ_inv Γ w hw_U hΓw_U
  have h1 : F_τ w = F w := hF_τ_eq_F w ⟨hw_U, hw⟩
  have h2 : F_τ (complexLorentzAction Γ w) =
      F (fun k => (complexLorentzAction Γ w) (τ k)) :=
    hF_τ_eq_Fτ (complexLorentzAction Γ w) ⟨hΓw_U, hΓw_τFT⟩
  exact h2.symm.trans (h_inv.trans h1)

/-- If `extendF` is permutation-invariant on the extended-tube overlap for `τ`,
    then the corresponding forward-tube permutation-invariance statement follows
    via extension data packaging. -/
private theorem permInvariance_of_extendF_overlap (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (τ : Equiv.Perm (Fin n))
    (hExtPerm :
      ∀ (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ExtendedTube d n →
        (fun k => z (τ k)) ∈ ExtendedTube d n →
        extendF F (fun k => z (τ k)) = extendF F z) :
    ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  obtain ⟨U_τ, F_τ, hU_open, hFT_sub, hτFT_sub, hF_τ_holo,
    hF_τ_eq_F, hF_τ_inv, hF_τ_eq_Fτ⟩ :=
    iterated_eow_permutation_extension_of_extendF_perm n F hF_holo hF_lorentz
      hF_bv hF_local τ hExtPerm
  intro w hw Γ h
  exact permInvariance_of_extensionData n F τ U_τ F_τ hFT_sub hτFT_sub
    hF_τ_eq_F hF_τ_inv hF_τ_eq_Fτ hw h

/-- **Inductive step for permutation invariance: one more adjacent swap.**
    Given that F is invariant under σ (i.e., for all w in FT and Gamma with
    Gamma(sigma w) in FT, F(Gamma(sigma w)) = F(w)), prove the same for swap(i,i+1) * sigma.

    The proof uses iterated_eow_permutation_extension to obtain a holomorphic
    Lorentz-invariant extension F_σ on U_σ ⊇ FT ∪ σ·FT. Then:
    1. Rewrite (swap * σ)·w as swap·(σ·w)
    2. By Lorentz-perm commutation: Γ·(swap·(σ·w)) = swap·(Γ·(σ·w))
    3. Since swap·(Γ·(σ·w)) ∈ FT, Γ·(σ·w) ∈ swap·FT ⊆ U_{swap·σ}
    4. The Lorentz-invariant extension F_{swap·σ} bridges the gap -/
private theorem eow_chain_adj_swap (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ₀ : Equiv.Perm (Fin n)) (i₀ : Fin n) (hi₀ : i₀.val + 1 < n)
    (_ih_σ : ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
      ∀ (Γ : ComplexLorentzGroup d),
        complexLorentzAction Γ (fun k => w (σ₀ k)) ∈ ForwardTube d n →
        F (complexLorentzAction Γ (fun k => w (σ₀ k))) = F w)
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ
      (fun k => w ((Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩ * σ₀) k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ
      (fun k => w ((Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩ * σ₀) k))) = F w := by
  -- Set τ = swap * σ₀
  set τ := Equiv.swap i₀ ⟨i₀.val + 1, hi₀⟩ * σ₀
  -- Obtain the iterated EOW extension for τ
  obtain ⟨U_τ, F_τ, hU_open, hFT_sub, hτFT_sub, hF_τ_holo,
    hF_τ_eq_F, hF_τ_inv, hF_τ_eq_Fτ⟩ :=
    iterated_eow_permutation_extension n F hF_holo hF_lorentz hF_bv hF_local τ
  exact permInvariance_of_extensionData n F τ U_τ F_τ hFT_sub hτFT_sub
    hF_τ_eq_F hF_τ_inv hF_τ_eq_Fτ hw h

private theorem F_permutation_invariance (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    {w : Fin n → Fin (d + 1) → ℂ} (hw : w ∈ ForwardTube d n)
    {τ : Equiv.Perm (Fin n)} {Γ : ComplexLorentzGroup d}
    (h : complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n) :
    F (complexLorentzAction Γ (fun k => w (τ k))) = F w := by
  -- Induction on τ via adjacent transposition decomposition.
  -- The motive universally quantifies over w and Γ.
  revert w Γ
  apply Fin.Perm.adjSwap_induction (motive := fun τ =>
    ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
    ∀ (Γ : ComplexLorentzGroup d),
      complexLorentzAction Γ (fun k => w (τ k)) ∈ ForwardTube d n →
      F (complexLorentzAction Γ (fun k => w (τ k))) = F w)
  -- Base case: τ = 1. Goal reduces to F(Γ·w) = F(w), which is complex_lorentz_invariance.
  · intro w₀ hw₀ Γ₀ h₀
    simp only [Equiv.Perm.one_apply] at h₀ ⊢
    exact complex_lorentz_invariance n F hF_holo hF_lorentz Γ₀ w₀ hw₀ h₀
  -- Inductive step: τ = swap(i, i+1) * σ.
  -- Given: motive holds for σ (for all w, Γ).
  -- Goal: motive holds for swap * σ (for all w, Γ).
  -- We have w ∈ FT and Γ·((swap * σ)·w) ∈ FT.
  -- (swap * σ)·w(k) = w(σ(swap(k))), so Γ·(fun k => w(σ(swap(k)))) ∈ FT.
  --
  -- The crux: σ·w := (fun k => w(σ(k))) may NOT lie in FT, so we cannot
  -- directly apply a single-swap overlap invariance argument to σ·w.
  -- The correct argument requires the EOW-iterated holomorphic extension:
  -- at each step in the transposition decomposition, the EOW theorem extends
  -- F to a larger domain. The induction hypothesis gives this extension
  -- implicitly via the universally quantified Γ.
  --
  -- Specifically: by Lorentz-perm commutation,
  -- Γ·((swap*σ)·w) = Γ·(swap·(σ·w)) = swap·(Γ·(σ·w))  (*)
  -- If Γ·(σ·w) ∈ FT, a local swap step plus ih_σ would suffice.
  -- If Γ·(σ·w) ∉ FT, the domain extension argument is needed.
  -- This is the fundamental blocker for the induction approach.
  · intro σ₀ i₀ hi₀ ih_σ w₀ hw₀ Γ₀ h₀
    -- Blocked: the intermediate point Γ₀·(σ₀·w₀) may not lie in FT.
    -- The resolution requires extending F holomorphically across permuted
    -- tubes via iterated EOW, which is a substantial infrastructure gap.
    -- Bootstrap with a helper capturing this gap.
    exact eow_chain_adj_swap n F hF_holo hF_lorentz hF_bv hF_local
      σ₀ i₀ hi₀ ih_σ hw₀ h₀

/-- Well-definedness: any two preimages of the same point give the same F-value.
    Reduces to `F_permutation_invariance` via the Lorentz-permutation commutation
    identity `Λ·(π·w) = π·(Λ·w)`.

    From Λ₁·(π₁·w₁) = Λ₂·(π₂·w₂), applying Λ₁⁻¹ and using the commutation:
    w₁ = (Λ₁⁻¹Λ₂)·((π₂π₁⁻¹)·w₂), then `F_permutation_invariance` gives
    F(w₁) = F(w₂). -/
private theorem fullExtendF_well_defined (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ}
    (hw₁ : w₁ ∈ ForwardTube d n) (hw₂ : w₂ ∈ ForwardTube d n)
    {π₁ π₂ : Equiv.Perm (Fin n)} {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : complexLorentzAction Λ₁ (fun k => w₁ (π₁ k)) =
         complexLorentzAction Λ₂ (fun k => w₂ (π₂ k))) :
    F w₁ = F w₂ := by
  -- Step 1: Derive w₁ = Γ·(τ·w₂) where Γ = Λ₁⁻¹Λ₂, τ = π₂π₁⁻¹.
  -- Key fact: Lorentz action commutes with particle-index permutation:
  --   complexLorentzAction Λ (fun k => z (σ k)) = fun k => (complexLorentzAction Λ z) (σ k)
  -- (holds definitionally since Λ acts only on the μ-index)
  have step1 := congr_arg (complexLorentzAction Λ₁⁻¹) h
  rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one,
      ← complexLorentzAction_mul] at step1
  -- step1 : (fun k => w₁ (π₁ k)) = complexLorentzAction (Λ₁⁻¹ * Λ₂) (fun k => w₂ (π₂ k))
  -- Extract pointwise: w₁(m) = (Γ·(π₂·w₂))(π₁⁻¹ m) = (Γ·(τ·w₂))(m)
  have hw₁_eq : w₁ = complexLorentzAction (Λ₁⁻¹ * Λ₂) (fun k => w₂ ((π₂ * π₁⁻¹) k)) := by
    ext m μ
    have := congr_fun (congr_fun step1 (π₁⁻¹ m)) μ
    rw [show π₁ (π₁⁻¹ m) = m from Equiv.apply_symm_apply π₁ m] at this
    rw [this]
    simp only [complexLorentzAction, Equiv.Perm.mul_apply]
  -- Step 2: Apply F_permutation_invariance
  rw [hw₁_eq]
  exact F_permutation_invariance n F hF_holo hF_lorentz hF_bv hF_local hw₂ (hw₁_eq ▸ hw₁)

theorem bargmann_hall_wightman_theorem [NeZero d] (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    -- F extends continuously to the real boundary of the forward tube.
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    -- Local commutativity: at spacelike-separated pairs, the boundary values
    -- of F and F∘swap agree.
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- F_ext is holomorphic on the permuted extended tube
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      -- F_ext restricts to F on the forward tube
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      -- F_ext is invariant under the complex Lorentz group
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (complexLorentzAction Λ z) = F_ext z) ∧
      -- F_ext is symmetric under permutations
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) ∧
      -- Uniqueness: any holomorphic function on PermutedExtendedTube agreeing with F
      -- on ForwardTube must equal F_ext.
      (∀ (G : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ G (PermutedExtendedTube d n) →
        (∀ z ∈ ForwardTube d n, G z = F z) →
        ∀ z ∈ PermutedExtendedTube d n, G z = F_ext z) := by
  -- === Construct F_ext ===
  -- Pre-prove Properties 1 and 2 so they can be referenced in Property 5.
  have hProp1 : DifferentiableOn ℂ (fullExtendF F) (PermutedExtendedTube d n) := by
    intro z₀ hz₀
    obtain ⟨π₀, Λ₀, w₀, hw₀, hz₀_eq⟩ := Set.mem_iUnion.mp hz₀
    have hw_ft : (fun k => w₀ (π₀ k)) ∈ ForwardTube d n := hw₀
    set ψ := fun z : Fin n → Fin (d + 1) → ℂ =>
      fun k => (complexLorentzAction (Λ₀⁻¹ : ComplexLorentzGroup d) z) (π₀ k) with hψ_def
    have hψ_diff : Differentiable ℂ ψ := by
      apply differentiable_pi.mpr; intro k
      exact (differentiable_apply (π₀ k)).comp (differentiable_complexLorentzAction_snd Λ₀⁻¹)
    have hψz₀ : ψ z₀ = fun k => w₀ (π₀ k) := by
      simp only [ψ, hz₀_eq]
      rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]
    have hV_open : IsOpen {z | ψ z ∈ ForwardTube d n} :=
      isOpen_forwardTube.preimage hψ_diff.continuous
    have hz₀_V : ψ z₀ ∈ ForwardTube d n := hψz₀ ▸ hw_ft
    have hfeq : fullExtendF F =ᶠ[nhds z₀] fun z => F (ψ z) := by
      apply Filter.eventuallyEq_of_mem (hV_open.mem_nhds hz₀_V)
      intro z (hz_V : ψ z ∈ ForwardTube d n)
      have hz_chart : z = complexLorentzAction Λ₀ (fun k => (ψ z) (π₀⁻¹ k)) := by
        have h1 : (fun k => (ψ z) (π₀⁻¹ k)) = complexLorentzAction Λ₀⁻¹ z := by
          ext k μ; simp only [ψ]
          rw [show π₀ (π₀⁻¹ k) = k from Equiv.apply_symm_apply π₀ k]
        rw [h1, ← complexLorentzAction_mul, mul_inv_cancel, complexLorentzAction_one]
      simp only [fullExtendF]
      have hex : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
          (w : Fin n → Fin (d + 1) → ℂ),
          w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k)) :=
        ⟨π₀⁻¹, Λ₀, ψ z, hz_V, hz_chart⟩
      rw [dif_pos hex]
      exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
        hex.choose_spec.choose_spec.choose_spec.1 hz_V
        (hex.choose_spec.choose_spec.choose_spec.2.symm.trans hz_chart)
    have hFψ_diff : DifferentiableAt ℂ (fun z => F (ψ z)) z₀ :=
      ((hF_holo _ hz₀_V).differentiableAt (isOpen_forwardTube.mem_nhds hz₀_V)).comp
        z₀ (hψ_diff z₀)
    exact (hfeq.differentiableAt_iff.mpr hFψ_diff).differentiableWithinAt
  have hProp2 : ∀ z ∈ ForwardTube d n, fullExtendF F z = F z := by
    intro z hz
    simp only [fullExtendF]
    have hex : ∃ (π : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ ForwardTube d n ∧ z = complexLorentzAction Λ (fun k => w (π k)) :=
      ⟨Equiv.refl _, 1, z, hz, by simp [complexLorentzAction_one, Equiv.refl_apply]⟩
    rw [dif_pos hex]
    set w_c := hex.choose_spec.choose_spec.choose with hw_c_def
    have hw_c : w_c ∈ ForwardTube d n := hex.choose_spec.choose_spec.choose_spec.1
    have hz_eq := hex.choose_spec.choose_spec.choose_spec.2
    have h_eq : complexLorentzAction hex.choose_spec.choose
        (fun k => w_c (hex.choose k)) =
        complexLorentzAction 1 (fun k => z ((Equiv.refl (Fin n)) k)) := by
      rw [← hz_eq, complexLorentzAction_one]; rfl
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local hw_c hz h_eq
  refine ⟨fullExtendF F, hProp1, hProp2, ?_, ?_, ?_⟩
  -- === Property 3: Complex Lorentz invariance ===
  -- If z = Λ'·w_p with w_p ∈ PermutedForwardTube π, then Λz = (ΛΛ')·w_p.
  -- Convert w_p to w_ft ∈ ForwardTube via w_ft = fun k => w_p (π k),
  -- then both fullExtendF(Λz) and fullExtendF(z) reduce to the same FT preimage.
  · intro Λ z hz
    simp only [fullExtendF]
    obtain ⟨π, Λ', w_p, hw_p, hzw⟩ := Set.mem_iUnion.mp hz
    -- w_p ∈ PermutedForwardTube means w_ft := (fun k => w_p (π k)) ∈ ForwardTube
    set w_ft := fun k => w_p (π k) with hw_ft_def
    have hw_ft : w_ft ∈ ForwardTube d n := hw_p
    -- z = Λ'·w_p = Λ'·(fun k => w_ft (π⁻¹ k))
    have hw_p_eq : w_p = fun k => w_ft (π⁻¹ k) := by
      ext k; simp [hw_ft_def]
    have hex_z : ∃ (π' : Equiv.Perm (Fin n)) (Λ'' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ z = complexLorentzAction Λ'' (fun k => w' (π' k)) :=
      ⟨π⁻¹, Λ', w_ft, hw_ft, by rw [hzw, hw_p_eq]⟩
    have hex_Λz : ∃ (π' : Equiv.Perm (Fin n)) (Λ'' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧
        complexLorentzAction Λ z =
          complexLorentzAction Λ'' (fun k => w' (π' k)) :=
      ⟨π⁻¹, Λ * Λ', w_ft, hw_ft, by rw [hzw, hw_p_eq, complexLorentzAction_mul]⟩
    rw [dif_pos hex_Λz, dif_pos hex_z]
    -- Both choices lead to FT preimages related by Lorentz + permutation.
    -- By fullExtendF_well_defined, F-values agree.
    have hΛz_eq := hex_Λz.choose_spec.choose_spec.choose_spec.2
    -- hΛz_eq : Λ·z = Λ_Λz·(π_Λz·w_Λz)
    have hz_eq' := hex_z.choose_spec.choose_spec.choose_spec.2
    -- hz_eq' : z = Λ_z·(π_z·w_z)
    have h_eq : complexLorentzAction hex_Λz.choose_spec.choose
        (fun k => hex_Λz.choose_spec.choose_spec.choose (hex_Λz.choose k)) =
        complexLorentzAction (Λ * hex_z.choose_spec.choose)
        (fun k => hex_z.choose_spec.choose_spec.choose (hex_z.choose k)) := by
      rw [complexLorentzAction_mul, ← hz_eq']
      exact hΛz_eq.symm
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
      hex_Λz.choose_spec.choose_spec.choose_spec.1
      hex_z.choose_spec.choose_spec.choose_spec.1 h_eq
  -- === Property 4: Permutation symmetry ===
  -- fullExtendF F (z∘π) = fullExtendF F z follows from fullExtendF_well_defined:
  -- both chosen preimages yield representations of z∘π.
  · intro π z hz
    simp only [fullExtendF]
    obtain ⟨π₀, Λ₀, w₀, hw₀, hzw₀⟩ := Set.mem_iUnion.mp hz
    set w_ft := fun k => w₀ (π₀ k) with hw_ft_def
    have hw_ft : w_ft ∈ ForwardTube d n := hw₀
    have hw₀_eq : w₀ = fun k => w_ft (π₀⁻¹ k) := by ext k; simp [hw_ft_def]
    have hex_z : ∃ (π' : Equiv.Perm (Fin n)) (Λ' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ z = complexLorentzAction Λ' (fun k => w' (π' k)) :=
      ⟨π₀⁻¹, Λ₀, w_ft, hw_ft, by rw [hzw₀, hw₀_eq]⟩
    have hex_πz : ∃ (π' : Equiv.Perm (Fin n)) (Λ' : ComplexLorentzGroup d)
        (w' : Fin n → Fin (d + 1) → ℂ),
        w' ∈ ForwardTube d n ∧ (fun k => z (π k)) =
          complexLorentzAction Λ' (fun k => w' (π' k)) := by
      refine ⟨π₀⁻¹ * π, Λ₀, w_ft, hw_ft, ?_⟩
      rw [hzw₀, hw₀_eq]; ext k μ
      simp only [complexLorentzAction, Equiv.Perm.mul_apply]
    rw [dif_pos hex_πz, dif_pos hex_z]
    have hπz_eq := hex_πz.choose_spec.choose_spec.choose_spec.2
    have hz_eq' := hex_z.choose_spec.choose_spec.choose_spec.2
    -- Build: both chosen representations equal z∘π
    -- From hz_eq': z = Λ_z·(π_z·w_z), so z∘π = Λ_z·((π_z*π)·w_z)
    have h_zperm : (fun k => z (π k)) =
        complexLorentzAction hex_z.choose_spec.choose
        (fun k => hex_z.choose_spec.choose_spec.choose ((hex_z.choose * π) k)) := by
      ext k μ
      have := congr_fun (congr_fun hz_eq' (π k)) μ
      simp only [complexLorentzAction, Equiv.Perm.mul_apply] at this ⊢
      exact this
    have h_eq : complexLorentzAction hex_πz.choose_spec.choose
        (fun k => hex_πz.choose_spec.choose_spec.choose (hex_πz.choose k)) =
        complexLorentzAction hex_z.choose_spec.choose
        (fun k => hex_z.choose_spec.choose_spec.choose ((hex_z.choose * π) k)) :=
      hπz_eq.symm.trans h_zperm
    exact fullExtendF_well_defined n F hF_holo hF_lorentz hF_bv hF_local
      hex_πz.choose_spec.choose_spec.choose_spec.1
      hex_z.choose_spec.choose_spec.choose_spec.1 h_eq
  -- === Property 5: Uniqueness ===
  -- By the identity theorem for product types (`identity_theorem_product`):
  -- G and fullExtendF are holomorphic on PET (open, connected) and agree on FT
  -- (open, nonempty subset of PET), so they agree on all of PET.
  · intro G hG_holo hG_eq
    -- fullExtendF F is differentiable on PET (Property 1)
    have hF_ext_holo : DifferentiableOn ℂ (fullExtendF F) (PermutedExtendedTube d n) :=
      hProp1
    -- PET is open
    have hPET_open := @isOpen_permutedExtendedTube d n
    -- PET is connected: different permutation sectors don't directly overlap;
    -- connectedness requires applying the (proved) edge-of-the-wedge theorem to
    -- glue sectors at Jost point boundaries via local commutativity.
    have hPET_conn : IsConnected (PermutedExtendedTube d n) := by
      constructor
      · exact (forwardTube_nonempty (d := d) (n := n)).mono
          forwardTube_subset_permutedExtendedTube
      · -- PET = ⋃_π ⋃_Λ Λ·(π·FT). Each orbit Λ·(π·FT) is connected (image of
        -- convex FT under continuous maps). Adjacent permutation sectors (differing
        -- by one swap(i,i+1)) have overlapping Lorentz orbits by the EOW theorem:
        -- the glued holomorphic extension from FT ∪ σ·FT lives on an open connected
        -- domain that intersects both sectors' Lorentz orbits. Iterating over all
        -- adjacent swaps (which generate S_n) connects all sectors.
        exact permutedExtendedTube_isPreconnected
    -- Pick z₀ ∈ FT ⊆ PET
    obtain ⟨z₀, hz₀⟩ := forwardTube_nonempty (d := d) (n := n)
    have hz₀_PET := forwardTube_subset_permutedExtendedTube hz₀
    -- G and fullExtendF agree on FT, which is an open neighborhood of z₀
    have hagree : G =ᶠ[nhds z₀] fullExtendF F := by
      apply Filter.eventuallyEq_of_mem (isOpen_forwardTube.mem_nhds hz₀)
      intro w hw
      rw [hG_eq w hw, hProp2 w hw]
    -- By identity theorem on product types
    have h_eq := identity_theorem_product hPET_open hPET_conn hG_holo hF_ext_holo hz₀_PET hagree
    intro z hz
    exact h_eq hz


end BHW
