import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.D1OrbitSet

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Permutation action on particle labels. -/
def permAct {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k => z (σ k)

/-- `d = 1` forward-overlap set for a fixed permutation `σ`. -/
def permForwardOverlapSetD1
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (1 + 1) → ℂ) :=
  {w | w ∈ ForwardTube 1 n ∧ permAct (d := 1) σ w ∈ ExtendedTube 1 n}

/-- `d = 1` fixed-`w` index slice:
`{Λ | Λ · (σ · w) ∈ FT}`. -/
def permLambdaSliceD1
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : Fin n → Fin (1 + 1) → ℂ) :
    Set (ComplexLorentzGroup 1) :=
  {Λ : ComplexLorentzGroup 1 |
    complexLorentzAction Λ (permAct (d := 1) σ w) ∈ ForwardTube 1 n}

/-- `d = 1` index set of nonempty permutation forward-overlap slices. -/
def permForwardOverlapIndexSetD1
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Set (ComplexLorentzGroup 1) :=
  {Λ : ComplexLorentzGroup 1 |
    ∃ w : Fin n → Fin (1 + 1) → ℂ,
      w ∈ ForwardTube 1 n ∧
      complexLorentzAction Λ (permAct (d := 1) σ w) ∈ ForwardTube 1 n}

/-- In `d = 1`, any ET seed has a preconnected Lorentz orbit set. -/
theorem orbitSet_isPreconnected_d1_of_mem_extendedTube
    {n : ℕ} {z : Fin n → Fin (1 + 1) → ℂ}
    (hz : z ∈ ExtendedTube 1 n) :
    IsPreconnected (orbitSet (d := 1) z) := by
  rcases Set.mem_iUnion.mp hz with ⟨Δ, u, huFT, hz_eq⟩
  have hu_core : u ∈ BHWCore.ForwardTube 1 n := by
    simpa [ForwardTube, BHWCore.ForwardTube] using huFT
  have hpre_u : IsPreconnected (orbitSet (d := 1) u) := by
    simpa [orbitSet, complexLorentzAction, complexLorentzVectorAction, ForwardTube,
      BHWCore.complexLorentzAction, BHWCore.ForwardTube] using
      orbitSet_isPreconnected_d1 (n := n) u hu_core
  exact orbitSet_isPreconnected_of_orbit_eq (d := 1) (n := n) u z Δ hz_eq hpre_u

/-- For fixed `w`, if `σ · w ∈ ET` then the corresponding `d = 1` index slice
is preconnected (as a right-translate of a `d = 1` orbit set). -/
theorem permLambdaSlice_isPreconnected_d1_of_perm_mem_ET
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Fin (1 + 1) → ℂ)
    (hσw_ET : permAct (d := 1) σ w ∈ ExtendedTube 1 n) :
    IsPreconnected (permLambdaSliceD1 (n := n) σ w) := by
  rcases Set.mem_iUnion.mp hσw_ET with ⟨Δ, u, huFT, hrepr⟩
  let S : Set (ComplexLorentzGroup 1) :=
    {Γ : ComplexLorentzGroup 1 | complexLorentzAction Γ u ∈ ForwardTube 1 n}
  have hS_pre : IsPreconnected S := by
    simpa [S, ForwardTube, complexLorentzAction, complexLorentzVectorAction,
      BHWCore.ForwardTube, BHWCore.complexLorentzAction]
      using orbitSet_isPreconnected_d1 (n := n) u (by
        simpa [ForwardTube, BHWCore.ForwardTube] using huFT)
  have hmul_cont : Continuous (fun Γ : ComplexLorentzGroup 1 => Γ * Δ⁻¹) :=
    continuous_id.mul continuous_const
  have himg_pre : IsPreconnected ((fun Γ : ComplexLorentzGroup 1 => Γ * Δ⁻¹) '' S) :=
    hS_pre.image _ hmul_cont.continuousOn
  have hset_eq :
      (permLambdaSliceD1 (n := n) σ w : Set (ComplexLorentzGroup 1))
        = (fun Γ : ComplexLorentzGroup 1 => Γ * Δ⁻¹) '' S := by
    ext Λ
    constructor
    · intro hΛ
      refine ⟨Λ * Δ, ?_, ?_⟩
      · change complexLorentzAction (Λ * Δ) u ∈ ForwardTube 1 n
        have hmul :
            complexLorentzAction (Λ * Δ) u =
              complexLorentzAction Λ (complexLorentzAction Δ u) := by
          simpa using complexLorentzAction_mul Λ Δ u
        rw [hmul]
        have hΛ' : complexLorentzAction Λ (permAct (d := 1) σ w) ∈ ForwardTube 1 n := by
          simpa [permLambdaSliceD1] using hΛ
        simpa [hrepr] using hΛ'
      · simp
    · rintro ⟨Γ, hΓS, hΓ⟩
      change complexLorentzAction Λ (permAct (d := 1) σ w) ∈ ForwardTube 1 n
      have hΛ : Λ = Γ * Δ⁻¹ := by simpa using hΓ.symm
      rw [hΛ, hrepr]
      have hmul :
          complexLorentzAction (Γ * Δ⁻¹) (complexLorentzAction Δ u) =
            complexLorentzAction Γ u := by
        calc
          complexLorentzAction (Γ * Δ⁻¹) (complexLorentzAction Δ u)
              = complexLorentzAction Γ
                  (complexLorentzAction Δ⁻¹ (complexLorentzAction Δ u)) := by
                    simp [complexLorentzAction_mul]
          _ = complexLorentzAction Γ u := by
                simp [complexLorentzAction_inv]
      have hΓFT : complexLorentzAction Γ u ∈ ForwardTube 1 n := by
        simpa [S] using hΓS
      exact hmul ▸ hΓFT
  simpa [hset_eq] using himg_pre

/-- For fixed `w`, if `σ · w ∈ ET` then the corresponding `d = 1` index slice
is connected (nonempty + preconnected). -/
theorem permLambdaSlice_isConnected_d1_of_perm_mem_ET
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Fin (1 + 1) → ℂ)
    (hσw_ET : permAct (d := 1) σ w ∈ ExtendedTube 1 n) :
    IsConnected (permLambdaSliceD1 (n := n) σ w) := by
  have hpre : IsPreconnected (permLambdaSliceD1 (n := n) σ w) :=
    permLambdaSlice_isPreconnected_d1_of_perm_mem_ET (n := n) σ w hσw_ET
  rcases Set.mem_iUnion.mp hσw_ET with ⟨Δ, u, huFT, hrepr⟩
  have hΔ : Δ⁻¹ ∈ permLambdaSliceD1 (n := n) σ w := by
    have hInv : complexLorentzAction Δ⁻¹ (permAct (d := 1) σ w) = u := by
      simpa [hrepr] using (complexLorentzAction_inv Δ u)
    simpa [permLambdaSliceD1, hInv] using huFT
  exact ⟨⟨Δ⁻¹, hΔ⟩, hpre⟩

/-- Characterization of the `d = 1` index-set membership by slice witnesses. -/
theorem mem_permForwardOverlapIndexSetD1_iff_exists_mem_slice
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup 1) :
    Λ ∈ permForwardOverlapIndexSetD1 (n := n) σ ↔
      ∃ w : Fin n → Fin (1 + 1) → ℂ,
        w ∈ permForwardOverlapSetD1 (n := n) σ ∧
          Λ ∈ permLambdaSliceD1 (n := n) σ w := by
  constructor
  · rintro ⟨w, hwFT, hΛσwFT⟩
    have hσw_ET : permAct (d := 1) σ w ∈ ExtendedTube 1 n := by
      refine Set.mem_iUnion.mpr ?_
      refine ⟨Λ⁻¹, complexLorentzAction Λ (permAct (d := 1) σ w), hΛσwFT, ?_⟩
      simp [complexLorentzAction_inv]
    exact ⟨w, ⟨hwFT, hσw_ET⟩, hΛσwFT⟩
  · rintro ⟨w, hwov, hΛσwFT⟩
    exact ⟨w, hwov.1, hΛσwFT⟩

/-- `d = 1` index set as a union of fixed-`w` slices over overlap witnesses. -/
theorem permForwardOverlapIndexSetD1_eq_sUnion_slices
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permForwardOverlapIndexSetD1 (n := n) σ =
      ⋃₀ {S : Set (ComplexLorentzGroup 1) |
        ∃ w : Fin n → Fin (1 + 1) → ℂ,
          w ∈ permForwardOverlapSetD1 (n := n) σ ∧
            S = permLambdaSliceD1 (n := n) σ w} := by
  ext Λ
  constructor
  · intro hΛ
    rcases (mem_permForwardOverlapIndexSetD1_iff_exists_mem_slice (n := n) σ Λ).1 hΛ with
      ⟨w, hwov, hΛw⟩
    refine Set.mem_sUnion.2 ?_
    exact ⟨permLambdaSliceD1 (n := n) σ w, ⟨w, hwov, rfl⟩, hΛw⟩
  · intro hΛ
    rcases Set.mem_sUnion.1 hΛ with ⟨S, hSfam, hΛS⟩
    rcases hSfam with ⟨w, hwov, rfl⟩
    exact (mem_permForwardOverlapIndexSetD1_iff_exists_mem_slice (n := n) σ Λ).2
      ⟨w, hwov, hΛS⟩

/-- Each `d = 1` fixed-`w` slice attached to an overlap witness is preconnected. -/
theorem permLambdaSlice_isPreconnected_d1_of_mem_overlap
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Fin (1 + 1) → ℂ)
    (hwov : w ∈ permForwardOverlapSetD1 (n := n) σ) :
    IsPreconnected (permLambdaSliceD1 (n := n) σ w) :=
  permLambdaSlice_isPreconnected_d1_of_perm_mem_ET (n := n) σ w hwov.2

/-- Connected version of `permLambdaSlice_isPreconnected_d1_of_mem_overlap`. -/
theorem permLambdaSlice_isConnected_d1_of_mem_overlap
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Fin (1 + 1) → ℂ)
    (hwov : w ∈ permForwardOverlapSetD1 (n := n) σ) :
    IsConnected (permLambdaSliceD1 (n := n) σ w) :=
  permLambdaSlice_isConnected_d1_of_perm_mem_ET (n := n) σ w hwov.2

end BHW
