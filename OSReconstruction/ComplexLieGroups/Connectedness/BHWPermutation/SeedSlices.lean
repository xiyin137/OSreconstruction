import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Forward-overlap base set for a fixed permutation `σ`. -/
def permForwardOverlapSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {w | w ∈ ForwardTube d n ∧ permAct (d := d) σ w ∈ ExtendedTube d n}

/-- ET seed set for a fixed permutation `σ`: `ET ∩ σFT`. -/
def permSeedSet (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ExtendedTube d n ∩ PermutedForwardTube d n σ⁻¹

/-- Unfolding form of the permutation seed set. -/
theorem permSeedSet_eq_inter_permutedForwardTube
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permSeedSet (d := d) n σ =
      ExtendedTube d n ∩ PermutedForwardTube d n σ⁻¹ := by
  rfl

/-- Seed sets are open intersections of ET and permuted forward tubes. -/
theorem isOpen_permSeedSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsOpen (permSeedSet (d := d) n σ) := by
  rw [permSeedSet_eq_inter_permutedForwardTube (d := d) n σ]
  exact isOpen_extendedTube.inter (isOpen_permutedForwardTube (d := d) (n := n) σ⁻¹)

/-- Fixed-`Λ` seed slice: `σFT ∩ (Λ · FT)`. -/
def permSeedSlice
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  PermutedForwardTube d n σ⁻¹ ∩
    (fun w : Fin n → Fin (d + 1) → ℂ => complexLorentzAction Λ w) '' ForwardTube d n

/-- Permuted forward tubes are convex (as linear preimages of `ForwardTube`). -/
theorem permutedForwardTube_convex
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Convex ℝ (PermutedForwardTube d n σ) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  change (fun k => (a • z₁ + b • z₂) (σ k)) ∈ ForwardTube d n
  have hperm_linear :
      (fun k => (a • z₁ + b • z₂) (σ k))
        = a • (fun k => z₁ (σ k)) + b • (fun k => z₂ (σ k)) := by
    ext k μ
    simp [Pi.smul_apply, Pi.add_apply]
  rw [hperm_linear]
  exact forwardTube_convex hz₁ hz₂ ha hb hab

/-- Fixed-`Λ` seed slices are convex. -/
theorem permSeedSlice_convex
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    Convex ℝ (permSeedSlice (d := d) n σ Λ) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  rcases hz₁.2 with ⟨w₁, hw₁FT, rfl⟩
  rcases hz₂.2 with ⟨w₂, hw₂FT, rfl⟩
  refine ⟨?_, ?_⟩
  · exact (permutedForwardTube_convex (d := d) (n := n) σ⁻¹) hz₁.1 hz₂.1 ha hb hab
  · refine ⟨a • w₁ + b • w₂, forwardTube_convex hw₁FT hw₂FT ha hb hab, ?_⟩
    have hlin :
        complexLorentzAction Λ (a • w₁ + b • w₂)
          = a • complexLorentzAction Λ w₁ + b • complexLorentzAction Λ w₂ := by
      ext k μ
      simp only [complexLorentzAction, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      trans (↑a * ∑ ν, Λ.val μ ν * w₁ k ν +
          ↑b * ∑ ν, Λ.val μ ν * w₂ k ν)
      · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ν _
        simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
        ring_nf
      · rfl
    simp [hlin]

/-- Fixed-`Λ` seed slices are preconnected. -/
theorem permSeedSlice_isPreconnected
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    IsPreconnected (permSeedSlice (d := d) n σ Λ) :=
  (permSeedSlice_convex (d := d) n σ Λ).isPreconnected

/-- Decompose the seed set as a union of fixed-`Λ` slices. -/
theorem permSeedSet_eq_iUnion_seedSlice
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permSeedSet (d := d) n σ =
      ⋃ Λ : ComplexLorentzGroup d, permSeedSlice (d := d) n σ Λ := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz.1 with ⟨Λ, w, hwFT, rfl⟩
    refine Set.mem_iUnion.mpr ⟨Λ, ?_⟩
    exact ⟨hz.2, ⟨w, hwFT, rfl⟩⟩
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨Λ, hzΛ⟩
    rcases hzΛ.2 with ⟨w, hwFT, rfl⟩
    refine ⟨?_, hzΛ.1⟩
    exact Set.mem_iUnion.mpr ⟨Λ, w, hwFT, rfl⟩

/-- Permutation forward-overlap index set in a reusable public form. -/
def permForwardOverlapIndexSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Set (ComplexLorentzGroup d) :=
  {Λ : ComplexLorentzGroup d |
    ∃ w : Fin n → Fin (d + 1) → ℂ,
      w ∈ ForwardTube d n ∧
      complexLorentzAction Λ (permAct (d := d) σ w) ∈ ForwardTube d n}

/-- A fixed seed slice is nonempty iff the inverse Lorentz element belongs to
the permutation forward-overlap index set. -/
theorem permSeedSlice_nonempty_iff_inv_mem_permForwardOverlapIndexSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    (permSeedSlice (d := d) n σ Λ).Nonempty ↔
      Λ⁻¹ ∈ permForwardOverlapIndexSet (d := d) n σ := by
  constructor
  · rintro ⟨z, hzσFT, hzimg⟩
    rcases hzimg with ⟨u, huFT, hzu⟩
    have hzσ : (fun k => z (σ⁻¹ k)) ∈ ForwardTube d n := by
      simpa [PermutedForwardTube] using hzσFT
    refine ⟨fun k => z (σ⁻¹ k), hzσ, ?_⟩
    have hperm_cancel : permAct (d := d) σ (fun k => z (σ⁻¹ k)) = z := by
      ext k μ
      simp [permAct]
    have hto :
        complexLorentzAction Λ⁻¹ (permAct (d := d) σ (fun k => z (σ⁻¹ k))) = u := by
      calc
        complexLorentzAction Λ⁻¹ (permAct (d := d) σ (fun k => z (σ⁻¹ k)))
            = complexLorentzAction Λ⁻¹ z := by rw [hperm_cancel]
        _ = complexLorentzAction Λ⁻¹ (complexLorentzAction Λ u) := by rw [hzu.symm]
        _ = u := by rw [complexLorentzAction_inv]
    exact hto ▸ huFT
  · rintro ⟨w, hwFT, hΛσwFT⟩
    refine ⟨permAct (d := d) σ w, ?_, ?_⟩
    · show permAct (d := d) σ w ∈ PermutedForwardTube d n σ⁻¹
      change (fun k => (permAct (d := d) σ w) (σ⁻¹ k)) ∈ ForwardTube d n
      simpa [permAct] using hwFT
    · refine ⟨complexLorentzAction Λ⁻¹ (permAct (d := d) σ w), hΛσwFT, ?_⟩
      have hcancel :
          complexLorentzAction Λ (complexLorentzAction Λ⁻¹ (permAct (d := d) σ w)) =
            permAct (d := d) σ w := by
        simpa using
          (complexLorentzAction_inv (n := n) (Λ := Λ⁻¹) (z := permAct (d := d) σ w))
      exact hcancel

/-- Permutation map continuity helper. -/
private lemma continuous_permAct
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Continuous (permAct (d := d) σ) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (σ k))

/-- The seed set is the image of the forward-overlap base under `permAct σ`. -/
theorem permSeedSet_eq_image_permForwardOverlapSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permSeedSet (d := d) n σ =
      (permAct (d := d) σ) '' (permForwardOverlapSet (d := d) n σ) := by
  ext z
  constructor
  · rintro ⟨hzET, hzPFT⟩
    refine ⟨permAct (d := d) σ⁻¹ z, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa [PermutedForwardTube, permAct] using hzPFT
      · have hperm_cancel : permAct (d := d) σ (permAct (d := d) σ⁻¹ z) = z := by
          ext k μ
          simp [permAct]
        simpa [hperm_cancel] using hzET
    · ext k μ
      simp [permAct]
  · rintro ⟨w, hwov, rfl⟩
    refine ⟨hwov.2, ?_⟩
    show (fun k => (permAct (d := d) σ w) (σ⁻¹ k)) ∈ ForwardTube d n
    simpa [permAct] using hwov.1

/-- The forward-overlap base is the image of the seed set under `permAct σ⁻¹`. -/
theorem permForwardOverlapSet_eq_image_permSeedSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permForwardOverlapSet (d := d) n σ =
      (permAct (d := d) σ⁻¹) '' (permSeedSet (d := d) n σ) := by
  ext w
  constructor
  · intro hw
    refine ⟨permAct (d := d) σ w, ?_, ?_⟩
    · exact ⟨hw.2, by
        show (fun k => (permAct (d := d) σ w) (σ⁻¹ k)) ∈ ForwardTube d n
        simpa [permAct] using hw.1⟩
    · ext k μ
      simp [permAct]
  · rintro ⟨z, hz, hzw⟩
    rcases hz with ⟨hzET, hzPFT⟩
    have hw_eq' : permAct (d := d) σ⁻¹ z = w := by
      simpa using hzw
    have hz_repr : z = permAct (d := d) σ w := by
      calc
        z = permAct (d := d) σ (permAct (d := d) σ⁻¹ z) := by
              ext k μ
              simp [permAct]
        _ = permAct (d := d) σ w := by rw [hw_eq']
    refine ⟨?_, ?_⟩
    · simpa [hz_repr, PermutedForwardTube, permAct] using hzPFT
    · simpa [hz_repr, permAct] using hzET

/-- Nonemptiness is equivalent between seed and forward-overlap sets. -/
theorem permSeedSet_nonempty_iff_permForwardOverlapSet_nonempty
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permSeedSet (d := d) n σ).Nonempty ↔
      (permForwardOverlapSet (d := d) n σ).Nonempty := by
  constructor
  · intro hseed
    rcases hseed with ⟨z, hz⟩
    refine ⟨permAct (d := d) σ⁻¹ z, ?_⟩
    exact (permForwardOverlapSet_eq_image_permSeedSet (d := d) n σ).symm ▸
      Set.mem_image_of_mem _ hz
  · intro hfwd
    rcases hfwd with ⟨w, hw⟩
    refine ⟨permAct (d := d) σ w, ?_⟩
    exact (permSeedSet_eq_image_permForwardOverlapSet (d := d) n σ).symm ▸
      Set.mem_image_of_mem _ hw

/-- Connectedness equivalence between seed set and forward-overlap base. -/
theorem isConnected_permSeedSet_iff_permForwardOverlapSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsConnected (permSeedSet (d := d) n σ) ↔
      IsConnected (permForwardOverlapSet (d := d) n σ) := by
  constructor
  · intro hseed
    have hcont : Continuous (permAct (d := d) σ⁻¹) :=
      continuous_permAct (d := d) n σ⁻¹
    have himage :
        IsConnected ((permAct (d := d) σ⁻¹) '' (permSeedSet (d := d) n σ)) :=
      hseed.image _ hcont.continuousOn
    simpa [permForwardOverlapSet_eq_image_permSeedSet (d := d) n σ] using himage
  · intro hfwd
    have hcont : Continuous (permAct (d := d) σ) :=
      continuous_permAct (d := d) n σ
    have himage :
        IsConnected ((permAct (d := d) σ) '' (permForwardOverlapSet (d := d) n σ)) :=
      hfwd.image _ hcont.continuousOn
    simpa [permSeedSet_eq_image_permForwardOverlapSet (d := d) n σ] using himage

end BHW
