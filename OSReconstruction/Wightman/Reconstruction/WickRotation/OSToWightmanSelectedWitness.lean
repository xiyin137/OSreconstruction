import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.EdgeDistribution
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeMonodromy
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues

/-!
# Selected OS witness support

This file exposes small theorem-surface facts about the selected OS analytic
witness `bvt_F OS lgc`.  The facts here are already implicit in the boundary
value construction, but later OS-route PET/edge arguments need them as named
inputs.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ} [NeZero d]

/-! ### Selected edge data

The next Route-1 seam is the OS-side compact edge pairing input for finite
permutations.  The OS/BHW route constructs this data for adjacent
transpositions first; full permutation statements must then be obtained by an
adjacent-swap chain through PET, not by requiring real edge witnesses for every
permutation at once.
-/

/-- Selected OS edge data for adjacent transpositions at fixed public arity.

This is the construction target for the OS route.  It deliberately stores only
the exact adjacent data consumed by the non-circular
`BHW.extendF_perm_overlap_of_edgePairingEquality` theorem: connectedness of the
explicit adjacent ET/swap-ET overlap and compact-test equality on one nonempty
real-open edge slice. -/
structure SelectedAdjacentPermutationEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) : Prop where
  overlap_connected :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
              BHW.ExtendedTube d n}
  edge_witness :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∃ V : Set (NPointDomain d n),
        IsOpen V ∧ V.Nonempty ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
        (∀ x ∈ V,
          BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
            =
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)

/-- OS-side source data for the distributional Euclidean/Jost anchor consumed
by the corrected Hall-Wightman source theorem.

Unlike `SelectedAdjacentPermutationEdgeData`, this is a data-carrying packet:
it stores the actual real Jost patches and scalar-product uniqueness
environments needed to supply `BHW.SourceDistributionalAdjacentTubeAnchor` for
the selected OS analytic witness. -/
structure SelectedAdjacentDistributionalJostAnchorData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) where
  basePatch :
    (i : Fin n) → (hi : i.val + 1 < n) → Set (NPointDomain d n)
  basePatch_open :
    ∀ i hi, IsOpen (basePatch i hi)
  basePatch_nonempty :
    ∀ i hi, (basePatch i hi).Nonempty
  basePatch_jost :
    ∀ i hi x, x ∈ basePatch i hi → x ∈ BHW.JostSet d n
  basePatch_left_ET :
    ∀ i hi x, x ∈ basePatch i hi →
      BHW.realEmbed x ∈ BHW.ExtendedTube d n
  basePatch_right_ET :
    ∀ i hi x, x ∈ basePatch i hi →
      BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHW.ExtendedTube d n
  baseGramEnvironment :
    (i : Fin n) → (hi : i.val + 1 < n) → Set (Fin n → Fin n → ℝ)
  baseGramEnvironment_unique :
    ∀ i hi,
      BHW.sourceDistributionalUniquenessSetOnVariety d n
        (baseGramEnvironment i hi)
  baseGram_left_mem :
    ∀ i hi x, x ∈ basePatch i hi →
      BHW.sourceRealMinkowskiGram d n x ∈ baseGramEnvironment i hi
  baseGram_realized :
    ∀ i hi G, G ∈ baseGramEnvironment i hi →
      ∃ x ∈ basePatch i hi,
        BHW.sourceRealMinkowskiGram d n x = G
  baseCompactEq :
    ∀ i hi (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ basePatch i hi →
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
            φ x

private def realPerm (π : Equiv.Perm (Fin n))
    (x : NPointDomain d n) : NPointDomain d n :=
  fun k => x (π k)

omit [NeZero d] in
private theorem continuous_realPerm (π : Equiv.Perm (Fin n)) :
    Continuous (realPerm (d := d) π) := by
  apply continuous_pi
  intro k
  exact continuous_apply (π k)

/-- Reindex a selected adjacent OS anchor into the permutation-indexed source
anchor consumed by the corrected Hall-Wightman theorem. -/
def bvt_F_distributionalJostAnchor_of_selectedJostData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) := by
  refine
    { realPatch := ?realPatch
      realPatch_open := ?realPatch_open
      realPatch_nonempty := ?realPatch_nonempty
      realPatch_jost := ?realPatch_jost
      realPatch_left_sector := ?realPatch_left_sector
      realPatch_right_sector := ?realPatch_right_sector
      gramEnvironment := ?gramEnvironment
      gramEnvironment_unique := ?gramEnvironment_unique
      gram_left_mem := ?gram_left_mem
      gram_environment_realized := ?gram_environment_realized
      gram_right_eq_perm_left := ?gram_right_eq_perm_left
      compact_branch_eq := ?compact_branch_eq }
  · exact fun π i hi => {x | realPerm (d := d) π x ∈ hData.basePatch i hi}
  · intro π i hi
    exact (hData.basePatch_open i hi).preimage (continuous_realPerm (d := d) π)
  · intro π i hi
    rcases hData.basePatch_nonempty i hi with ⟨y, hy⟩
    refine ⟨realPerm (d := d) π.symm y, ?_⟩
    have hperm :
        realPerm (d := d) π (realPerm (d := d) π.symm y) = y := by
      ext k μ
      simp [realPerm]
    simpa [hperm] using hy
  · intro π i hi x hx
    have hy := hData.basePatch_jost i hi (realPerm (d := d) π x) hx
    simpa [realPerm] using
      BHW.jostSet_permutation_invariant (d := d) (n := n) π.symm hy
  · intro π i hi x hx
    have hy := hData.basePatch_left_ET i hi (realPerm (d := d) π x) hx
    simpa [BHW.permutedExtendedTubeSector, realPerm] using hy
  · intro π i hi x hx
    have hy := hData.basePatch_right_ET i hi (realPerm (d := d) π x) hx
    simpa [BHW.permutedExtendedTubeSector, realPerm, Equiv.Perm.mul_apply]
      using hy
  · exact fun _π i hi => hData.baseGramEnvironment i hi
  · exact fun _π i hi => hData.baseGramEnvironment_unique i hi
  · intro π i hi x hx
    simpa [realPerm] using
      hData.baseGram_left_mem i hi (realPerm (d := d) π x) hx
  · intro π i hi G hG
    rcases hData.baseGram_realized i hi G hG with ⟨y, hy, hG_y⟩
    refine ⟨realPerm (d := d) π.symm y, ?_, ?_⟩
    · have hperm :
          realPerm (d := d) π (realPerm (d := d) π.symm y) = y := by
        ext k μ
        simp [realPerm]
      simpa [hperm] using hy
    · simpa [realPerm] using hG_y
  · intro π i hi x hx
    ext a b
    simp [BHW.sourceRealMinkowskiGram, BHW.sourcePermuteGram,
      Equiv.Perm.mul_apply]
  · intro π i hi φ hφ_compact hφ_tsupport
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let ψ : SchwartzNPoint d n := BHW.permuteSchwartz (d := d) π.symm φ
    have hψ_compact :
        HasCompactSupport (ψ : NPointDomain d n → ℂ) :=
      BHW.permuteSchwartz_hasCompactSupport (d := d) π.symm φ
        (by simpa using hφ_compact)
    have hψ_tsupport :
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ hData.basePatch i hi := by
      intro y hy
      have hyφ :
          realPerm (d := d) π.symm y ∈
            tsupport (φ : NPointDomain d n → ℂ) := by
        have hsupp_eq := BHW.tsupport_permuteSchwartz (d := d) π.symm φ
        rw [show ψ = BHW.permuteSchwartz (d := d) π.symm φ from rfl] at hy
        rw [hsupp_eq] at hy
        simpa [realPerm] using hy
      have hxPatch :
          realPerm (d := d) π (realPerm (d := d) π.symm y) ∈
            hData.basePatch i hi :=
        hφ_tsupport hyφ
      have hperm :
          realPerm (d := d) π (realPerm (d := d) π.symm y) = y := by
        ext k μ
        simp [realPerm]
      simpa [hperm] using hxPatch
    have hbase := hData.baseCompactEq i hi ψ hψ_compact hψ_tsupport
    have hleft :
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (fun k => BHW.realEmbed x (π k)) * φ x) =
          ∫ y : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed y) * ψ y := by
      simpa [ψ, realPerm] using
        BHW.integral_perm_eq_self (d := d) (n := n) π
          (fun y : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed y) * ψ y)
    have hright :
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (fun k => BHW.realEmbed x ((π * τ) k)) * φ x) =
          ∫ y : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => y (τ k))) * ψ y := by
      simpa [ψ, realPerm, τ, Equiv.Perm.mul_apply] using
        BHW.integral_perm_eq_self (d := d) (n := n) π
          (fun y : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => y (τ k))) * ψ y)
    exact hleft.trans (hbase.trans hright.symm)

/-- The richer selected OS/Jost anchor data supplies the compact real-edge part
of `SelectedAdjacentPermutationEdgeData`; the only extra input needed for the
selected edge packet is the connectedness of the corresponding adjacent
extended-tube overlap. -/
theorem bvt_F_selectedAdjacentPermutationEdgeData_of_selectedJostData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hOverlap :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        IsConnected
          {z : Fin n → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d n ∧
              BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
                BHW.ExtendedTube d n})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n) :
    SelectedAdjacentPermutationEdgeData OS lgc n := by
  refine
    { overlap_connected := ?overlap_connected
      edge_witness := ?edge_witness }
  · exact hOverlap
  · intro i hi
    refine
      ⟨hData.basePatch i hi,
        hData.basePatch_open i hi,
        hData.basePatch_nonempty i hi,
        ?left_ET,
        ?right_ET,
        ?compact_eq⟩
    · intro x hx
      exact hData.basePatch_left_ET i hi x hx
    · intro x hx
      exact hData.basePatch_right_ET i hi x hx
    · intro φ hφ_compact hφ_tsupport
      exact (hData.baseCompactEq i hi φ hφ_compact hφ_tsupport).symm

omit [NeZero d] in
/-- Existing BHW adjacent-overlap geometry supplies the exact connectedness
field needed by `SelectedAdjacentPermutationEdgeData`, once the corresponding
forward-overlap slice is known connected. -/
theorem bvt_selectedAdjacentOverlap_connected_of_forwardOverlapConnected
    (n : ℕ)
    (hFwd :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        IsConnected (BHW.adjSwapForwardOverlapSet (d := d) n i hi)) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
              BHW.ExtendedTube d n} := by
  intro i hi
  have hconn :
      IsConnected (BHW.adjSwapExtendedOverlapSet (d := d) n i hi) :=
    BHW.isConnected_adjSwapExtendedOverlap_of_forwardOverlapConnected
      (d := d) n i hi (hFwd i hi)
  simpa [BHW.adjSwapExtendedOverlapSet, BHW.permAct] using hconn

omit [NeZero d] in
/-- The existing pure BHW `permSeedSet` connectedness blocker gives the adjacent
ET-overlap connectedness needed by the selected OS edge packet.  This theorem
introduces no new trust boundary; it only reuses the current geometric blocker
under the adjacent-transposition specialization. -/
theorem bvt_selectedAdjacentOverlap_connected_of_permSeedGeometry
    (n : ℕ) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
              BHW.ExtendedTube d n} := by
  refine
    bvt_selectedAdjacentOverlap_connected_of_forwardOverlapConnected
      (d := d) n ?_
  intro i hi
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hn : ¬ n ≤ 1 := by
    omega
  have hτ_ne : τ ≠ 1 := by
    intro hτ
    let ip1 : Fin n := ⟨i.val + 1, hi⟩
    have hip1_ne_i : ip1 ≠ i := by
      intro h
      have hval := congrArg Fin.val h
      simp [ip1] at hval
    have happly := congrArg (fun σ : Equiv.Perm (Fin n) => σ i) hτ
    exact hip1_ne_i (by simpa [τ, ip1] using happly)
  have hseed :
      IsConnected (BHW.permSeedSet (d := d) n τ) :=
    BHW.blocker_isConnected_permSeedSet_nontrivial
      (d := d) n τ hτ_ne hn
  have hfwd :
      IsConnected (BHW.permForwardOverlapSet (d := d) n τ) :=
    (BHW.isConnected_permSeedSet_iff_permForwardOverlapSet
      (d := d) n τ).mp hseed
  simpa [BHW.permForwardOverlapSet, BHW.adjSwapForwardOverlapSet, τ, BHW.permAct]
    using hfwd

/-- The selected OS/Jost anchor data supplies the selected adjacent edge packet,
with adjacent-overlap connectedness discharged by the existing BHW pure-geometry
blocker. -/
theorem bvt_F_selectedAdjacentPermutationEdgeData_of_selectedJostData_and_permSeedGeometry
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n) :
    SelectedAdjacentPermutationEdgeData OS lgc n := by
  exact
    bvt_F_selectedAdjacentPermutationEdgeData_of_selectedJostData
      (d := d) OS lgc n
      (bvt_selectedAdjacentOverlap_connected_of_permSeedGeometry (d := d) n)
      hData

/-- Overstrong all-permutation edge data at fixed public arity.

This is a conditional helper only, not the OS-route construction target:
arbitrary permutations can have no nonempty real edge overlap in high arity.
The active route should construct `SelectedAdjacentPermutationEdgeData` and then
derive general branch independence by an adjacent-swap chain. -/
structure SelectedAllPermutationEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) : Prop where
  overlap_connected :
    ∀ σ : Equiv.Perm (Fin n),
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n}
  edge_witness :
    ∀ σ : Equiv.Perm (Fin n),
      ∃ V : Set (NPointDomain d n),
        IsOpen V ∧ V.Nonempty ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
        (∀ x ∈ V,
          BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed (fun k => x (σ k))) * φ x
            =
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)

/-- The selected OS analytic witness is invariant under restricted real Lorentz
transformations on the forward tube. -/
theorem bvt_F_restrictedLorentzInvariant_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      bvt_F OS lgc n
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
      bvt_F OS lgc n z := by
  intro Λ z hz
  have hF_holo_BHW :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_dist_BHW :
      ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (hdet : R.det = 1) (horth : R.transpose * R = 1)
        (ψ : SchwartzNPoint d n),
          HasCompactSupport (ψ : NPointDomain d n → ℂ) →
          tsupport (ψ : NPointDomain d n → ℂ) ⊆
            {x : NPointDomain d n |
              (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n ∧
                BHW.complexLorentzAction
                  (ComplexLorentzGroup.ofEuclidean R hdet horth)
                  (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n} →
          ∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (BHW.complexLorentzAction
                  (ComplexLorentzGroup.ofEuclidean R hdet horth)
                  (fun k => wickRotatePoint (x k))) * ψ x
            =
          ∫ x : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * ψ x := by
    intro R hdet horth ψ hψ_compact hψ_tsupport
    refine bvt_F_ofEuclidean_wick_pairing
      (d := d) OS lgc n R hdet horth ψ hψ_compact ?_
    intro x hx
    rcases hψ_tsupport hx with ⟨hx0, hx1⟩
    constructor
    · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx0
    · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx1
  have hz_BHW : z ∈ BHW.ForwardTube d n := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz
  exact
    BHW.Task5Bridge.real_lorentz_invariance_from_euclidean_distributional
      (d := d) n (bvt_F OS lgc n) hF_holo_BHW hF_dist_BHW Λ z hz_BHW

/-- Restricted real Lorentz invariance analytically continues to complex
Lorentz invariance on the forward-tube overlap. -/
theorem bvt_F_complexLorentzInvariant_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n →
      BHW.complexLorentzAction Λ z ∈ ForwardTube d n →
      bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
        bvt_F OS lgc n z := by
  intro Λ z hz hΛz
  have hF_hol_BHW :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hreal_BHW :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  exact
    BHW.complex_lorentz_invariance
      (d := d) n (bvt_F OS lgc n)
      hF_hol_BHW
      hreal_BHW
      Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)

/-- Selected compact edge data propagates to pointwise equality of the selected
`extendF` branches on the whole adjacent ET/swap-ET overlap. -/
theorem bvt_F_extendF_adjacent_overlap_of_selectedEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d n)
    (hswapz :
      BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
        BHW.ExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z) =
      BHW.extendF (bvt_F OS lgc n) z := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rcases hEdge.edge_witness i hi with
    ⟨V, hV_open, hV_ne, hV_ET, hV_permET, hPairing⟩
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  have hOverlap := hEdge.overlap_connected i hi
  exact
    BHW.extendF_perm_overlap_of_edgePairingEquality
      (d := d) n (bvt_F OS lgc n) hF_holo hF_lorentz τ
      (by simpa [τ] using hOverlap)
      V hV_open hV_ne hV_ET
      (by intro x hx; simpa [τ] using hV_permET x hx)
      (by
        intro φ hφ_compact hφ_tsupport
        simpa [τ] using hPairing φ hφ_compact hφ_tsupport)
      z hz
      (by simpa [τ] using hswapz)

/-! ### Selected PET branch cover

The adjacent route works first branch-by-branch on the explicit PET cover
`BHW.permutedExtendedTubeSector d n π`.  The theorem
`bvt_selectedPETBranch_adjacent_eq_on_sector_overlap` is the checked local
compatibility datum that the later global PET gluing/monodromy step must
propagate through the finite adjacent-swap sector graph.
-/

/-- The selected `π`-branch on the explicit PET sector
`{z | z ∘ π ∈ ExtendedTube}`. -/
noncomputable def bvt_selectedPETBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z => BHW.extendF (bvt_F OS lgc n) (fun k => z (π k))

/-- Each selected PET branch is holomorphic on its explicit sector. -/
theorem bvt_selectedPETBranch_holomorphicOn_sector
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (bvt_selectedPETBranch (d := d) OS lgc n π)
      (BHW.permutedExtendedTubeSector d n π) := by
  intro z hz
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
          bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hExt_at :
      DifferentiableAt ℂ (BHW.extendF (bvt_F OS lgc n)) (fun k => z (π k)) := by
    exact
      ((BHW.extendF_holomorphicOn n (bvt_F OS lgc n) hF_holo hF_cinv)
        (fun k => z (π k)) hz).differentiableAt
        (BHW.isOpen_extendedTube.mem_nhds hz)
  have hperm_diff :
      Differentiable ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π k)) :=
    differentiable_pi.mpr fun k => differentiable_apply (π k)
  have hbranch_at :
      DifferentiableAt ℂ
        (fun w => BHW.extendF (bvt_F OS lgc n) (fun k => w (π k))) z := by
    simpa [Function.comp_def] using hExt_at.comp z hperm_diff.differentiableAt
  simpa [bvt_selectedPETBranch] using hbranch_at.differentiableWithinAt

/-- Adjacent selected branches agree on the overlap of the corresponding PET
sectors.  This is the branch-cover compatibility datum supplied by adjacent
edge data. -/
theorem bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzπswap :
      z ∈ BHW.permutedExtendedTubeSector d n
        (π * Equiv.swap i ⟨i.val + 1, hi⟩)) :
    bvt_selectedPETBranch (d := d) OS lgc n
        (π * Equiv.swap i ⟨i.val + 1, hi⟩) z =
      bvt_selectedPETBranch (d := d) OS lgc n π z := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let y : Fin n → Fin (d + 1) → ℂ := fun k => z (π k)
  have hy : y ∈ BHW.ExtendedTube d n := by
    simpa [BHW.permutedExtendedTubeSector, y] using hzπ
  have hτy : BHW.permAct (d := d) τ y ∈ BHW.ExtendedTube d n := by
    simpa [BHW.permutedExtendedTubeSector, BHW.permAct, y, τ, Equiv.Perm.mul_apply]
      using hzπswap
  have hmain :=
    bvt_F_extendF_adjacent_overlap_of_selectedEdgeData
      (d := d) OS lgc n hEdge i hi y hy hτy
  simpa [bvt_selectedPETBranch, BHW.permAct, y, τ, Equiv.Perm.mul_apply] using hmain

/-- If the complex Lorentz orbit of every forward-tube point hits a
Cayley-connected family of permuted-forward-tube chambers, then the selected
OS adjacent overlap equalities promote to full PET branch independence.  This
is the theorem-2-facing reuse point of the existing BHW monodromy
infrastructure. -/
theorem bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π →
      z ∈ BHW.permutedExtendedTubeSector d n ρ →
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k)) := by
  refine
    BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected
      (d := d) (n := n) (bvt_F OS lgc n) ?_ hOrbit
  intro π i hi z hzπ hzπswap
  simpa [bvt_selectedPETBranch] using
    bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
      (d := d) OS lgc n hEdge π i hi z hzπ hzπswap

/-- Selected adjacent OS edge data gives the BHW forward-tube permutation
invariance conclusion, once the PET sector-fiber geometry is supplied.  This
is the non-circular selected-witness replacement for the old BHW use of
`IsAdjacentLocallyCommutativeWeak`. -/
theorem bvt_F_permutation_invariance_of_selectedAdjacentEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ)
    {w : Fin n → Fin (d + 1) → ℂ}
    (hw : w ∈ BHW.ForwardTube d n)
    {τ : Equiv.Perm (Fin n)}
    {Γ : ComplexLorentzGroup d}
    (h :
      BHW.complexLorentzAction Γ (fun k => w (τ k)) ∈
        BHW.ForwardTube d n) :
    bvt_F OS lgc n
        (BHW.complexLorentzAction Γ (fun k => w (τ k))) =
      bvt_F OS lgc n w := by
  have hPET :=
    bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData
      (d := d) OS lgc n hEdge hOrbit
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  exact
    BHW.F_permutation_invariance_of_petBranchIndependence
      (d := d) n (bvt_F OS lgc n) hF_holo hF_lorentz hPET hw h

/-- Overstrong all-permutation compact edge data propagates to pointwise equality
of the selected `extendF` branches on the whole ET/permuted-ET overlap.

This lemma is useful only under the explicit all-permutation hypothesis; the
OS route should not try to construct that hypothesis directly. -/
theorem bvt_F_extendF_perm_overlap_of_selectedEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAllPermutationEdgeData OS lgc n)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d n)
    (hσz : BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) σ z) =
      BHW.extendF (bvt_F OS lgc n) z := by
  rcases hEdge.edge_witness σ with
    ⟨V, hV_open, hV_ne, hV_ET, hV_permET, hPairing⟩
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  exact
    BHW.extendF_perm_overlap_of_edgePairingEquality
      (d := d) n (bvt_F OS lgc n) hF_holo hF_lorentz σ
      (hEdge.overlap_connected σ) V hV_open hV_ne hV_ET hV_permET
      hPairing z hz hσz

/-! ### Selected glued absolute PET scalar

Using the overlap equality above, the selected `extendF` branches have a
well-defined value on the whole permuted extended tube.  This is still an
absolute-coordinate PET scalar; the later reduced theorem must prove/descent
the corresponding quotient package.
-/

/-- Selected absolute PET scalar obtained by choosing a permutation branch and
evaluating the ordinary selected `extendF` there.  It is zero off PET only so it
can be used as a total ambient function; the meaningful theorems below are
PET-local. -/
noncomputable def bvt_selectedAbsolutePETGluedValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if hz : z ∈ BHW.PermutedExtendedTube d n then
      BHW.extendF (bvt_F OS lgc n)
        (fun k => z (BHW.permutedExtendedTubeBranch (d := d) (n := n) z hz k))
    else
      0

/-- Adjacent selected edge data plus PET sector-fiber connectivity makes the
selected glued PET scalar independent of the chosen branch. -/
theorem bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_selectedAdjacentEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hπz : (fun k => z (π k)) ∈ BHW.ExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) := by
  have hzPET : z ∈ BHW.PermutedExtendedTube d n := by
    rw [BHW.mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube]
    exact ⟨π, hπz⟩
  let π₀ : Equiv.Perm (Fin n) :=
    BHW.permutedExtendedTubeBranch (d := d) (n := n) z hzPET
  have hπ₀z : (fun k => z (π₀ k)) ∈ BHW.ExtendedTube d n := by
    simpa [π₀] using
      BHW.permutedExtendedTubeBranch_mem_extendedTube
        (d := d) (n := n) z hzPET
  have hzπ₀ : z ∈ BHW.permutedExtendedTubeSector d n π₀ := by
    simpa [π₀, BHW.permutedExtendedTubeSector] using hπ₀z
  have hzπ : z ∈ BHW.permutedExtendedTubeSector d n π := by
    simpa [BHW.permutedExtendedTubeSector] using hπz
  have hPET :=
    bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData
      (d := d) OS lgc n hEdge hOrbit
  have hbranch :
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) :=
    hPET π₀ π z hzπ₀ hzπ
  unfold bvt_selectedAbsolutePETGluedValue
  simp only [dif_pos hzPET]
  exact hbranch

/-- On the original forward tube, the selected glued PET scalar built from
adjacent edge data agrees with the selected OS witness. -/
theorem bvt_selectedAbsolutePETGluedValue_eq_bvt_F_on_forwardTube_of_selectedAdjacentEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ForwardTube d n) :
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z =
      bvt_F OS lgc n z := by
  have hbranch :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_selectedAdjacentEdgeData
      (d := d) OS lgc n hEdge hOrbit (1 : Equiv.Perm (Fin n)) z
      (BHW.forwardTube_subset_extendedTube hz)
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  have hbranch' :
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z =
        BHW.extendF (bvt_F OS lgc n) z := by
    simpa using hbranch
  have hext :
      BHW.extendF (bvt_F OS lgc n) z = bvt_F OS lgc n z :=
    BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_lorentz z hz
  exact hbranch'.trans hext

/-- Adjacent selected edge data plus PET sector-fiber connectivity makes the
selected glued absolute PET scalar holomorphic on the permuted extended tube. -/
theorem bvt_selectedAbsolutePETGluedValue_holomorphicOn_PET_of_selectedAdjacentEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    DifferentiableOn ℂ
      (bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n)
      (BHW.PermutedExtendedTube d n) := by
  intro z hzPET
  let π₀ : Equiv.Perm (Fin n) :=
    BHW.permutedExtendedTubeBranch (d := d) (n := n) z hzPET
  have hπ₀z : (fun k => z (π₀ k)) ∈ BHW.ExtendedTube d n := by
    simpa [π₀] using
      BHW.permutedExtendedTubeBranch_mem_extendedTube
        (d := d) (n := n) z hzPET
  have hperm_cont :
      Continuous
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π₀ k)) := by
    refine continuous_pi ?_
    intro k
    exact continuous_apply (π₀ k)
  have hEq :
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n =ᶠ[𝓝 z]
        fun w => BHW.extendF (bvt_F OS lgc n) (fun k => w (π₀ k)) := by
    filter_upwards
      [(BHW.isOpen_extendedTube.preimage hperm_cont).mem_nhds hπ₀z] with w hw
    exact
      bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_selectedAdjacentEdgeData
        (d := d) OS lgc n hEdge hOrbit π₀ w hw
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
          bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hExt_at :
      DifferentiableAt ℂ (BHW.extendF (bvt_F OS lgc n)) (fun k => z (π₀ k)) := by
    exact
      ((BHW.extendF_holomorphicOn n (bvt_F OS lgc n) hF_holo hF_cinv)
        (fun k => z (π₀ k)) hπ₀z).differentiableAt
        (BHW.isOpen_extendedTube.mem_nhds hπ₀z)
  have hperm_diff :
      Differentiable ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π₀ k)) :=
    differentiable_pi.mpr fun k => differentiable_apply (π₀ k)
  have hperm_at :
      DifferentiableAt ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π₀ k)) z :=
    hperm_diff.differentiableAt
  have hbranch_at :
      DifferentiableAt ℂ
        (fun w => BHW.extendF (bvt_F OS lgc n) (fun k => w (π₀ k))) z :=
    by
      simpa [Function.comp_def] using hExt_at.comp z hperm_at
  exact (hEq.differentiableAt_iff.mpr hbranch_at).differentiableWithinAt

/-- Adjacent selected edge data plus PET sector-fiber connectivity makes the
selected glued absolute PET scalar invariant under complex Lorentz
transformations on PET. -/
theorem bvt_selectedAbsolutePETGluedValue_lorentzInvariant_of_selectedAdjacentEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ)
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n
        (BHW.complexLorentzAction Λ z) =
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z := by
  let π₀ : Equiv.Perm (Fin n) :=
    BHW.permutedExtendedTubeBranch (d := d) (n := n) z hz
  have hπ₀z : (fun k => z (π₀ k)) ∈ BHW.ExtendedTube d n := by
    simpa [π₀] using
      BHW.permutedExtendedTubeBranch_mem_extendedTube
        (d := d) (n := n) z hz
  have hπ₀Λz :
      (fun k => BHW.complexLorentzAction Λ z (π₀ k)) ∈
        BHW.ExtendedTube d n := by
    have hΛπ₀z :=
      BHW.complexLorentzAction_mem_extendedTube
        (d := d) n Λ hπ₀z
    simpa [BHW.lorentz_perm_commute] using hΛπ₀z
  have hleft :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_selectedAdjacentEdgeData
      (d := d) OS lgc n hEdge hOrbit π₀
      (BHW.complexLorentzAction Λ z) hπ₀Λz
  have hright :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_selectedAdjacentEdgeData
      (d := d) OS lgc n hEdge hOrbit π₀ z hπ₀z
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  have hExt :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.complexLorentzAction Λ (fun k => z (π₀ k))) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) :=
    BHW.extendF_complex_lorentz_invariant n (bvt_F OS lgc n)
      hF_holo hF_lorentz Λ (fun k => z (π₀ k)) hπ₀z
  calc
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n
        (BHW.complexLorentzAction Λ z)
        = BHW.extendF (bvt_F OS lgc n)
            (fun k => BHW.complexLorentzAction Λ z (π₀ k)) := hleft
    _ = BHW.extendF (bvt_F OS lgc n)
          (BHW.complexLorentzAction Λ (fun k => z (π₀ k))) := by
            congr 1
    _ = BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) := hExt
    _ = bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z := hright.symm

/-- Adjacent selected edge data plus PET sector-fiber connectivity makes the
selected glued absolute PET scalar invariant under finite coordinate
permutations on PET. -/
theorem bvt_selectedAbsolutePETGluedValue_permInvariant_of_selectedAdjacentEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ →
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n
        (fun k => z (σ k)) =
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z := by
  let π₀ : Equiv.Perm (Fin n) :=
    BHW.permutedExtendedTubeBranch (d := d) (n := n) z hz
  have hπ₀z : (fun k => z (π₀ k)) ∈ BHW.ExtendedTube d n := by
    simpa [π₀] using
      BHW.permutedExtendedTubeBranch_mem_extendedTube
        (d := d) (n := n) z hz
  have hperm_apply :
      (fun k => (fun j => z (σ j)) ((σ⁻¹ * π₀) k)) =
        fun k => z (π₀ k) := by
    ext k μ
    simp [Equiv.Perm.mul_apply]
  have hleft :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_selectedAdjacentEdgeData
      (d := d) OS lgc n hEdge hOrbit (σ⁻¹ * π₀) (fun k => z (σ k))
      (by
        rw [hperm_apply]
        exact hπ₀z)
  have hright :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_selectedAdjacentEdgeData
      (d := d) OS lgc n hEdge hOrbit π₀ z hπ₀z
  have hleft' :
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n
          (fun k => z (σ k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) := by
    simpa [hperm_apply] using hleft
  exact hleft'.trans hright.symm

/-- The selected glued PET scalar is independent of the chosen branch: on any
permutation branch landing in ET, it equals that branch's `extendF` value. -/
theorem bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAllPermutationEdgeData OS lgc n)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hπz : (fun k => z (π k)) ∈ BHW.ExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) := by
  have hzPET : z ∈ BHW.PermutedExtendedTube d n := by
    rw [BHW.mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube]
    exact ⟨π, hπz⟩
  let π₀ : Equiv.Perm (Fin n) :=
    BHW.permutedExtendedTubeBranch (d := d) (n := n) z hzPET
  have hπ₀z : (fun k => z (π₀ k)) ∈ BHW.ExtendedTube d n := by
    simpa [π₀] using
      BHW.permutedExtendedTubeBranch_mem_extendedTube
        (d := d) (n := n) z hzPET
  have hperm_apply :
      BHW.permAct (d := d) (π₀⁻¹ * π) (fun k => z (π₀ k)) =
        fun k => z (π k) := by
    ext k μ
    simp [BHW.permAct, Equiv.Perm.mul_apply]
  have hcompat :=
    bvt_F_extendF_perm_overlap_of_selectedEdgeData
      (d := d) OS lgc n hEdge (π₀⁻¹ * π) (fun k => z (π₀ k))
      hπ₀z
      (by
        rw [hperm_apply]
        exact hπz)
  have hbranch :
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) := by
    simpa [hperm_apply] using hcompat
  unfold bvt_selectedAbsolutePETGluedValue
  simp only [dif_pos hzPET]
  change BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) =
    BHW.extendF (bvt_F OS lgc n) (fun k => z (π k))
  exact hbranch.symm

/-- On the original forward tube, the selected glued PET scalar agrees with the
selected OS witness. -/
theorem bvt_selectedAbsolutePETGluedValue_eq_bvt_F_on_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAllPermutationEdgeData OS lgc n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ForwardTube d n) :
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z =
      bvt_F OS lgc n z := by
  have hbranch :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
      (d := d) OS lgc n hEdge (1 : Equiv.Perm (Fin n)) z
      (BHW.forwardTube_subset_extendedTube hz)
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  have hext :
      BHW.extendF (bvt_F OS lgc n) z = bvt_F OS lgc n z :=
    BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_lorentz z hz
  simpa using hbranch.trans hext

/-- The selected glued absolute PET scalar is holomorphic on the permuted
extended tube. -/
theorem bvt_selectedAbsolutePETGluedValue_holomorphicOn_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAllPermutationEdgeData OS lgc n) :
    DifferentiableOn ℂ
      (bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n)
      (BHW.PermutedExtendedTube d n) := by
  intro z hzPET
  let π₀ : Equiv.Perm (Fin n) :=
    BHW.permutedExtendedTubeBranch (d := d) (n := n) z hzPET
  have hπ₀z : (fun k => z (π₀ k)) ∈ BHW.ExtendedTube d n := by
    simpa [π₀] using
      BHW.permutedExtendedTubeBranch_mem_extendedTube
        (d := d) (n := n) z hzPET
  have hperm_cont :
      Continuous
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π₀ k)) := by
    refine continuous_pi ?_
    intro k
    exact continuous_apply (π₀ k)
  have hEq :
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n =ᶠ[𝓝 z]
        fun w => BHW.extendF (bvt_F OS lgc n) (fun k => w (π₀ k)) := by
    filter_upwards
      [(BHW.isOpen_extendedTube.preimage hperm_cont).mem_nhds hπ₀z] with w hw
    exact
      bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
        (d := d) OS lgc n hEdge π₀ w hw
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
          bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hExt_at :
      DifferentiableAt ℂ (BHW.extendF (bvt_F OS lgc n)) (fun k => z (π₀ k)) := by
    exact
      ((BHW.extendF_holomorphicOn n (bvt_F OS lgc n) hF_holo hF_cinv)
        (fun k => z (π₀ k)) hπ₀z).differentiableAt
        (BHW.isOpen_extendedTube.mem_nhds hπ₀z)
  have hperm_diff :
      Differentiable ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π₀ k)) :=
    differentiable_pi.mpr fun k => differentiable_apply (π₀ k)
  have hperm_at :
      DifferentiableAt ℂ
        (fun w : Fin n → Fin (d + 1) → ℂ => fun k => w (π₀ k)) z :=
    hperm_diff.differentiableAt
  have hbranch_at :
      DifferentiableAt ℂ
        (fun w => BHW.extendF (bvt_F OS lgc n) (fun k => w (π₀ k))) z :=
    by
      simpa [Function.comp_def] using hExt_at.comp z hperm_at
  exact (hEq.differentiableAt_iff.mpr hbranch_at).differentiableWithinAt

/-- The selected glued absolute PET scalar is invariant under complex Lorentz
transformations on PET. -/
theorem bvt_selectedAbsolutePETGluedValue_lorentzInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAllPermutationEdgeData OS lgc n)
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n
        (BHW.complexLorentzAction Λ z) =
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z := by
  let π₀ : Equiv.Perm (Fin n) :=
    BHW.permutedExtendedTubeBranch (d := d) (n := n) z hz
  have hπ₀z : (fun k => z (π₀ k)) ∈ BHW.ExtendedTube d n := by
    simpa [π₀] using
      BHW.permutedExtendedTubeBranch_mem_extendedTube
        (d := d) (n := n) z hz
  have hπ₀Λz :
      (fun k => BHW.complexLorentzAction Λ z (π₀ k)) ∈
        BHW.ExtendedTube d n := by
    have hΛπ₀z :=
      BHW.complexLorentzAction_mem_extendedTube
        (d := d) n Λ hπ₀z
    simpa [BHW.lorentz_perm_commute] using hΛπ₀z
  have hleft :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
      (d := d) OS lgc n hEdge π₀
      (BHW.complexLorentzAction Λ z) hπ₀Λz
  have hright :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
      (d := d) OS lgc n hEdge π₀ z hπ₀z
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  have hExt :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.complexLorentzAction Λ (fun k => z (π₀ k))) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) :=
    BHW.extendF_complex_lorentz_invariant n (bvt_F OS lgc n)
      hF_holo hF_lorentz Λ (fun k => z (π₀ k)) hπ₀z
  calc
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n
        (BHW.complexLorentzAction Λ z)
        = BHW.extendF (bvt_F OS lgc n)
            (fun k => BHW.complexLorentzAction Λ z (π₀ k)) := hleft
    _ = BHW.extendF (bvt_F OS lgc n)
          (BHW.complexLorentzAction Λ (fun k => z (π₀ k))) := by
            congr 1
    _ = BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) := hExt
    _ = bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z := hright.symm

/-- The selected glued absolute PET scalar is invariant under finite coordinate
permutations on PET. -/
theorem bvt_selectedAbsolutePETGluedValue_permInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAllPermutationEdgeData OS lgc n)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n
        (fun k => z (σ k)) =
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n z := by
  let π₀ : Equiv.Perm (Fin n) :=
    BHW.permutedExtendedTubeBranch (d := d) (n := n) z hz
  have hπ₀z : (fun k => z (π₀ k)) ∈ BHW.ExtendedTube d n := by
    simpa [π₀] using
      BHW.permutedExtendedTubeBranch_mem_extendedTube
        (d := d) (n := n) z hz
  have hperm_apply :
      (fun k => (fun j => z (σ j)) ((σ⁻¹ * π₀) k)) =
        fun k => z (π₀ k) := by
    ext k μ
    simp [Equiv.Perm.mul_apply]
  have hleft :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
      (d := d) OS lgc n hEdge (σ⁻¹ * π₀) (fun k => z (σ k))
      (by
        rw [hperm_apply]
        exact hπ₀z)
  have hright :=
    bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
      (d := d) OS lgc n hEdge π₀ z hπ₀z
  have hleft' :
      bvt_selectedAbsolutePETGluedValue (d := d) OS lgc n
          (fun k => z (σ k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (π₀ k)) := by
    simpa [hperm_apply] using hleft
  exact hleft'.trans hright.symm

/-! ### Selected Route-1 pre-pullback

The following absolute-coordinate function is the selected OS witness descended
to reduced difference coordinates and pulled back along `reducedDiffMap`.

This is only the Route-1 *preinput* pullback, not the selected PET extension:
away from the forward tube its values are just the total values of the original
forward-tube witness on the safe section, so no ET/PET extension property is
claimed here.  What it does provide, non-circularly, is the algebraic
translation-invariant core and its forward-tube comparison with `bvt_F`.
-/

/-- The selected OS Route-1 absolute pre-pullback at public arity `m + 1`. -/
noncomputable def bvt_route1AbsolutePrePullback
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ :=
  BHW.pullbackReducedExtension (d := d) (n := m + 1)
    (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun

/-- The selected Route-1 pre-pullback is invariant under uniform complex
translations, because it factors through reduced differences. -/
theorem bvt_route1AbsolutePrePullback_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    bvt_route1AbsolutePrePullback (d := d) OS lgc m
        (fun k μ => z k μ + c μ) =
      bvt_route1AbsolutePrePullback (d := d) OS lgc m z := by
  exact
    BHW.reduced_pullback_translation_invariant (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun z c

/-- On the forward tube, the selected Route-1 pre-pullback agrees with the selected
OS witness `bvt_F`. -/
theorem bvt_route1AbsolutePrePullback_eq_bvt_F_on_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1)) :
    bvt_route1AbsolutePrePullback (d := d) OS lgc m z =
      bvt_F OS lgc (m + 1) z := by
  exact
    BHW.descendAbsoluteForwardTubeInput_factorization (d := d) (m := m)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc m) z
      ((BHW_forwardTube_eq (d := d) (n := m + 1)) ▸ hz)

/-! ### Selected reduced boundary-value input

The selected OS witness also supplies the reduced boundary-value input needed by
the reduced BHW theorem.  This is independent of the PET gluing/locality seam:
it is just the absolute boundary-value theorem transported through the
basepoint/reduced-difference change of variables.
-/

/-- The selected reduced real-side Wightman family obtained by inserting a
normalized basepoint cutoff and testing the public `(m + 1)`-point `bvt_W`. -/
noncomputable def bvt_reducedWightmanFamily
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d) :
    (m : ℕ) → SchwartzNPoint d m → ℂ :=
  fun m φ => bvt_W OS lgc (m + 1) (BHW.reducedTestLift m d χ.toSchwartz φ)

/-- The descended selected preinput factors along the absolute approach points
used in the reduced boundary-value proof. -/
theorem bvt_selectedReducedPreInput_factorization_absoluteApproach
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (x₀ : SpacetimeDim d) (ξ η : Fin m → Fin (d + 1) → ℝ)
    (hη : η ∈ BHW.ProductForwardConeReal d m) {ε : ℝ} (hε : 0 < ε) :
    (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun
        (fun j μ => (ξ j μ : ℂ) + ε * (η j μ : ℂ) * Complex.I) =
      bvt_F OS lgc (m + 1)
        (BHW.absoluteApproachOfReduced d m x₀ ξ η ε) := by
  have hz :
      BHW.absoluteApproachOfReduced d m x₀ ξ η ε ∈
        BHW.ForwardTube d (m + 1) :=
    BHW.absoluteApproachOfReduced_mem_forwardTube (d := d) m x₀ ξ η hη hε
  have hred :=
    BHW.reducedDiffMap_absoluteApproachOfReduced (d := d) (m := m) x₀ ξ η ε
  have hfact :=
    BHW.descendAbsoluteForwardTubeInput_factorization (d := d) (m := m)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc m)
      (BHW.absoluteApproachOfReduced d m x₀ ξ η ε) hz
  rw [hred] at hfact
  exact hfact

/-- At fixed positive imaginary height, the selected reduced smeared boundary
integral equals the corresponding absolute `bvt_F` boundary integral after the
basepoint/reduced-difference change of variables. -/
theorem bvt_selectedReducedBoundaryIntegral_eq_absoluteBoundaryIntegral
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    ∀ (f : SchwartzNPoint d m) (η : Fin m → Fin (d + 1) → ℝ)
      (_hη : η ∈ BHW.ProductForwardConeReal d m) {ε : ℝ}, 0 < ε →
      ∫ x : NPointDomain d m,
        (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
          (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun
          (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x
        =
      ∫ x : NPointDomain d (m + 1),
        bvt_F OS lgc (m + 1)
          (fun k μ => (x k μ : ℂ) +
            ε * (BHW.absoluteDirectionOfReduced d m η k μ : ℂ) * Complex.I) *
          BHW.reducedTestLift m d χ.toSchwartz f x := by
  intro f η hη ε hε
  let G : NPointDomain d (m + 1) → ℂ := fun x =>
    bvt_F OS lgc (m + 1)
      (fun k μ => (x k μ : ℂ) +
        ε * (BHW.absoluteDirectionOfReduced d m η k μ : ℂ) * Complex.I) *
      BHW.reducedTestLift m d χ.toSchwartz f x
  have hG_int : MeasureTheory.Integrable G := by
    exact forward_tube_bv_integrable
      (bvt_F OS lgc (m + 1))
      (bvt_F_holomorphic OS lgc (m + 1))
      (full_analytic_continuation_with_acr_symmetry_growth
        OS lgc (m + 1)).choose_spec.2.2.2.2.2.2
      ⟨{ toLinearMap :=
          { toFun := bvt_W OS lgc (m + 1)
            map_add' := (bvt_W_linear OS lgc (m + 1)).map_add
            map_smul' := (bvt_W_linear OS lgc (m + 1)).map_smul }
         cont := bvt_W_continuous OS lgc (m + 1) },
        bvt_boundary_values OS lgc (m + 1)⟩
      (BHW.reducedTestLift m d χ.toSchwartz f)
      (BHW.absoluteDirectionOfReduced d m η)
      (BHW.absoluteDirectionOfReduced_mem_forwardCone (d := d) m η hη)
      ε hε
  rw [BHW.integral_realDiffCoord_change_variables (d := d) m G hG_int]
  simp_rw [G]
  have hfactor :
      ∀ (ξ : NPointDomain d m) (x₀ : SpacetimeDim d),
        bvt_F OS lgc (m + 1)
          (fun k μ =>
            (((BHW.realDiffCoordCLE (m + 1) d).symm
              (BHW.prependBasepointReal d m x₀ ξ) k μ : ℂ) +
              ε * (BHW.absoluteDirectionOfReduced d m η k μ : ℂ) * Complex.I)) =
          (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
            (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun
            (fun k μ => (ξ k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) := by
    intro ξ x₀
    exact (bvt_selectedReducedPreInput_factorization_absoluteApproach
      (d := d) OS lgc m x₀ ξ η hη hε).symm
  simp_rw [hfactor]
  have htest :
      ∀ (ξ : NPointDomain d m) (x₀ : SpacetimeDim d),
        BHW.reducedTestLift m d χ.toSchwartz f
          ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) =
            χ.toSchwartz x₀ * f ξ := by
    intro ξ x₀
    simp [BHW.reducedTestLift]
  simp_rw [htest]
  simp_rw [mul_assoc]
  simp_rw [show ∀ (a b c : ℂ), a * (b * c) = (a * c) * b by
    intro a b c; ring]
  simp_rw [← smul_eq_mul (a := _ * _), MeasureTheory.integral_smul, smul_eq_mul]
  simp [χ.integral_eq_one]

/-- The selected descended preinput has the reduced distributional boundary
values required by the reduced BHW input interface. -/
theorem bvt_selectedReducedBoundaryValues
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    BHW.HasReducedBoundaryValues (d := d)
      (bvt_reducedWightmanFamily (d := d) OS lgc χ) m
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun := by
  intro f η hη
  let ηAbs := BHW.absoluteDirectionOfReduced d m η
  have hηAbs :
      InForwardCone d (m + 1) ηAbs :=
    BHW.absoluteDirectionOfReduced_mem_forwardCone (d := d) m η hη
  have habs :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ x : NPointDomain d (m + 1),
            bvt_F OS lgc (m + 1)
              (fun k μ => (x k μ : ℂ) + ε * (ηAbs k μ : ℂ) * Complex.I) *
            BHW.reducedTestLift m d χ.toSchwartz f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_reducedWightmanFamily (d := d) OS lgc χ m f)) := by
    simpa [ηAbs, bvt_reducedWightmanFamily] using
      bvt_boundary_values (d := d) OS lgc (m + 1)
        (BHW.reducedTestLift m d χ.toSchwartz f) ηAbs hηAbs
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d m,
          (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
            (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun
            (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d (m + 1),
          bvt_F OS lgc (m + 1)
            (fun k μ => (x k μ : ℂ) + ε * (ηAbs k μ : ℂ) * Complex.I) *
          BHW.reducedTestLift m d χ.toSchwartz f x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [ηAbs] using
      bvt_selectedReducedBoundaryIntegral_eq_absoluteBoundaryIntegral
        (d := d) OS lgc χ m f η hη (Set.mem_Ioi.mp hε)
  exact Filter.Tendsto.congr' hEq.symm habs

/-- Fully bundled selected reduced forward-tube input.  The remaining PET/Fred
seam starts after this object: constructing a reduced BHW extension from it
using selected edge/permutation data. -/
noncomputable def bvt_selectedReducedForwardTubeInput
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    BHW.ReducedForwardTubeInput (d := d)
      (bvt_reducedWightmanFamily (d := d) OS lgc χ) m where
  toFun :=
    (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun
  holomorphic :=
    (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).holomorphic
  real_lorentz_invariant :=
    (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).real_lorentz_invariant
  boundary_values :=
    bvt_selectedReducedBoundaryValues (d := d) OS lgc χ m

/-! ### Selected PET scalar from reduced extension data

This section packages the part that is already implementation-ready once the
hard reduced BHW/PET extension has been constructed: pull the reduced extension
back to absolute coordinates.  The missing theorem is the construction of the
`ReducedBHWExtensionData` argument, not the translation algebra below.
-/

/-- The selected absolute PET scalar associated to a reduced BHW/PET extension
of the selected Route-1 preinput. -/
noncomputable def bvt_selectedPETExtensionOfReducedData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ :=
  BHW.pullbackReducedExtension (d := d) (n := m + 1) Fred.toFun

/-- Pullback from reduced coordinates makes the selected PET scalar uniformly
translation-invariant. -/
theorem bvt_selectedPETExtensionOfReducedData_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred
        (fun k μ => z k μ + c μ) =
      bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred z := by
  exact
    BHW.reduced_pullback_translation_invariant (d := d) (n := m + 1)
      Fred.toFun z c

/-- PET-local form of
`bvt_selectedPETExtensionOfReducedData_translate`, matching the hypothesis shape
expected by `translatedPETValue`. -/
theorem bvt_selectedPETExtensionOfReducedData_translate_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (_hz : z ∈ PermutedExtendedTube d (m + 1))
    (_hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1)) :
    bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred
        (fun k μ => z k μ + c μ) =
      bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred z :=
  bvt_selectedPETExtensionOfReducedData_translate (d := d) OS lgc m Fred z c

/-- The selected PET scalar built from reduced extension data is holomorphic on
the absolute PET, because it is the pullback of a reduced PET-holomorphic
scalar along `reducedDiffMap`. -/
theorem bvt_selectedPETExtensionOfReducedData_holomorphicOn_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun) :
    DifferentiableOn ℂ
      (bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred)
      (BHW.PermutedExtendedTube d (m + 1)) := by
  intro z hz
  change DifferentiableWithinAt ℂ
    (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
      Fred.toFun (BHW.reducedDiffMap (m + 1) d z))
    (BHW.PermutedExtendedTube d (m + 1)) z
  have hdiff :
      DifferentiableWithinAt ℂ
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.reducedDiffMap (m + 1) d z)
        (BHW.PermutedExtendedTube d (m + 1)) z :=
    (BHW.reducedDiffMap (m + 1) d).differentiable.differentiableAt.differentiableWithinAt
  have hmaps :
      Set.MapsTo
        (fun z : Fin (m + 1) → Fin (d + 1) → ℂ =>
          BHW.reducedDiffMap (m + 1) d z)
        (BHW.PermutedExtendedTube d (m + 1))
        (BHW.ReducedPermutedExtendedTubeN d m) := by
    intro w hw
    exact ⟨w, hw, rfl⟩
  exact (Fred.holomorphic _ ⟨z, hz, rfl⟩).comp z hdiff hmaps

/-- The selected PET scalar built from reduced extension data inherits PET
permutation invariance from the reduced extension datum. -/
theorem bvt_selectedPETExtensionOfReducedData_permInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun)
    (σ : Equiv.Perm (Fin (m + 1)))
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d (m + 1))
    (hσz : (fun k => z (σ k)) ∈ BHW.PermutedExtendedTube d (m + 1)) :
    bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred
        (fun k => z (σ k)) =
      bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred z := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  change
    Fred.toFun (BHW.reducedDiffMap (m + 1) d (fun k => z (σ k))) =
      Fred.toFun (BHW.reducedDiffMap (m + 1) d z)
  rw [← BHW.permOnReducedDiff_reducedDiffMap (d := d) (n := m + 1) σ z]
  exact
    Fred.perm_invariant σ (BHW.reducedDiffMap (m + 1) d z)
      ⟨z, hz, rfl⟩
      (by
        rw [BHW.permOnReducedDiff_reducedDiffMap (d := d) (n := m + 1) σ z]
        exact ⟨fun k => z (σ k), hσz, rfl⟩)

/-- The selected PET scalar built from reduced extension data agrees with
`bvt_F` on the original forward tube. -/
theorem bvt_selectedPETExtensionOfReducedData_eq_bvt_F_on_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1)) :
    bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred z =
      bvt_F OS lgc (m + 1) z := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  have hred : BHW.reducedDiffMap (m + 1) d z ∈ BHW.ReducedForwardTubeN d m := by
    have hz_BHW : z ∈ BHW.ForwardTube d (m + 1) := by
      simpa [BHW_forwardTube_eq (d := d) (n := m + 1)] using hz
    have hz_split :=
      (BHW.mem_forwardTube_iff_basepoint_and_reducedDiff
        (n := m + 1) (d := d) z).1 hz_BHW
    simpa [BHW.ReducedForwardTubeN, BHW.ReducedForwardTube] using hz_split.2
  calc
    bvt_selectedPETExtensionOfReducedData (d := d) OS lgc m Fred z
        = Fred.toFun (BHW.reducedDiffMap (m + 1) d z) := rfl
    _ =
        (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
          (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun
          (BHW.reducedDiffMap (m + 1) d z) :=
          Fred.agrees_on_reducedForwardTube _ hred
    _ = bvt_F OS lgc (m + 1) z :=
        BHW.descendAbsoluteForwardTubeInput_factorization (d := d) (m := m)
          (bvt_absoluteForwardTubeInput (d := d) OS lgc m) z
          ((BHW_forwardTube_eq (d := d) (n := m + 1)) ▸ hz)
