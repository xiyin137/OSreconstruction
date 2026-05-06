import Mathlib.Topology.UnitInterval
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceRank

/-!
# Source-oriented BHW/Jost continuation carriers

This file contains the lower data structures for the strict proper-complex
BHW/Jost source-patch route.  The structures deliberately store local
realization fields for oriented invariant patches: one-way membership of the
source image in an oriented domain is not enough for the later descent of
source branch equality to equality of oriented scalar germs.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- The source-patch ambient used in the OS I §4.5 adjacent transposition
route: the ordinary extended tube together with the selected adjacent
permuted extended-tube sector. -/
def os45SourcePatchBHWJostAmbient
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ExtendedTube d n ∪ {z | permAct (d := d) τ z ∈ ExtendedTube d n}

/-- The connected hull used by the source-patch BHW/Jost continuation. -/
def os45SourcePatchBHWJostHull
    (d n : ℕ) (τ : Equiv.Perm (Fin n))
    (z0 : Fin n → Fin (d + 1) → ℂ) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  pathComponentIn (os45SourcePatchBHWJostAmbient d n τ) z0

/-- The oriented invariant-side domain forced by the OS45 source-patch
ambient.  This is only the visible one-way image domain; no global converse
realization is asserted here. -/
def os45SourcePatchOrientedAmbientDomain
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Set (SourceOrientedGramData d n) :=
  sourceOrientedExtendedTubeDomain d n ∪
    {G | sourcePermuteOrientedGram d n τ G ∈
      sourceOrientedExtendedTubeDomain d n}

/-- A source point in the OS45 source-patch ambient has oriented invariant in
the corresponding oriented union domain. -/
theorem sourceOrientedMinkowskiInvariant_mem_os45SourcePatchOrientedAmbientDomain
    (τ : Equiv.Perm (Fin n)) {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ os45SourcePatchBHWJostAmbient d n τ) :
    sourceOrientedMinkowskiInvariant d n z ∈
      os45SourcePatchOrientedAmbientDomain d n τ := by
  rcases hz with hz | hz
  · exact Or.inl ⟨z, hz, rfl⟩
  · refine Or.inr ?_
    change
      sourcePermuteOrientedGram d n τ
          (sourceOrientedMinkowskiInvariant d n z) ∈
        sourceOrientedExtendedTubeDomain d n
    rw [← sourceOrientedMinkowskiInvariant_permAct (d := d) (n := n) τ z]
    exact ⟨permAct (d := d) τ z, hz, rfl⟩

/-- The oriented OS45 ambient domain lies in the oriented source variety. -/
theorem os45SourcePatchOrientedAmbientDomain_subset_variety
    (τ : Equiv.Perm (Fin n)) :
    os45SourcePatchOrientedAmbientDomain d n τ ⊆
      sourceOrientedGramVariety d n := by
  intro G hG
  rcases hG with hG | hG
  · exact sourceOrientedExtendedTubeDomain_subset_variety d n hG
  · exact
      (sourcePermuteOrientedGram_mem_variety_iff (d := d) (n := n) τ G).mp
        (sourceOrientedExtendedTubeDomain_subset_variety d n hG)

/-- Relative openness in the oriented source variety is stable under finite
unions. -/
theorem IsRelOpenInSourceOrientedGramVariety.union
    {U V : Set (SourceOrientedGramData d n)}
    (hU : IsRelOpenInSourceOrientedGramVariety d n U)
    (hV : IsRelOpenInSourceOrientedGramVariety d n V) :
    IsRelOpenInSourceOrientedGramVariety d n (U ∪ V) := by
  rcases hU with ⟨U0, hU0_open, hU_eq⟩
  rcases hV with ⟨V0, hV0_open, hV_eq⟩
  refine ⟨U0 ∪ V0, hU0_open.union hV0_open, ?_⟩
  rw [hU_eq, hV_eq]
  ext G
  constructor
  · rintro (⟨hU0G, hGvar⟩ | ⟨hV0G, hGvar⟩)
    · exact ⟨Or.inl hU0G, hGvar⟩
    · exact ⟨Or.inr hV0G, hGvar⟩
  · rintro ⟨hUV, hGvar⟩
    rcases hUV with hU0G | hV0G
    · exact Or.inl ⟨hU0G, hGvar⟩
    · exact Or.inr ⟨hV0G, hGvar⟩

/-- Conditional relative-openness of the oriented OS45 union domain.  The only
hard input is relative-openness of the oriented extended-tube image. -/
theorem os45SourcePatchOrientedAmbientDomain_relOpen_of_sourceOrientedExtendedTubeDomain
    (hET :
      IsRelOpenInSourceOrientedGramVariety d n
        (sourceOrientedExtendedTubeDomain d n))
    (τ : Equiv.Perm (Fin n)) :
    IsRelOpenInSourceOrientedGramVariety d n
      (os45SourcePatchOrientedAmbientDomain d n τ) := by
  have hpre :
      IsRelOpenInSourceOrientedGramVariety d n
        {G | sourcePermuteOrientedGram d n τ G ∈
          sourceOrientedExtendedTubeDomain d n} :=
    IsRelOpenInSourceOrientedGramVariety.preimage_sourcePermuteOrientedGram
      (d := d) (n := n) hET τ
  simpa [os45SourcePatchOrientedAmbientDomain] using
    IsRelOpenInSourceOrientedGramVariety.union
      (d := d) (n := n) hET hpre

/-- The chosen base point belongs to its source-patch hull once it belongs to
the OS45 ambient. -/
theorem mem_os45SourcePatchBHWJostHull_self
    (τ : Equiv.Perm (Fin n)) (z0 : Fin n → Fin (d + 1) → ℂ)
    (hz0 : z0 ∈ os45SourcePatchBHWJostAmbient d n τ) :
    z0 ∈ os45SourcePatchBHWJostHull d n τ z0 := by
  simpa [os45SourcePatchBHWJostHull] using
    (mem_pathComponentIn_self hz0)

/-- The source-patch hull is contained in the displayed OS45 ambient. -/
theorem os45SourcePatchBHWJostHull_subset_ambient
    (τ : Equiv.Perm (Fin n)) (z0 : Fin n → Fin (d + 1) → ℂ) :
    os45SourcePatchBHWJostHull d n τ z0 ⊆
      os45SourcePatchBHWJostAmbient d n τ := by
  intro z hz
  exact hz.target_mem

/-- A source-patch hull is nonempty when the base point lies in the ambient. -/
theorem os45SourcePatchBHWJostHull_nonempty
    (τ : Equiv.Perm (Fin n)) (z0 : Fin n → Fin (d + 1) → ℂ)
    (hz0 : z0 ∈ os45SourcePatchBHWJostAmbient d n τ) :
    (os45SourcePatchBHWJostHull d n τ z0).Nonempty :=
  ⟨z0, mem_os45SourcePatchBHWJostHull_self (d := d) (n := n) τ z0 hz0⟩

/-- A source-patch hull is path-connected when the base point lies in the
ambient. -/
theorem os45SourcePatchBHWJostHull_isPathConnected
    (τ : Equiv.Perm (Fin n)) (z0 : Fin n → Fin (d + 1) → ℂ)
    (hz0 : z0 ∈ os45SourcePatchBHWJostAmbient d n τ) :
    IsPathConnected (os45SourcePatchBHWJostHull d n τ z0) := by
  simpa [os45SourcePatchBHWJostHull] using
    (isPathConnected_pathComponentIn hz0)

/-- A source-patch hull is connected when the base point lies in the ambient. -/
theorem os45SourcePatchBHWJostHull_connected
    (τ : Equiv.Perm (Fin n)) (z0 : Fin n → Fin (d + 1) → ℂ)
    (hz0 : z0 ∈ os45SourcePatchBHWJostAmbient d n τ) :
    IsConnected (os45SourcePatchBHWJostHull d n τ z0) :=
  (os45SourcePatchBHWJostHull_isPathConnected (d := d) (n := n) τ z0 hz0).isConnected

/-- A source-patch hull is preconnected when the base point lies in the
ambient. -/
theorem os45SourcePatchBHWJostHull_preconnected
    (τ : Equiv.Perm (Fin n)) (z0 : Fin n → Fin (d + 1) → ℂ)
    (hz0 : z0 ∈ os45SourcePatchBHWJostAmbient d n τ) :
    IsPreconnected (os45SourcePatchBHWJostHull d n τ z0) :=
  (os45SourcePatchBHWJostHull_isPathConnected (d := d) (n := n) τ z0 hz0).isConnected.2

/-- A finite ordered subdivision of the unit interval subordinate to an open
cover. -/
structure UnitIntervalOrderedSubdivision
    {ι : Type*} (c : ι → Set unitInterval) where
  m : ℕ
  t : Fin (m + 1) → unitInterval
  t_zero : t 0 = 0
  t_last : t (Fin.last m) = 1
  t_mono : Monotone t
  interval_sub :
    ∀ j : Fin m,
      ∃ i, Set.Icc (t (Fin.castSucc j)) (t j.succ) ⊆ c i

namespace UnitIntervalOrderedSubdivision

variable {ι : Type*} {c : ι → Set unitInterval}

/-- The two endpoints of each subdivision interval lie in one common member of
the cover. -/
theorem interval_endpoints_mem_cover
    (S : UnitIntervalOrderedSubdivision c) (j : Fin S.m) :
    ∃ i,
      S.t (Fin.castSucc j) ∈ c i ∧
      S.t j.succ ∈ c i := by
  rcases S.interval_sub j with ⟨i, hi⟩
  have hle : S.t (Fin.castSucc j) ≤ S.t j.succ :=
    S.t_mono (Fin.castSucc_le_succ j)
  exact
    ⟨i, hi ((Set.left_mem_Icc).2 hle),
      hi ((Set.right_mem_Icc).2 hle)⟩

/-- The left endpoint of each subdivision interval lies in a member of the
cover controlling that interval. -/
theorem left_endpoint_mem_cover
    (S : UnitIntervalOrderedSubdivision c) (j : Fin S.m) :
    ∃ i, S.t (Fin.castSucc j) ∈ c i := by
  rcases S.interval_endpoints_mem_cover j with ⟨i, hi_left, _hi_right⟩
  exact ⟨i, hi_left⟩

/-- The right endpoint of each subdivision interval lies in a member of the
cover controlling that interval. -/
theorem right_endpoint_mem_cover
    (S : UnitIntervalOrderedSubdivision c) (j : Fin S.m) :
    ∃ i, S.t j.succ ∈ c i := by
  rcases S.interval_endpoints_mem_cover j with ⟨i, _hi_left, hi_right⟩
  exact ⟨i, hi_right⟩

end UnitIntervalOrderedSubdivision

/-- Mathlib's open-cover subdivision theorem packaged as existence of a finite
ordered subdivision object. -/
theorem exists_unitInterval_orderedSubdivision_of_openCover
    {ι : Type*} (c : ι → Set unitInterval)
    (hc_open : ∀ i, IsOpen (c i))
    (hc_cover : Set.univ ⊆ ⋃ i, c i) :
    Nonempty (UnitIntervalOrderedSubdivision c) := by
  obtain ⟨tN, ht0, ht_mono, ⟨m, hm⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  refine ⟨
    { m := m
      t := fun j => tN j
      t_zero := ?_
      t_last := ?_
      t_mono := ?_
      interval_sub := ?_ }⟩
  · simpa using ht0
  · simpa using hm m le_rfl
  · intro j k hjk
    exact ht_mono (show (j : ℕ) ≤ (k : ℕ) from hjk)
  · intro j
    simpa using ht_sub j.val

/-- A noncomputable finite ordered subdivision selected from an open cover of
the unit interval. -/
noncomputable def unitInterval_orderedSubdivision_of_openCover
    {ι : Type*} (c : ι → Set unitInterval)
    (hc_open : ∀ i, IsOpen (c i))
    (hc_cover : Set.univ ⊆ ⋃ i, c i) :
    UnitIntervalOrderedSubdivision c :=
  Classical.choice
    (exists_unitInterval_orderedSubdivision_of_openCover c hc_open hc_cover)

/-- Path-specialized open-cover subdivision: if each point of a continuous
unit-interval path has an open target neighborhood containing its image, then
the pullback cover of the unit interval admits a finite ordered subdivision. -/
theorem exists_unitInterval_orderedSubdivision_of_path_openCover
    {E : Type*} [TopologicalSpace E]
    (γ : unitInterval → E) (hγ : Continuous γ)
    (N : unitInterval → Set E)
    (hN_open : ∀ t, IsOpen (N t))
    (hN_mem : ∀ t, γ t ∈ N t) :
    Nonempty
      (UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' N t)) := by
  refine
    exists_unitInterval_orderedSubdivision_of_openCover
      (fun t : unitInterval => γ ⁻¹' N t) ?_ ?_
  · intro t
    exact (hN_open t).preimage hγ
  · intro s _hs
    exact Set.mem_iUnion.mpr ⟨s, hN_mem s⟩

/-- A selected finite ordered subdivision for a path-neighborhood pullback
cover. -/
noncomputable def unitInterval_orderedSubdivision_of_path_openCover
    {E : Type*} [TopologicalSpace E]
    (γ : unitInterval → E) (hγ : Continuous γ)
    (N : unitInterval → Set E)
    (hN_open : ∀ t, IsOpen (N t))
    (hN_mem : ∀ t, γ t ∈ N t) :
    UnitIntervalOrderedSubdivision
      (fun t : unitInterval => γ ⁻¹' N t) :=
  Classical.choice
    (exists_unitInterval_orderedSubdivision_of_path_openCover
      γ hγ N hN_open hN_mem)

/-- Every point of an open subset of a real normed space has an open
preconnected neighborhood contained in the subset. -/
theorem exists_open_preconnected_neighborhood_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {p : E}
    (hs : IsOpen s) (hp : p ∈ s) :
    ∃ P : Set E,
      p ∈ P ∧ IsOpen P ∧ IsPreconnected P ∧ P.Nonempty ∧ P ⊆ s := by
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp hs p hp
  refine ⟨Metric.ball p ε, ?_, Metric.isOpen_ball, ?_, ?_, hε_sub⟩
  · exact Metric.mem_ball_self hε_pos
  · exact (convex_ball p ε).isPreconnected
  · exact ⟨p, Metric.mem_ball_self hε_pos⟩

/-- Permuting source labels is continuous in the finite product topology. -/
theorem continuous_permAct (σ : Equiv.Perm (Fin n)) :
    Continuous (permAct (d := d) σ) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (σ k))

/-- The OS45 source-patch BHW/Jost ambient is open. -/
theorem isOpen_os45SourcePatchBHWJostAmbient
    (d n : ℕ) (τ : Equiv.Perm (Fin n)) :
    IsOpen (os45SourcePatchBHWJostAmbient d n τ) := by
  exact isOpen_extendedTube.union
    (isOpen_extendedTube.preimage
      (continuous_permAct (d := d) (n := n) τ))

/-- Maximal oriented source rank: maximal rank of the ordinary Gram
coordinate, carried on the oriented invariant space. -/
def SourceOrientedMaxRankAt
    (d n : ℕ) (G : SourceOrientedGramData d n) : Prop :=
  sourceGramMatrixRank n G.gram = min (d + 1) n

/-- The complementary exceptional-rank locus inside the oriented source
variety. -/
def SourceOrientedExceptionalRank
    (d n : ℕ) (G : SourceOrientedGramData d n) : Prop :=
  G ∈ sourceOrientedGramVariety d n ∧ ¬ SourceOrientedMaxRankAt d n G

/-- Inside the oriented source variety, exceptional rank is exactly failure of
maximal oriented rank. -/
theorem sourceOrientedExceptionalRank_iff_not_maxRank
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    SourceOrientedExceptionalRank d n G ↔
      ¬ SourceOrientedMaxRankAt d n G := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hG, h⟩

/-- On the oriented source variety, not being exceptional is the same as
being in the maximal-rank stratum. -/
theorem not_sourceOrientedExceptionalRank_iff_maxRank
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    ¬ SourceOrientedExceptionalRank d n G ↔
      SourceOrientedMaxRankAt d n G := by
  rw [sourceOrientedExceptionalRank_iff_not_maxRank (d := d) (n := n) hG]
  exact not_not

/-- Maximal oriented source rank is transported by equality of oriented source
invariants. -/
theorem SourceOrientedMaxRankAt_of_invariant_eq
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z))
    (hzw :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    SourceOrientedMaxRankAt d n
      (sourceOrientedMinkowskiInvariant d n w) := by
  simpa [← hzw] using hz

/-- Proper complex-Lorentz action preserves maximal oriented source rank. -/
theorem sourceOrientedMaxRankAt_complexLorentzAction_iff
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n
          (complexLorentzAction Λ z)) ↔
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z) := by
  rw [sourceOrientedMinkowskiInvariant_complexLorentzAction]

/-- A local source chart whose branch descends through the oriented source
invariant.  The `oriented_realizes` field is essential: the stored oriented
domain is a local image of the source carrier, not an arbitrary larger
relative-open set. -/
structure BHWJostLocalOrientedContinuationChart
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (U : Set (Fin n → Fin (d + 1) → ℂ)) where
  carrier : Set (Fin n → Fin (d + 1) → ℂ)
  carrier_open : IsOpen carrier
  carrier_preconnected : IsPreconnected carrier
  carrier_sub_U : carrier ⊆ U
  carrier_is_lorentz_step :
    ∃ Ωbase : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ωbase ∧
      Ωbase ⊆ os45SourcePatchBHWJostAmbient d n τ ∧
      ∃ Λ : ComplexLorentzGroup d,
        carrier = (fun u => complexLorentzAction Λ u) '' Ωbase
  orientedDomain : Set (SourceOrientedGramData d n)
  oriented_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n orientedDomain
  oriented_preconnected : IsPreconnected orientedDomain
  oriented_sub_variety :
    orientedDomain ⊆ sourceOrientedGramVariety d n
  oriented_mem :
    ∀ z, z ∈ carrier →
      sourceOrientedMinkowskiInvariant d n z ∈ orientedDomain
  oriented_realizes :
    ∀ G, G ∈ orientedDomain →
      ∃ z, z ∈ carrier ∧ sourceOrientedMinkowskiInvariant d n z = G
  Psi : SourceOrientedGramData d n → ℂ
  Psi_holo :
    SourceOrientedVarietyGermHolomorphicOn d n Psi orientedDomain
  branch : (Fin n → Fin (d + 1) → ℂ) → ℂ
  branch_eq_orientedPullback :
    ∀ z, z ∈ carrier →
      branch z = Psi (sourceOrientedMinkowskiInvariant d n z)
  branch_holo : DifferentiableOn ℂ branch carrier
  branch_same_sourceOrientedInvariant :
    ∀ z w, z ∈ carrier → w ∈ carrier →
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w →
      branch z = branch w
  branch_complexLorentzInvariant :
    ∀ Λ z, z ∈ carrier →
      complexLorentzAction Λ z ∈ carrier →
        branch (complexLorentzAction Λ z) = branch z

namespace BHWJostLocalOrientedContinuationChart

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}

/-- Source points in a chart have oriented invariants in the oriented source
variety. -/
theorem sourceOrientedInvariant_mem_variety
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ C.carrier) :
    sourceOrientedMinkowskiInvariant d n z ∈ sourceOrientedGramVariety d n :=
  C.oriented_sub_variety (C.oriented_mem z hz)

/-- Branch equality descends immediately from equality of oriented source
invariants once the chart is stored as an oriented pullback. -/
theorem branch_eq_of_sourceOrientedInvariant
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ C.carrier) (hw : w ∈ C.carrier)
    (hzw :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    C.branch z = C.branch w := by
  rw [C.branch_eq_orientedPullback z hz,
    C.branch_eq_orientedPullback w hw, hzw]

/-- Complex-Lorentz invariance of a stored oriented-pullback branch is a
rewrite by invariance of the oriented source invariant. -/
theorem branch_eq_complexLorentzAction
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    (Λ : ComplexLorentzGroup d)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ C.carrier)
    (hΛz : complexLorentzAction Λ z ∈ C.carrier) :
    C.branch (complexLorentzAction Λ z) = C.branch z := by
  rw [C.branch_eq_orientedPullback (complexLorentzAction Λ z) hΛz,
    C.branch_eq_orientedPullback z hz,
    sourceOrientedMinkowskiInvariant_complexLorentzAction]

/-- Every oriented point of a chart domain has a source representative whose
stored source branch is exactly the oriented germ evaluated at that point. -/
theorem exists_source_realization_branch_eq
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ C.orientedDomain) :
    ∃ z, z ∈ C.carrier ∧
      sourceOrientedMinkowskiInvariant d n z = G ∧
      C.branch z = C.Psi G := by
  rcases C.oriented_realizes G hG with ⟨z, hz, hzG⟩
  refine ⟨z, hz, hzG, ?_⟩
  rw [C.branch_eq_orientedPullback z hz, hzG]

/-- Every oriented point of a chart domain has a source representative in the
ambient continuation set `U`. -/
theorem exists_source_realization_mem_U_branch_eq
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ C.orientedDomain) :
    ∃ z, z ∈ C.carrier ∧ z ∈ U ∧
      sourceOrientedMinkowskiInvariant d n z = G ∧
      C.branch z = C.Psi G := by
  rcases C.exists_source_realization_branch_eq hG with
    ⟨z, hz, hzG, hbranch⟩
  exact ⟨z, hz, C.carrier_sub_U hz, hzG, hbranch⟩

/-- If a local oriented chart has a source point, its oriented domain is
nonempty. -/
theorem orientedDomain_nonempty_of_carrier_nonempty
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hC : C.carrier.Nonempty) :
    C.orientedDomain.Nonempty := by
  rcases hC with ⟨z, hz⟩
  exact ⟨sourceOrientedMinkowskiInvariant d n z, C.oriented_mem z hz⟩

/-- A local oriented chart domain is connected once its source carrier is
known to be nonempty. -/
theorem orientedDomain_connected_of_carrier_nonempty
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hC : C.carrier.Nonempty) :
    IsConnected C.orientedDomain :=
  ⟨C.orientedDomain_nonempty_of_carrier_nonempty hC,
    C.oriented_preconnected⟩

end BHWJostLocalOrientedContinuationChart

/-- Transition data between consecutive oriented BHW/Jost charts.  The
oriented transition patch is again required to be locally realized by the
source overlap. -/
structure BHWJostOrientedTransitionData
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (Cleft Cright :
      BHWJostLocalOrientedContinuationChart hd n τ U)
    (p q : Fin n → Fin (d + 1) → ℂ) where
  sourcePatch : Set (Fin n → Fin (d + 1) → ℂ)
  sourcePatch_open : IsOpen sourcePatch
  sourcePatch_preconnected : IsPreconnected sourcePatch
  sourcePatch_nonempty : sourcePatch.Nonempty
  source_mem : p ∈ sourcePatch
  target_mem : q ∈ Cright.carrier
  sourcePatch_sub :
    sourcePatch ⊆ Cleft.carrier ∩ Cright.carrier
  source_branch_agree :
    Set.EqOn Cleft.branch Cright.branch sourcePatch
  orientedPatch : Set (SourceOrientedGramData d n)
  orientedPatch_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n orientedPatch
  orientedPatch_preconnected : IsPreconnected orientedPatch
  orientedPatch_nonempty : orientedPatch.Nonempty
  orientedPatch_sub :
    orientedPatch ⊆ Cleft.orientedDomain ∩ Cright.orientedDomain
  sourcePatch_oriented_mem :
    ∀ y, y ∈ sourcePatch →
      sourceOrientedMinkowskiInvariant d n y ∈ orientedPatch
  orientedPatch_source_realizes :
    ∀ G, G ∈ orientedPatch →
      ∃ y, y ∈ sourcePatch ∧ sourceOrientedMinkowskiInvariant d n y = G
  oriented_psi_agree :
    Set.EqOn Cleft.Psi Cright.Psi orientedPatch

namespace BHWJostOrientedTransitionData

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {Cleft Cright : BHWJostLocalOrientedContinuationChart hd n τ U}
variable {p q : Fin n → Fin (d + 1) → ℂ}

/-- The tautological transition from a local oriented chart to itself.  This
is used to retarget a continuation chain from its stored terminal node to any
other point in its terminal chart. -/
def sameChart
    (C : BHWJostLocalOrientedContinuationChart hd n τ U)
    {p q : Fin n → Fin (d + 1) → ℂ}
    (hp : p ∈ C.carrier) (hq : q ∈ C.carrier) :
    BHWJostOrientedTransitionData hd n τ U C C p q where
  sourcePatch := C.carrier
  sourcePatch_open := C.carrier_open
  sourcePatch_preconnected := C.carrier_preconnected
  sourcePatch_nonempty := ⟨p, hp⟩
  source_mem := hp
  target_mem := hq
  sourcePatch_sub := by
    intro y hy
    exact ⟨hy, hy⟩
  source_branch_agree := by
    intro _y _hy
    rfl
  orientedPatch := C.orientedDomain
  orientedPatch_relOpen := C.oriented_relOpen
  orientedPatch_preconnected := C.oriented_preconnected
  orientedPatch_nonempty :=
    ⟨sourceOrientedMinkowskiInvariant d n p, C.oriented_mem p hp⟩
  orientedPatch_sub := by
    intro G hG
    exact ⟨hG, hG⟩
  sourcePatch_oriented_mem := by
    intro y hy
    exact C.oriented_mem y hy
  orientedPatch_source_realizes := by
    intro G hG
    exact C.oriented_realizes G hG
  oriented_psi_agree := by
    intro _G _hG
    rfl

/-- The source transition patch lies in the left chart carrier. -/
theorem sourcePatch_subset_left
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    T.sourcePatch ⊆ Cleft.carrier := by
  intro y hy
  exact (T.sourcePatch_sub hy).1

/-- The source transition patch lies in the right chart carrier. -/
theorem sourcePatch_subset_right
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    T.sourcePatch ⊆ Cright.carrier := by
  intro y hy
  exact (T.sourcePatch_sub hy).2

/-- The source transition patch lies in the ambient continuation set `U`. -/
theorem sourcePatch_subset_U
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    T.sourcePatch ⊆ U := by
  intro y hy
  exact Cleft.carrier_sub_U (sourcePatch_subset_left T hy)

/-- The transition source point belongs to the left chart carrier. -/
theorem source_mem_left_carrier
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    p ∈ Cleft.carrier :=
  sourcePatch_subset_left T T.source_mem

/-- The transition source point belongs to the right chart carrier. -/
theorem source_mem_right_carrier
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    p ∈ Cright.carrier :=
  sourcePatch_subset_right T T.source_mem

/-- The transition source point belongs to the ambient continuation set `U`. -/
theorem source_mem_U
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    p ∈ U :=
  sourcePatch_subset_U T T.source_mem

/-- The oriented transition patch lies in the left oriented chart domain. -/
theorem orientedPatch_subset_left
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    T.orientedPatch ⊆ Cleft.orientedDomain := by
  intro G hG
  exact (T.orientedPatch_sub hG).1

/-- The oriented transition patch lies in the right oriented chart domain. -/
theorem orientedPatch_subset_right
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    T.orientedPatch ⊆ Cright.orientedDomain := by
  intro G hG
  exact (T.orientedPatch_sub hG).2

/-- A stored oriented transition patch is connected. -/
theorem orientedPatch_connected
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    IsConnected T.orientedPatch :=
  ⟨T.orientedPatch_nonempty, T.orientedPatch_preconnected⟩

/-- Oriented germ agreement on the transition patch descends to agreement of
the source branches on the realized source overlap. -/
theorem source_branch_agree_of_oriented
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    Set.EqOn Cleft.branch Cright.branch T.sourcePatch := by
  intro y hy
  have hyLR := T.sourcePatch_sub hy
  rw [Cleft.branch_eq_orientedPullback y hyLR.1,
    Cright.branch_eq_orientedPullback y hyLR.2]
  exact T.oriented_psi_agree (T.sourcePatch_oriented_mem y hy)

/-- At the transition source point, the previous chart branch is the starting
branch for the next chart. -/
theorem source_branch_agree_at_source
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q) :
    Cleft.branch p = Cright.branch p :=
  source_branch_agree_of_oriented T T.source_mem

/-- Every oriented transition-patch point is represented by a genuine source
overlap point where the two consecutive source branches agree. -/
theorem exists_sourcePatch_realization_of_orientedPatch
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ T.orientedPatch) :
    ∃ y, y ∈ T.sourcePatch ∧
      y ∈ Cleft.carrier ∧
      y ∈ Cright.carrier ∧
      sourceOrientedMinkowskiInvariant d n y = G ∧
      Cleft.branch y = Cright.branch y := by
  rcases T.orientedPatch_source_realizes G hG with ⟨y, hy, hyG⟩
  refine
    ⟨y, hy, sourcePatch_subset_left T hy, sourcePatch_subset_right T hy,
      hyG, ?_⟩
  exact source_branch_agree_of_oriented T hy

/-- Every realized point of the oriented transition patch lies in the ambient
continuation set `U`. -/
theorem exists_sourcePatch_realization_mem_U_of_orientedPatch
    (T : BHWJostOrientedTransitionData hd n τ U Cleft Cright p q)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ T.orientedPatch) :
    ∃ y, y ∈ T.sourcePatch ∧ y ∈ U ∧
      sourceOrientedMinkowskiInvariant d n y = G ∧
      Cleft.branch y = Cright.branch y := by
  rcases T.exists_sourcePatch_realization_of_orientedPatch hG with
    ⟨y, hyPatch, _hyLeft, _hyRight, hyG, hbranch⟩
  exact ⟨y, hyPatch, sourcePatch_subset_U T hyPatch, hyG, hbranch⟩

end BHWJostOrientedTransitionData

/-- Source-normal-form geometry patch used to build branch-free local transfer
neighborhoods. -/
structure BHWJostOrientedSourceNormalFormGeometryPatch
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (center : Fin n → Fin (d + 1) → ℂ) where
  carrier : Set (Fin n → Fin (d + 1) → ℂ)
  carrier_open : IsOpen carrier
  carrier_preconnected : IsPreconnected carrier
  center_mem : center ∈ carrier
  carrier_sub_U : carrier ⊆ U
  orientedDomain : Set (SourceOrientedGramData d n)
  oriented_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n orientedDomain
  oriented_preconnected : IsPreconnected orientedDomain
  oriented_sub_variety :
    orientedDomain ⊆ sourceOrientedGramVariety d n
  oriented_mem :
    ∀ z, z ∈ carrier →
      sourceOrientedMinkowskiInvariant d n z ∈ orientedDomain
  oriented_realizes :
    ∀ G, G ∈ orientedDomain →
      ∃ z, z ∈ carrier ∧ sourceOrientedMinkowskiInvariant d n z = G

namespace BHWJostOrientedSourceNormalFormGeometryPatch

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {center : Fin n → Fin (d + 1) → ℂ}

/-- Source points in a normal-form geometry patch have oriented invariants in
the oriented source variety. -/
theorem sourceOrientedInvariant_mem_variety
    (P : BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ P.carrier) :
    sourceOrientedMinkowskiInvariant d n z ∈ sourceOrientedGramVariety d n :=
  P.oriented_sub_variety (P.oriented_mem z hz)

/-- Normal-form oriented domains are stored with actual source
representatives. -/
theorem exists_source_realization
    (P : BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ P.orientedDomain) :
    ∃ z, z ∈ P.carrier ∧ sourceOrientedMinkowskiInvariant d n z = G :=
  P.oriented_realizes G hG

/-- Normal-form oriented domains are stored with source representatives lying
in the ambient continuation set `U`. -/
theorem exists_source_realization_mem_U
    (P : BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ P.orientedDomain) :
    ∃ z, z ∈ P.carrier ∧ z ∈ U ∧
      sourceOrientedMinkowskiInvariant d n z = G := by
  rcases P.exists_source_realization hG with ⟨z, hz, hzG⟩
  exact ⟨z, hz, P.carrier_sub_U hz, hzG⟩

/-- The oriented domain of a source-normal-form geometry patch is nonempty. -/
theorem orientedDomain_nonempty
    (P : BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center) :
    P.orientedDomain.Nonempty :=
  ⟨sourceOrientedMinkowskiInvariant d n center,
    P.oriented_mem center P.center_mem⟩

/-- The oriented domain of a source-normal-form geometry patch is connected. -/
theorem orientedDomain_connected
    (P : BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center) :
    IsConnected P.orientedDomain :=
  ⟨P.orientedDomain_nonempty, P.oriented_preconnected⟩

end BHWJostOrientedSourceNormalFormGeometryPatch

/-- Branch-free local transfer neighborhood used to form finite continuation
chains from compact paths. -/
structure BHWJostOrientedBranchFreeTransferNeighborhood
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (center : Fin n → Fin (d + 1) → ℂ) where
  N : Set (Fin n → Fin (d + 1) → ℂ)
  N_mem_nhds : N ∈ 𝓝 center
  N_open : IsOpen N
  center_mem : center ∈ N
  transfer :
    ∀ p q, p ∈ N → p ∈ U → q ∈ N → q ∈ U →
    ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
      p ∈ Cprev.carrier →
        Σ Cnext : BHWJostLocalOrientedContinuationChart hd n τ U,
          BHWJostOrientedTransitionData hd n τ U Cprev Cnext p q

namespace BHWJostOrientedBranchFreeTransferNeighborhood

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {center : Fin n → Fin (d + 1) → ℂ}

/-- A source-normal-form geometry patch plus uniform oriented descent on that
patch gives the branch-free transfer neighborhood used by compact-path
continuation. -/
def ofSourceNormalFormPatch
    (G : BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center)
    (transfer :
      ∀ p q, p ∈ G.carrier → p ∈ U → q ∈ G.carrier → q ∈ U →
      ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
        p ∈ Cprev.carrier →
          Σ Cnext : BHWJostLocalOrientedContinuationChart hd n τ U,
            BHWJostOrientedTransitionData hd n τ U Cprev Cnext p q) :
    BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center where
  N := G.carrier
  N_mem_nhds := G.carrier_open.mem_nhds G.center_mem
  N_open := G.carrier_open
  center_mem := G.center_mem
  transfer := transfer

/-- A branch-free transfer produces a next chart containing the previous
source point. -/
theorem transfer_source_mem_next
    (N : BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    {p q : Fin n → Fin (d + 1) → ℂ}
    (hpN : p ∈ N.N) (hpU : p ∈ U)
    (hqN : q ∈ N.N) (hqU : q ∈ U)
    (Cprev : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hpC : p ∈ Cprev.carrier) :
    p ∈ (N.transfer p q hpN hpU hqN hqU Cprev hpC).1.carrier := by
  let R := N.transfer p q hpN hpU hqN hqU Cprev hpC
  change p ∈ R.1.carrier
  exact BHWJostOrientedTransitionData.source_mem_right_carrier R.2

/-- A branch-free transfer produces a next chart containing the target source
point. -/
theorem transfer_target_mem_next
    (N : BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    {p q : Fin n → Fin (d + 1) → ℂ}
    (hpN : p ∈ N.N) (hpU : p ∈ U)
    (hqN : q ∈ N.N) (hqU : q ∈ U)
    (Cprev : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hpC : p ∈ Cprev.carrier) :
    q ∈ (N.transfer p q hpN hpU hqN hqU Cprev hpC).1.carrier := by
  let R := N.transfer p q hpN hpU hqN hqU Cprev hpC
  change q ∈ R.1.carrier
  exact R.2.target_mem

/-- At the previous source point, a branch-free transfer preserves the stored
branch value when passing to the next chart. -/
theorem transfer_branch_agree_at_source
    (N : BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    {p q : Fin n → Fin (d + 1) → ℂ}
    (hpN : p ∈ N.N) (hpU : p ∈ U)
    (hqN : q ∈ N.N) (hqU : q ∈ U)
    (Cprev : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hpC : p ∈ Cprev.carrier) :
    Cprev.branch p =
      (N.transfer p q hpN hpU hqN hqU Cprev hpC).1.branch p := by
  let R := N.transfer p q hpN hpU hqN hqU Cprev hpC
  change Cprev.branch p = R.1.branch p
  exact BHWJostOrientedTransitionData.source_branch_agree_at_source R.2

end BHWJostOrientedBranchFreeTransferNeighborhood

/-- Transfer-neighborhood specialization of the path subdivision theorem.
This is the compactness step used before recursively applying branch-free
local continuation transfers. -/
theorem exists_unitInterval_orderedSubdivision_of_orientedTransferCover
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ : Continuous γ)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t)) :
    Nonempty
      (UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' (T t).N)) := by
  exact
    exists_unitInterval_orderedSubdivision_of_path_openCover
      γ hγ (fun t : unitInterval => (T t).N)
      (fun t => (T t).N_open)
      (fun t => (T t).center_mem)

/-- A selected finite ordered subdivision for a branch-free transfer
neighborhood cover along a source path. -/
noncomputable def unitInterval_orderedSubdivision_of_orientedTransferCover
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ : Continuous γ)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t)) :
    UnitIntervalOrderedSubdivision
      (fun t : unitInterval => γ ⁻¹' (T t).N) :=
  Classical.choice
    (exists_unitInterval_orderedSubdivision_of_orientedTransferCover
      γ hγ T)

/-- Each interval in a transfer-cover subdivision has both path endpoints in
one common branch-free transfer neighborhood. -/
theorem orientedTransferSubdivision_interval_endpoints_mem
    [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    {γ : unitInterval → Fin n → Fin (d + 1) → ℂ}
    {T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t)}
    (S :
      UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' (T t).N))
    (j : Fin S.m) :
    ∃ t : unitInterval,
      γ (S.t (Fin.castSucc j)) ∈ (T t).N ∧
      γ (S.t j.succ) ∈ (T t).N :=
  S.interval_endpoints_mem_cover j

/-- A finite oriented source-patch continuation chain from the fixed base
point `p0` to the endpoint `z`. -/
structure BHWJostOrientedSourcePatchContinuationChain
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (p0 z : Fin n → Fin (d + 1) → ℂ) where
  base_mem : p0 ∈ Ω0 ∩ U
  m : ℕ
  node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ
  node_zero : node 0 = p0
  node_last : node (Fin.last m) = z
  chart : Fin (m + 1) → Set (Fin n → Fin (d + 1) → ℂ)
  node_mem : ∀ j, node j ∈ chart j
  localChart :
    Fin (m + 1) → BHWJostLocalOrientedContinuationChart hd n τ U
  branch : Fin (m + 1) → (Fin n → Fin (d + 1) → ℂ) → ℂ
  chart_open : ∀ j, IsOpen (chart j)
  chart_preconnected : ∀ j, IsPreconnected (chart j)
  chart_sub_U : ∀ j, chart j ⊆ U
  chart_eq_local : ∀ j, chart j = (localChart j).carrier
  branch_eq_local :
    ∀ j y, y ∈ chart j → branch j y = (localChart j).branch y
  branch_holo : ∀ j, DifferentiableOn ℂ (branch j) (chart j)
  start_patch : Set (Fin n → Fin (d + 1) → ℂ)
  start_patch_open : IsOpen start_patch
  start_patch_preconnected : IsPreconnected start_patch
  start_patch_nonempty : start_patch.Nonempty
  start_mem : p0 ∈ start_patch
  start_patch_sub : start_patch ⊆ Ω0 ∩ chart 0
  start_agree :
    ∀ y, y ∈ start_patch → branch 0 y = B0 y
  transition_patch :
    ∀ _ : Fin m, Set (Fin n → Fin (d + 1) → ℂ)
  transition_patch_open : ∀ j, IsOpen (transition_patch j)
  transition_patch_nonempty : ∀ j, (transition_patch j).Nonempty
  transition_patch_preconnected :
    ∀ j, IsPreconnected (transition_patch j)
  transition_patch_sub_left :
    ∀ j, transition_patch j ⊆ chart (Fin.castSucc j)
  transition_patch_sub_right :
    ∀ j, transition_patch j ⊆ chart j.succ
  consecutive_agree :
    ∀ j : Fin m, ∀ y,
      y ∈ transition_patch j →
        branch (Fin.castSucc j) y = branch j.succ y
  oriented_transition :
    ∀ j : Fin m,
      BHWJostOrientedTransitionData hd n τ U
        (localChart (Fin.castSucc j)) (localChart j.succ)
        (node (Fin.castSucc j)) (node j.succ)
  final_mem : z ∈ chart (Fin.last m)
  chart_is_lorentz_step :
    ∀ j, ∃ Ωbase : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ωbase ∧
      Ωbase ⊆ os45SourcePatchBHWJostAmbient d n τ ∧
      ∃ Λ : ComplexLorentzGroup d,
        chart j = (fun u => complexLorentzAction Λ u) '' Ωbase

namespace BHWJostOrientedSourcePatchContinuationChain

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 z : Fin n → Fin (d + 1) → ℂ}

/-- The zero-step oriented continuation chain at the base point.  This is the
base case for the finite compact-path transfer recursion. -/
def base
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 p0 where
  base_mem := hbase
  m := 0
  node := fun _ => p0
  node_zero := rfl
  node_last := rfl
  chart := fun _ => C0.carrier
  node_mem := fun _ => hp0C
  localChart := fun _ => C0
  branch := fun _ => C0.branch
  chart_open := fun _ => C0.carrier_open
  chart_preconnected := fun _ => C0.carrier_preconnected
  chart_sub_U := fun _ => C0.carrier_sub_U
  chart_eq_local := fun _ => rfl
  branch_eq_local := fun _ _ _ => rfl
  branch_holo := fun _ => C0.branch_holo
  start_patch := start_patch
  start_patch_open := hstart_open
  start_patch_preconnected := hstart_preconnected
  start_patch_nonempty := hstart_nonempty
  start_mem := hstart_mem
  start_patch_sub := hstart_sub
  start_agree := hstart_agree
  transition_patch := fun j => Fin.elim0 j
  transition_patch_open := fun j => Fin.elim0 j
  transition_patch_nonempty := fun j => Fin.elim0 j
  transition_patch_preconnected := fun j => Fin.elim0 j
  transition_patch_sub_left := fun j => Fin.elim0 j
  transition_patch_sub_right := fun j => Fin.elim0 j
  consecutive_agree := fun j => Fin.elim0 j
  oriented_transition := fun j => Fin.elim0 j
  final_mem := hp0C
  chart_is_lorentz_step := fun _ => C0.carrier_is_lorentz_step

/-- Append one oriented transition step to a finite continuation chain.  This
is the successor case for the compact-path transfer recursion. -/
def snoc
    {p q : Fin n → Fin (d + 1) → ℂ}
    (C : BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 p)
    (Cnext : BHWJostLocalOrientedContinuationChart hd n τ U)
    (T :
      BHWJostOrientedTransitionData hd n τ U
        (C.localChart (Fin.last C.m)) Cnext
        (C.node (Fin.last C.m)) q) :
    BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 q where
  base_mem := C.base_mem
  m := C.m + 1
  node := Fin.snoc C.node q
  node_zero := by
    rw [show (0 : Fin (C.m + 1 + 1)) =
      Fin.castSucc (0 : Fin (C.m + 1)) from rfl]
    simpa [Fin.snoc_castSucc] using C.node_zero
  node_last := by
    simp
  chart := Fin.snoc C.chart Cnext.carrier
  node_mem := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using T.target_mem
    · intro i
      simpa [Fin.snoc_castSucc] using C.node_mem i
  localChart := Fin.snoc C.localChart Cnext
  branch := Fin.snoc C.branch Cnext.branch
  chart_open := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using Cnext.carrier_open
    · intro i
      simpa [Fin.snoc_castSucc] using C.chart_open i
  chart_preconnected := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using Cnext.carrier_preconnected
    · intro i
      simpa [Fin.snoc_castSucc] using C.chart_preconnected i
  chart_sub_U := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using Cnext.carrier_sub_U
    · intro i
      simpa [Fin.snoc_castSucc] using C.chart_sub_U i
  chart_eq_local := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simp [Fin.snoc_last]
    · intro i
      simpa [Fin.snoc_castSucc] using C.chart_eq_local i
  branch_eq_local := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · intro y hy
      simp [Fin.snoc_last]
    · intro i y hy
      have hyOld : y ∈ C.chart i := by
        have hchart :
            (@Fin.snoc (C.m + 1)
                (fun _ : Fin (C.m + 1 + 1) =>
                  Set (Fin n → Fin (d + 1) → ℂ))
                C.chart Cnext.carrier (Fin.castSucc i)) =
                C.chart i := by
            simp
        simpa [hchart] using hy
      simpa [Fin.snoc_castSucc] using C.branch_eq_local i y hyOld
  branch_holo := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using Cnext.branch_holo
    · intro i
      simpa [Fin.snoc_castSucc] using C.branch_holo i
  start_patch := C.start_patch
  start_patch_open := C.start_patch_open
  start_patch_preconnected := C.start_patch_preconnected
  start_patch_nonempty := C.start_patch_nonempty
  start_mem := C.start_mem
  start_patch_sub := by
    intro y hy
    have h := C.start_patch_sub hy
    simpa [Fin.snoc_castSucc] using h
  start_agree := C.start_agree
  transition_patch := Fin.snoc C.transition_patch T.sourcePatch
  transition_patch_open := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using T.sourcePatch_open
    · intro i
      simpa [Fin.snoc_castSucc] using C.transition_patch_open i
  transition_patch_nonempty := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using T.sourcePatch_nonempty
    · intro i
      simpa [Fin.snoc_castSucc] using C.transition_patch_nonempty i
  transition_patch_preconnected := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using T.sourcePatch_preconnected
    · intro i
      simpa [Fin.snoc_castSucc] using C.transition_patch_preconnected i
  transition_patch_sub_left := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · intro y hy
      have hyT : y ∈ T.sourcePatch := by
        simpa [Fin.snoc_last] using hy
      have hyLocal : y ∈ (C.localChart (Fin.last C.m)).carrier :=
        BHWJostOrientedTransitionData.sourcePatch_subset_left T hyT
      have hyChart : y ∈ C.chart (Fin.last C.m) := by
        simpa [C.chart_eq_local (Fin.last C.m)] using hyLocal
      simpa [Fin.snoc_castSucc] using hyChart
    · intro i y hy
      have hyOld : y ∈ C.transition_patch i := by
        simpa [Fin.snoc_castSucc] using hy
      have hyLeft := C.transition_patch_sub_left i hyOld
      simpa [Fin.snoc_castSucc] using hyLeft
  transition_patch_sub_right := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · intro y hy
      have hyT : y ∈ T.sourcePatch := by
        simpa [Fin.snoc_last] using hy
      have hyLocal : y ∈ Cnext.carrier :=
        BHWJostOrientedTransitionData.sourcePatch_subset_right T hyT
      simpa [Fin.snoc_last] using hyLocal
    · intro i y hy
      have hyOld : y ∈ C.transition_patch i := by
        simpa [Fin.snoc_castSucc] using hy
      have hyRight := C.transition_patch_sub_right i hyOld
      have hidx :
          (i.castSucc : Fin (C.m + 1)).succ = (i.succ).castSucc := by
        ext
        rfl
      have hchart :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              Set (Fin n → Fin (d + 1) → ℂ))
            C.chart Cnext.carrier (Fin.castSucc i.succ)) =
            C.chart i.succ := by
        simpa using
          (Fin.snoc_castSucc
            (α := fun _ : Fin (C.m + 1 + 1) =>
              Set (Fin n → Fin (d + 1) → ℂ))
            (x := Cnext.carrier) (p := C.chart) i.succ)
      have htarget :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              Set (Fin n → Fin (d + 1) → ℂ))
            C.chart Cnext.carrier (i.castSucc.succ)) =
            C.chart i.succ := by
        rw [hidx]
        exact hchart
      simpa [htarget] using hyRight
  consecutive_agree := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · intro y hy
      have hyT : y ∈ T.sourcePatch := by
        simpa [Fin.snoc_last] using hy
      have hyLocalLeft : y ∈ (C.localChart (Fin.last C.m)).carrier :=
        BHWJostOrientedTransitionData.sourcePatch_subset_left T hyT
      have hyChartLeft : y ∈ C.chart (Fin.last C.m) := by
        simpa [C.chart_eq_local (Fin.last C.m)] using hyLocalLeft
      have hbranch :
          C.branch (Fin.last C.m) y =
            (C.localChart (Fin.last C.m)).branch y :=
        C.branch_eq_local (Fin.last C.m) y hyChartLeft
      have hagree :=
        BHWJostOrientedTransitionData.source_branch_agree_of_oriented T hyT
      exact by
        simpa [Fin.snoc_castSucc, Fin.snoc_last] using hbranch.trans hagree
    · intro i y hy
      have hyOld : y ∈ C.transition_patch i := by
        simpa [Fin.snoc_castSucc] using hy
      have hagree := C.consecutive_agree i y hyOld
      have hidx :
          (i.castSucc : Fin (C.m + 1)).succ = (i.succ).castSucc := by
        ext
        rfl
      have hleft :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              (Fin n → Fin (d + 1) → ℂ) → ℂ)
            C.branch Cnext.branch (Fin.castSucc i.castSucc)) =
            C.branch i.castSucc := by
        simp
      have hright_cast :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              (Fin n → Fin (d + 1) → ℂ) → ℂ)
            C.branch Cnext.branch (Fin.castSucc i.succ)) =
            C.branch i.succ := by
        simpa using
          (Fin.snoc_castSucc
            (α := fun _ : Fin (C.m + 1 + 1) =>
              (Fin n → Fin (d + 1) → ℂ) → ℂ)
            (x := Cnext.branch) (p := C.branch) i.succ)
      have hright :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              (Fin n → Fin (d + 1) → ℂ) → ℂ)
            C.branch Cnext.branch (i.castSucc.succ)) =
            C.branch i.succ := by
        rw [hidx]
        exact hright_cast
      simpa [hleft, hright] using hagree
  oriented_transition := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_castSucc, Fin.snoc_last] using T
    · intro i
      have hidx :
          (i.castSucc : Fin (C.m + 1)).succ = (i.succ).castSucc := by
        ext
        rfl
      have hchart_left :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              BHWJostLocalOrientedContinuationChart hd n τ U)
            C.localChart Cnext (Fin.castSucc i.castSucc)) =
            C.localChart i.castSucc := by
        simp
      have hchart_right_cast :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              BHWJostLocalOrientedContinuationChart hd n τ U)
            C.localChart Cnext (Fin.castSucc i.succ)) =
            C.localChart i.succ := by
        simpa using
          (Fin.snoc_castSucc
            (α := fun _ : Fin (C.m + 1 + 1) =>
              BHWJostLocalOrientedContinuationChart hd n τ U)
            (x := Cnext) (p := C.localChart) i.succ)
      have hchart_right :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              BHWJostLocalOrientedContinuationChart hd n τ U)
            C.localChart Cnext (i.castSucc.succ)) =
            C.localChart i.succ := by
        rw [hidx]
        exact hchart_right_cast
      have hnode_left :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              Fin n → Fin (d + 1) → ℂ)
            C.node q (Fin.castSucc i.castSucc)) =
            C.node i.castSucc := by
        simp
      have hnode_right_cast :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              Fin n → Fin (d + 1) → ℂ)
            C.node q (Fin.castSucc i.succ)) =
            C.node i.succ := by
        simpa using
          (Fin.snoc_castSucc
            (α := fun _ : Fin (C.m + 1 + 1) =>
              Fin n → Fin (d + 1) → ℂ)
            (x := q) (p := C.node) i.succ)
      have hnode_right :
          (@Fin.snoc (C.m + 1)
            (fun _ : Fin (C.m + 1 + 1) =>
              Fin n → Fin (d + 1) → ℂ)
            C.node q (i.castSucc.succ)) =
            C.node i.succ := by
        rw [hidx]
        exact hnode_right_cast
      simpa [hchart_left, hchart_right, hnode_left, hnode_right] using
        C.oriented_transition i
  final_mem := by
    simpa [Fin.snoc_last] using T.target_mem
  chart_is_lorentz_step := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using Cnext.carrier_is_lorentz_step
    · intro i
      simpa [Fin.snoc_castSucc] using C.chart_is_lorentz_step i

/-- Retarget a continuation chain to any point in its terminal chart by
appending the tautological transition from the terminal chart to itself. -/
def retargetTerminal
    (C : BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z)
    {y : Fin n → Fin (d + 1) → ℂ}
    (hy : y ∈ C.chart (Fin.last C.m)) :
    BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 y :=
  snoc (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    (p0 := p0) C (C.localChart (Fin.last C.m))
    (BHWJostOrientedTransitionData.sameChart
      (C.localChart (Fin.last C.m))
      (p := C.node (Fin.last C.m)) (q := y)
      (by
        simpa [C.chart_eq_local (Fin.last C.m)] using
          C.node_mem (Fin.last C.m))
      (by
        simpa [C.chart_eq_local (Fin.last C.m)] using hy))

/-- A finite sequence of source nodes, together with a one-step transition
rule for every adjacent pair, produces an oriented continuation chain.  This
is the pure finite-recursion layer behind the compact-path construction. -/
theorem exists_of_nodeSteps
    {m : ℕ}
    (node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ)
    (hnode_zero : node 0 = p0)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (step :
      ∀ j : Fin m,
        ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
          node (Fin.castSucc j) ∈ Cprev.carrier →
            Σ Cnext : BHWJostLocalOrientedContinuationChart hd n τ U,
              BHWJostOrientedTransitionData hd n τ U Cprev Cnext
                (node (Fin.castSucc j)) (node j.succ)) :
    Nonempty
      (BHWJostOrientedSourcePatchContinuationChain
        hd n τ Ω0 U B0 p0 (node (Fin.last m))) := by
  induction m with
  | zero =>
      have hlast : node (Fin.last 0) = p0 := by
        simpa using hnode_zero
      refine ⟨?_⟩
      rw [hlast]
      exact
        base (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
          (p0 := p0) C0 hbase hp0C start_patch hstart_open
          hstart_preconnected hstart_nonempty hstart_mem hstart_sub
          hstart_agree
  | succ m ih =>
      let nodePrefix : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ :=
        fun i => node (Fin.castSucc i)
      have hnode_zero_prefix : nodePrefix 0 = p0 := by
        simpa [nodePrefix] using hnode_zero
      have stepPrefix :
          ∀ j : Fin m,
            ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
              nodePrefix (Fin.castSucc j) ∈ Cprev.carrier →
                Σ Cnext : BHWJostLocalOrientedContinuationChart hd n τ U,
                  BHWJostOrientedTransitionData hd n τ U Cprev Cnext
                    (nodePrefix (Fin.castSucc j)) (nodePrefix j.succ) := by
        intro j Cprev hpC
        simpa [nodePrefix] using
          (step (Fin.castSucc j) Cprev hpC)
      rcases ih nodePrefix hnode_zero_prefix stepPrefix with
        ⟨Cprev⟩
      have hpLast :
          node (Fin.castSucc (Fin.last m)) ∈
            (Cprev.localChart (Fin.last Cprev.m)).carrier := by
        have hfinal :
            nodePrefix (Fin.last m) ∈
              Cprev.chart (Fin.last Cprev.m) :=
          Cprev.final_mem
        simpa [nodePrefix, Cprev.chart_eq_local (Fin.last Cprev.m)]
          using hfinal
      let R := step (Fin.last m)
        (Cprev.localChart (Fin.last Cprev.m)) hpLast
      have hterminal :
          Cprev.node (Fin.last Cprev.m) =
            node (Fin.castSucc (Fin.last m)) := by
        simpa [nodePrefix] using Cprev.node_last
      have Tlast :
          BHWJostOrientedTransitionData hd n τ U
            (Cprev.localChart (Fin.last Cprev.m)) R.1
            (Cprev.node (Fin.last Cprev.m)) (node (Fin.last m).succ) := by
        simpa [hterminal] using R.2
      have hlast_succ :
          (Fin.last m).succ = Fin.last (m + 1) := by
        ext
        rfl
      refine ⟨?_⟩
      simpa [hlast_succ] using
        (snoc (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
          (p0 := p0) Cprev R.1 Tlast)

/-- Noncomputably select the chain produced from finite node-step data. -/
noncomputable def ofNodeSteps
    {m : ℕ}
    (node : Fin (m + 1) → Fin n → Fin (d + 1) → ℂ)
    (hnode_zero : node 0 = p0)
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y)
    (step :
      ∀ j : Fin m,
        ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
          node (Fin.castSucc j) ∈ Cprev.carrier →
            Σ Cnext : BHWJostLocalOrientedContinuationChart hd n τ U,
              BHWJostOrientedTransitionData hd n τ U Cprev Cnext
                (node (Fin.castSucc j)) (node j.succ)) :
    BHWJostOrientedSourcePatchContinuationChain
      hd n τ Ω0 U B0 p0 (node (Fin.last m)) :=
  Classical.choice
    (exists_of_nodeSteps (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U)
      (B0 := B0) (p0 := p0) node hnode_zero C0 hbase hp0C
      start_patch hstart_open hstart_preconnected hstart_nonempty
      hstart_mem hstart_sub hstart_agree step)

/-- A source path with a subdivision subordinate to branch-free transfer
neighborhoods produces an oriented continuation chain from the initial to the
terminal endpoint. -/
theorem exists_of_subdivision
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (S :
      UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' (T t).N))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    Nonempty
      (BHWJostOrientedSourcePatchContinuationChain
        hd n τ Ω0 U B0 p0 (γ 1)) := by
  have hnode_zero :
      (fun j : Fin (S.m + 1) => γ (S.t j)) 0 = p0 := by
    simpa [S.t_zero] using hγ_zero
  have hsteps :
      ∀ j : Fin S.m,
        ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
          (fun j : Fin (S.m + 1) => γ (S.t j)) (Fin.castSucc j) ∈
              Cprev.carrier →
            Σ Cnext : BHWJostLocalOrientedContinuationChart hd n τ U,
              BHWJostOrientedTransitionData hd n τ U Cprev Cnext
                ((fun j : Fin (S.m + 1) => γ (S.t j)) (Fin.castSucc j))
                ((fun j : Fin (S.m + 1) => γ (S.t j)) j.succ) := by
    intro j Cprev hpC
    let t : unitInterval := Classical.choose (S.interval_endpoints_mem_cover j)
    have ht := Classical.choose_spec (S.interval_endpoints_mem_cover j)
    exact
      (T t).transfer
        (γ (S.t (Fin.castSucc j))) (γ (S.t j.succ))
        ht.1 (hγU (S.t (Fin.castSucc j)))
        ht.2 (hγU (S.t j.succ)) Cprev hpC
  have hchain :=
    exists_of_nodeSteps (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U)
      (B0 := B0) (p0 := p0)
      (node := fun j : Fin (S.m + 1) => γ (S.t j))
      hnode_zero C0 hbase hp0C start_patch hstart_open
      hstart_preconnected hstart_nonempty hstart_mem hstart_sub
      hstart_agree hsteps
  simpa [S.t_last] using hchain

/-- Noncomputably select the chain produced from a path subdivision and its
branch-free transfer neighborhoods. -/
noncomputable def ofSubdivision
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (S :
      UnitIntervalOrderedSubdivision
        (fun t : unitInterval => γ ⁻¹' (T t).N))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedSourcePatchContinuationChain
      hd n τ Ω0 U B0 p0 (γ 1) :=
  Classical.choice
    (exists_of_subdivision (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U)
      (B0 := B0) (p0 := p0) γ hγ_zero hγU T S C0 hbase hp0C
      start_patch hstart_open hstart_preconnected hstart_nonempty
      hstart_mem hstart_sub hstart_agree)

/-- A continuous source path with branch-free transfer neighborhoods along
the path produces an oriented continuation chain after selecting the compact
subdivision of the transfer cover. -/
theorem exists_of_transferCover
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ : Continuous γ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    Nonempty
      (BHWJostOrientedSourcePatchContinuationChain
        hd n τ Ω0 U B0 p0 (γ 1)) := by
  exact
    exists_of_subdivision (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U)
      (B0 := B0) (p0 := p0) γ hγ_zero hγU T
      (unitInterval_orderedSubdivision_of_orientedTransferCover
        (hd := hd) (τ := τ) γ hγ T)
      C0 hbase hp0C start_patch hstart_open hstart_preconnected
      hstart_nonempty hstart_mem hstart_sub hstart_agree

/-- Noncomputably select the continuation chain produced by the compact
transfer-cover subdivision of a continuous source path. -/
noncomputable def ofTransferCover
    (γ : unitInterval → Fin n → Fin (d + 1) → ℂ)
    (hγ : Continuous γ)
    (hγ_zero : γ 0 = p0)
    (hγU : ∀ t : unitInterval, γ t ∈ U)
    (T :
      ∀ t : unitInterval,
        BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U (γ t))
    (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
    (hbase : p0 ∈ Ω0 ∩ U)
    (hp0C : p0 ∈ C0.carrier)
    (start_patch : Set (Fin n → Fin (d + 1) → ℂ))
    (hstart_open : IsOpen start_patch)
    (hstart_preconnected : IsPreconnected start_patch)
    (hstart_nonempty : start_patch.Nonempty)
    (hstart_mem : p0 ∈ start_patch)
    (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
    (hstart_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y) :
    BHWJostOrientedSourcePatchContinuationChain
      hd n τ Ω0 U B0 p0 (γ 1) :=
  Classical.choice
    (exists_of_transferCover (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U)
      (B0 := B0) (p0 := p0) γ hγ hγ_zero hγU T C0 hbase hp0C
      start_patch hstart_open hstart_preconnected hstart_nonempty
      hstart_mem hstart_sub hstart_agree)

/-- Consecutive local oriented charts agree on the stored transition source
patch. -/
theorem localChart_consecutive_agree
    (C : BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z)
    (j : Fin C.m) :
    Set.EqOn
      (C.localChart (Fin.castSucc j)).branch
      (C.localChart j.succ).branch
      (C.transition_patch j) := by
  intro y hy
  have hyLeft : y ∈ C.chart (Fin.castSucc j) :=
    C.transition_patch_sub_left j hy
  have hyRight : y ∈ C.chart j.succ :=
    C.transition_patch_sub_right j hy
  calc
    (C.localChart (Fin.castSucc j)).branch y =
        C.branch (Fin.castSucc j) y :=
      (C.branch_eq_local (Fin.castSucc j) y hyLeft).symm
    _ = C.branch j.succ y :=
      C.consecutive_agree j y hy
    _ = (C.localChart j.succ).branch y :=
      C.branch_eq_local j.succ y hyRight

/-- The chain-level consecutive branch equality follows from the oriented
transition data and the local-chart branch identifications. -/
theorem consecutive_agree_of_oriented_transition
    (C : BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z)
    (j : Fin C.m) :
    ∀ y, y ∈ C.transition_patch j →
      C.branch (Fin.castSucc j) y = C.branch j.succ y := by
  intro y hy
  have hyLeft : y ∈ C.chart (Fin.castSucc j) :=
    C.transition_patch_sub_left j hy
  have hyRight : y ∈ C.chart j.succ :=
    C.transition_patch_sub_right j hy
  rw [C.branch_eq_local (Fin.castSucc j) y hyLeft,
    C.branch_eq_local j.succ y hyRight]
  exact localChart_consecutive_agree C j hy

/-- The Lorentz-step provenance of a chain chart is inherited from its stored
local oriented chart. -/
theorem chart_is_lorentz_step_of_localChart
    (C : BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z)
    (j : Fin (C.m + 1)) :
    ∃ Ωbase : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ωbase ∧
      Ωbase ⊆ os45SourcePatchBHWJostAmbient d n τ ∧
      ∃ Λ : ComplexLorentzGroup d,
        C.chart j = (fun u => complexLorentzAction Λ u) '' Ωbase := by
  rcases (C.localChart j).carrier_is_lorentz_step with
    ⟨Ωbase, hΩopen, hΩsub, Λ, hΛ⟩
  refine ⟨Ωbase, hΩopen, hΩsub, Λ, ?_⟩
  rw [C.chart_eq_local j]
  exact hΛ

end BHWJostOrientedSourcePatchContinuationChain

/-- Point value of the terminal branch carried by an oriented continuation
chain. -/
def bhw_continuedValueAlongOrientedChain
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    {p0 z : Fin n → Fin (d + 1) → ℂ}
    (C : BHWJostOrientedSourcePatchContinuationChain
      hd n τ Ω0 U B0 p0 z) : ℂ :=
  C.branch (Fin.last C.m) z

namespace BHWJostOrientedSourcePatchContinuationChain

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 z : Fin n → Fin (d + 1) → ℂ}

/-- The continued value of a terminal-retargeted chain is the original
terminal branch evaluated at the new terminal point. -/
theorem retargetTerminal_continuedValue_eq_branch
    (C : BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z)
    {y : Fin n → Fin (d + 1) → ℂ}
    (hy : y ∈ C.chart (Fin.last C.m)) :
    bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0
        (C.retargetTerminal hy) =
      C.branch (Fin.last C.m) y := by
  simpa [bhw_continuedValueAlongOrientedChain, retargetTerminal, snoc] using
    (C.branch_eq_local (Fin.last C.m) y hy).symm

end BHWJostOrientedSourcePatchContinuationChain

/-- A closed oriented continuation loop at the fixed base point. -/
structure BHWJostOrientedClosedContinuationLoop
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (p0 : Fin n → Fin (d + 1) → ℂ) where
  chain :
    BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 p0
  final_base_mem : p0 ∈ chain.chart (Fin.last chain.m)
  closing_patch : Set (Fin n → Fin (d + 1) → ℂ)
  closing_patch_open : IsOpen closing_patch
  closing_patch_preconnected : IsPreconnected closing_patch
  closing_patch_nonempty : closing_patch.Nonempty
  closing_patch_mem : p0 ∈ closing_patch
  closing_patch_sub_start : closing_patch ⊆ chain.start_patch
  closing_patch_sub_final : closing_patch ⊆ chain.chart (Fin.last chain.m)
  closing_orientedPatch : Set (SourceOrientedGramData d n)
  closing_orientedPatch_relOpen :
    IsRelOpenInSourceOrientedGramVariety d n closing_orientedPatch
  closing_orientedPatch_preconnected : IsPreconnected closing_orientedPatch
  closing_orientedPatch_nonempty : closing_orientedPatch.Nonempty
  closing_orientedPatch_sub_start :
    closing_orientedPatch ⊆ (chain.localChart 0).orientedDomain
  closing_orientedPatch_sub_final :
    closing_orientedPatch ⊆
      (chain.localChart (Fin.last chain.m)).orientedDomain
  closing_patch_oriented_mem :
    ∀ y, y ∈ closing_patch →
      sourceOrientedMinkowskiInvariant d n y ∈ closing_orientedPatch

namespace BHWJostOrientedClosedContinuationLoop

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}

/-- The closing source patch lies in the initial chain chart. -/
theorem closing_patch_subset_initial_chart
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
    L.closing_patch ⊆ L.chain.chart 0 := by
  intro y hy
  exact (L.chain.start_patch_sub (L.closing_patch_sub_start hy)).2

/-- The closing source patch lies in the initial local chart carrier. -/
theorem closing_patch_subset_initial_localChart
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
    L.closing_patch ⊆ (L.chain.localChart 0).carrier := by
  intro y hy
  simpa [L.chain.chart_eq_local 0] using
    closing_patch_subset_initial_chart L hy

/-- The closing source patch lies in the final local chart carrier. -/
theorem closing_patch_subset_final_localChart
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
    L.closing_patch ⊆
      (L.chain.localChart (Fin.last L.chain.m)).carrier := by
  intro y hy
  simpa [L.chain.chart_eq_local (Fin.last L.chain.m)] using
    L.closing_patch_sub_final hy

/-- The stored closing oriented patch of a closed loop is connected. -/
theorem closing_orientedPatch_connected
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
    IsConnected L.closing_orientedPatch :=
  ⟨L.closing_orientedPatch_nonempty, L.closing_orientedPatch_preconnected⟩

/-- Every point of the closing oriented patch has source representatives in
the initial and terminal chart carriers. -/
theorem exists_initial_final_source_realizations_of_closing
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ L.closing_orientedPatch) :
    ∃ y0 yF,
      y0 ∈ (L.chain.localChart 0).carrier ∧
      yF ∈ (L.chain.localChart (Fin.last L.chain.m)).carrier ∧
      sourceOrientedMinkowskiInvariant d n y0 = G ∧
      sourceOrientedMinkowskiInvariant d n yF = G := by
  have hGstart : G ∈ (L.chain.localChart 0).orientedDomain :=
    L.closing_orientedPatch_sub_start hG
  have hGfinal :
      G ∈ (L.chain.localChart (Fin.last L.chain.m)).orientedDomain :=
    L.closing_orientedPatch_sub_final hG
  rcases (L.chain.localChart 0).oriented_realizes G hGstart with
    ⟨y0, hy0, hy0G⟩
  rcases (L.chain.localChart (Fin.last L.chain.m)).oriented_realizes
      G hGfinal with
    ⟨yF, hyF, hyFG⟩
  exact ⟨y0, yF, hy0, hyF, hy0G, hyFG⟩

/-- The source representatives of a closing oriented point can be chosen with
their branch values rewritten as the corresponding oriented germs. -/
theorem exists_initial_final_source_realizations_branch_eqs_of_closing
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ L.closing_orientedPatch) :
    ∃ y0 yF,
      y0 ∈ (L.chain.localChart 0).carrier ∧
      yF ∈ (L.chain.localChart (Fin.last L.chain.m)).carrier ∧
      sourceOrientedMinkowskiInvariant d n y0 = G ∧
      sourceOrientedMinkowskiInvariant d n yF = G ∧
      (L.chain.localChart 0).branch y0 =
        (L.chain.localChart 0).Psi G ∧
      (L.chain.localChart (Fin.last L.chain.m)).branch yF =
        (L.chain.localChart (Fin.last L.chain.m)).Psi G := by
  rcases L.exists_initial_final_source_realizations_of_closing hG with
    ⟨y0, yF, hy0, hyF, hy0G, hyFG⟩
  refine ⟨y0, yF, hy0, hyF, hy0G, hyFG, ?_, ?_⟩
  · rw [(L.chain.localChart 0).branch_eq_orientedPullback y0 hy0, hy0G]
  · rw [(L.chain.localChart (Fin.last L.chain.m)).branch_eq_orientedPullback
      yF hyF, hyFG]

/-- Oriented monodromy on the closing invariant patch descends to equality of
the terminal and initial source branches on the closing source patch. -/
theorem terminal_branch_eq_initial_branch_of_orientedMonodromy
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    (hmon :
      Set.EqOn
        (L.chain.localChart (Fin.last L.chain.m)).Psi
        (L.chain.localChart 0).Psi
        L.closing_orientedPatch) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      (L.chain.branch 0)
      L.closing_patch := by
  intro y hy
  have hyFinalChart : y ∈ L.chain.chart (Fin.last L.chain.m) :=
    L.closing_patch_sub_final hy
  have hyFinalLocal :
      y ∈ (L.chain.localChart (Fin.last L.chain.m)).carrier := by
    simpa [L.chain.chart_eq_local (Fin.last L.chain.m)] using hyFinalChart
  have hyStartPatch : y ∈ L.chain.start_patch :=
    L.closing_patch_sub_start hy
  have hyStartChart : y ∈ L.chain.chart 0 :=
    (L.chain.start_patch_sub hyStartPatch).2
  have hyStartLocal : y ∈ (L.chain.localChart 0).carrier := by
    simpa [L.chain.chart_eq_local 0] using hyStartChart
  rw [L.chain.branch_eq_local (Fin.last L.chain.m) y hyFinalChart,
    L.chain.branch_eq_local 0 y hyStartChart,
    (L.chain.localChart (Fin.last L.chain.m)).branch_eq_orientedPullback
      y hyFinalLocal,
    (L.chain.localChart 0).branch_eq_orientedPullback y hyStartLocal]
  exact hmon (L.closing_patch_oriented_mem y hy)

/-- Oriented monodromy on the closing invariant patch gives the terminal
source branch normalized by the initial branch `B0` on the closing source
patch. -/
theorem terminal_branch_eq_B0_of_orientedMonodromy
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    (hmon :
      Set.EqOn
        (L.chain.localChart (Fin.last L.chain.m)).Psi
        (L.chain.localChart 0).Psi
        L.closing_orientedPatch) :
    Set.EqOn (L.chain.branch (Fin.last L.chain.m)) B0 L.closing_patch := by
  intro y hy
  calc
    L.chain.branch (Fin.last L.chain.m) y = L.chain.branch 0 y :=
      terminal_branch_eq_initial_branch_of_orientedMonodromy L hmon hy
    _ = B0 y := L.chain.start_agree y (L.closing_patch_sub_start hy)

end BHWJostOrientedClosedContinuationLoop

/-- Source-level closed-loop monodromy is mechanical once oriented monodromy
has been proved on the closing invariant patch. -/
theorem bhw_jost_orientedClosedChain_sourceMonodromy_of_orientedMonodromy
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
    (hmon :
      Set.EqOn
        (L.chain.localChart (Fin.last L.chain.m)).Psi
        (L.chain.localChart 0).Psi
        L.closing_orientedPatch) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      L.closing_patch :=
  BHWJostOrientedClosedContinuationLoop.terminal_branch_eq_B0_of_orientedMonodromy
    L hmon

/-- The max-rank seed produced by the genuine BHW/Jost closed-loop
single-valuedness theorem.  The propagation from this seed is a separate
identity-principle step. -/
structure BHWJostOrientedMaxRankClosedLoopSeed
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    {p0 : Fin n → Fin (d + 1) → ℂ}
    (L : BHWJostOrientedClosedContinuationLoop
      hd n τ Ω0 U B0 p0) where
  seed : Set (SourceOrientedGramData d n)
  seed_relOpen : IsRelOpenInSourceOrientedGramVariety d n seed
  seed_preconnected : IsPreconnected seed
  seed_nonempty : seed.Nonempty
  seed_sub :
    seed ⊆ L.closing_orientedPatch ∩
      {G | SourceOrientedMaxRankAt d n G}
  seed_eq :
    Set.EqOn
      (L.chain.localChart (Fin.last L.chain.m)).Psi
      (L.chain.localChart 0).Psi
      seed

namespace BHWJostOrientedMaxRankClosedLoopSeed

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 : Fin n → Fin (d + 1) → ℂ}
variable {L : BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}

/-- The max-rank monodromy seed lies inside the closing oriented patch. -/
theorem seed_subset_closing_orientedPatch
    (S : BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :
    S.seed ⊆ L.closing_orientedPatch := by
  intro G hG
  exact (S.seed_sub hG).1

/-- Every point of the closed-loop seed is in the maximal oriented rank
stratum. -/
theorem seed_subset_maxRank
    (S : BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :
    S.seed ⊆ {G | SourceOrientedMaxRankAt d n G} := by
  intro G hG
  exact (S.seed_sub hG).2

/-- A seed point has initial and final source representatives, and the two
stored source branches agree on those representatives. -/
theorem exists_initial_final_source_realizations
    (S : BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ S.seed) :
    ∃ y0 yF,
      y0 ∈ (L.chain.localChart 0).carrier ∧
      yF ∈ (L.chain.localChart (Fin.last L.chain.m)).carrier ∧
      sourceOrientedMinkowskiInvariant d n y0 = G ∧
      sourceOrientedMinkowskiInvariant d n yF = G ∧
      (L.chain.localChart (Fin.last L.chain.m)).branch yF =
        (L.chain.localChart 0).branch y0 := by
  have hGclosing : G ∈ L.closing_orientedPatch :=
    seed_subset_closing_orientedPatch S hG
  have hGstart : G ∈ (L.chain.localChart 0).orientedDomain :=
    L.closing_orientedPatch_sub_start hGclosing
  have hGfinal :
      G ∈ (L.chain.localChart (Fin.last L.chain.m)).orientedDomain :=
    L.closing_orientedPatch_sub_final hGclosing
  rcases (L.chain.localChart 0).oriented_realizes G hGstart with
    ⟨y0, hy0, hy0G⟩
  rcases (L.chain.localChart (Fin.last L.chain.m)).oriented_realizes
      G hGfinal with
    ⟨yF, hyF, hyFG⟩
  refine ⟨y0, yF, hy0, hyF, hy0G, hyFG, ?_⟩
  rw [(L.chain.localChart (Fin.last L.chain.m)).branch_eq_orientedPullback
      yF hyF,
    (L.chain.localChart 0).branch_eq_orientedPullback y0 hy0,
    hyFG, hy0G]
  exact S.seed_eq hG

/-- On source points of the closing patch whose oriented invariant lies in
the seed, seed monodromy already gives the terminal branch normalized by
`B0`.  The remaining global closed-loop step is the identity-principle
propagation from this seed to the whole closing oriented patch. -/
theorem terminal_branch_eq_B0_on_seedRealizedClosingPatch
    (S : BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :
    Set.EqOn
      (L.chain.branch (Fin.last L.chain.m))
      B0
      {y | y ∈ L.closing_patch ∧
        sourceOrientedMinkowskiInvariant d n y ∈ S.seed} := by
  intro y hy
  rcases hy with ⟨hyClosing, hySeed⟩
  have hyFinalChart : y ∈ L.chain.chart (Fin.last L.chain.m) :=
    L.closing_patch_sub_final hyClosing
  have hyFinalLocal :
      y ∈ (L.chain.localChart (Fin.last L.chain.m)).carrier := by
    simpa [L.chain.chart_eq_local (Fin.last L.chain.m)] using hyFinalChart
  have hyStartPatch : y ∈ L.chain.start_patch :=
    L.closing_patch_sub_start hyClosing
  have hyStartChart : y ∈ L.chain.chart 0 :=
    (L.chain.start_patch_sub hyStartPatch).2
  have hyStartLocal : y ∈ (L.chain.localChart 0).carrier := by
    simpa [L.chain.chart_eq_local 0] using hyStartChart
  calc
    L.chain.branch (Fin.last L.chain.m) y = L.chain.branch 0 y := by
      rw [L.chain.branch_eq_local (Fin.last L.chain.m) y hyFinalChart,
        L.chain.branch_eq_local 0 y hyStartChart,
        (L.chain.localChart (Fin.last L.chain.m)).branch_eq_orientedPullback
          y hyFinalLocal,
        (L.chain.localChart 0).branch_eq_orientedPullback y hyStartLocal]
      exact S.seed_eq hySeed
    _ = B0 y := L.chain.start_agree y hyStartPatch

end BHWJostOrientedMaxRankClosedLoopSeed

/-- A source-patch continuation atlas assembled from continuation chains. -/
structure BHWSourcePatchContinuationAtlas
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  chart : Type
  carrier : chart → Set (Fin n → Fin (d + 1) → ℂ)
  branch : chart → (Fin n → Fin (d + 1) → ℂ) → ℂ
  cover : ∀ z, z ∈ U → ∃ a, z ∈ carrier a
  carrier_open : ∀ a, IsOpen (carrier a)
  carrier_sub_U : ∀ a, carrier a ⊆ U
  branch_holo : ∀ a, DifferentiableOn ℂ (branch a) (carrier a)
  overlap_eq :
    ∀ a b, Set.EqOn (branch a) (branch b) (carrier a ∩ carrier b)
  base_agree :
    ∀ z, z ∈ Ω0 ∩ U →
      ∃ a, z ∈ carrier a ∧ branch a z = B0 z

namespace BHWSourcePatchContinuationAtlas

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}

/-- The glued branch obtained by choosing any atlas chart through a point of
`U`.  The overlap field proves this choice is independent on `U`. -/
noncomputable def glued
    (A : BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z =>
    if hz : z ∈ U then
      A.branch (Classical.choose (A.cover z hz)) z
    else 0

/-- The glued branch agrees with any atlas branch on that branch's carrier. -/
theorem glued_eq_branch_of_mem
    (A : BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0)
    {a : A.chart} {z : Fin n → Fin (d + 1) → ℂ}
    (hzU : z ∈ U) (hza : z ∈ A.carrier a) :
    A.glued z = A.branch a z := by
  unfold glued
  rw [dif_pos hzU]
  let b := Classical.choose (A.cover z hzU)
  have hzb : z ∈ A.carrier b :=
    Classical.choose_spec (A.cover z hzU)
  exact A.overlap_eq b a ⟨hzb, hza⟩

/-- The glued atlas branch is holomorphic on the covered source patch `U`. -/
theorem glued_differentiableOn
    (A : BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0) :
    DifferentiableOn ℂ A.glued U := by
  intro z hzU
  rcases A.cover z hzU with ⟨a, hza⟩
  have hdiffAt : DifferentiableAt ℂ (A.branch a) z :=
    (A.branch_holo a).differentiableAt
      ((A.carrier_open a).mem_nhds hza)
  refine hdiffAt.differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((A.carrier_open a).mem_nhds hza)]
      with w hwU hwa
    exact A.glued_eq_branch_of_mem hwU hwa
  · exact A.glued_eq_branch_of_mem hzU hza

/-- On the initial source patch, the glued branch has the prescribed initial
branch value. -/
theorem glued_eq_B0_of_mem
    (A : BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ Ω0 ∩ U) :
    A.glued z = B0 z := by
  rcases A.base_agree z hz with ⟨a, hza, hbranch⟩
  calc
    A.glued z = A.branch a z := A.glued_eq_branch_of_mem hz.2 hza
    _ = B0 z := hbranch

end BHWSourcePatchContinuationAtlas

/-- Glue a source-patch continuation atlas into a single holomorphic branch on
`U`.  All analytic continuation content is in the atlas fields; this theorem
only performs the sheaf-style choice and overlap-independence step. -/
theorem bhw_glue_sourcePatchContinuationAtlas
    [NeZero d] (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (A : BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) := by
  refine ⟨A.glued, A.glued_differentiableOn, ?_⟩
  intro z hzΩ hzU
  exact A.glued_eq_B0_of_mem ⟨hzΩ, hzU⟩

end BHW
