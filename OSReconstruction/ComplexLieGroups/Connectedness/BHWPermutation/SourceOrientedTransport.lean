import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation

/-!
# Transport equivalences for oriented source invariants

The rank-deficient normal-form route transports a normal Schur chart back to
the original oriented source coordinates.  This file records the purely
topological/algebraic interface for such transports.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A homeomorphic change of oriented source-invariant coordinates preserving
the oriented source variety and the maximal-rank predicate. -/
structure SourceOrientedInvariantTransportEquiv (d n : ℕ) where
  toHomeomorph :
    SourceOrientedGramData d n ≃ₜ SourceOrientedGramData d n
  mem_variety_iff :
    ∀ G,
      toHomeomorph G ∈ sourceOrientedGramVariety d n ↔
        G ∈ sourceOrientedGramVariety d n
  maxRank_iff :
    ∀ G,
      SourceOrientedMaxRankAt d n (toHomeomorph G) ↔
        SourceOrientedMaxRankAt d n G

namespace SourceOrientedInvariantTransportEquiv

variable {d n : ℕ}

/-- Forward coordinate transport. -/
def toFun (T : SourceOrientedInvariantTransportEquiv d n) :
    SourceOrientedGramData d n → SourceOrientedGramData d n :=
  T.toHomeomorph

/-- Inverse coordinate transport. -/
def invFun (T : SourceOrientedInvariantTransportEquiv d n) :
    SourceOrientedGramData d n → SourceOrientedGramData d n :=
  T.toHomeomorph.symm

/-- The inverse transport is a left inverse to the forward transport. -/
theorem left_inv (T : SourceOrientedInvariantTransportEquiv d n) :
    Function.LeftInverse T.invFun T.toFun := by
  intro G
  exact T.toHomeomorph.left_inv G

/-- The inverse transport is a right inverse to the forward transport. -/
theorem right_inv (T : SourceOrientedInvariantTransportEquiv d n) :
    Function.RightInverse T.invFun T.toFun := by
  intro G
  exact T.toHomeomorph.right_inv G

/-- Forward transport is continuous. -/
theorem continuous_toFun (T : SourceOrientedInvariantTransportEquiv d n) :
    Continuous T.toFun :=
  T.toHomeomorph.continuous

/-- Inverse transport is continuous. -/
theorem continuous_invFun (T : SourceOrientedInvariantTransportEquiv d n) :
    Continuous T.invFun :=
  T.toHomeomorph.symm.continuous

/-- Images under the inverse transport of open sets are open. -/
theorem isOpen_invFun_image
    (T : SourceOrientedInvariantTransportEquiv d n)
    {Ω : Set (SourceOrientedGramData d n)}
    (hΩ : IsOpen Ω) :
    IsOpen (T.invFun '' Ω) := by
  simpa [invFun] using T.toHomeomorph.symm.isOpenMap Ω hΩ

/-- The inverse transport also preserves membership in the oriented source
variety. -/
theorem invFun_mem_variety_iff
    (T : SourceOrientedInvariantTransportEquiv d n)
    (G : SourceOrientedGramData d n) :
    T.invFun G ∈ sourceOrientedGramVariety d n ↔
      G ∈ sourceOrientedGramVariety d n := by
  have h := T.mem_variety_iff (T.invFun G)
  have h' :
      G ∈ sourceOrientedGramVariety d n ↔
        T.invFun G ∈ sourceOrientedGramVariety d n := by
    simpa [toFun, invFun] using h
  exact h'.symm

/-- The inverse transport also preserves the maximal-rank predicate. -/
theorem invFun_maxRank_iff
    (T : SourceOrientedInvariantTransportEquiv d n)
    (G : SourceOrientedGramData d n) :
    SourceOrientedMaxRankAt d n (T.invFun G) ↔
      SourceOrientedMaxRankAt d n G := by
  have h := T.maxRank_iff (T.invFun G)
  have h' :
      SourceOrientedMaxRankAt d n G ↔
        SourceOrientedMaxRankAt d n (T.invFun G) := by
    simpa [toFun, invFun] using h
  exact h'.symm

/-- Identity transport for oriented source invariants. -/
def refl (d n : ℕ) :
    SourceOrientedInvariantTransportEquiv d n where
  toHomeomorph := Homeomorph.refl (SourceOrientedGramData d n)
  mem_variety_iff := by
    intro G
    rfl
  maxRank_iff := by
    intro G
    rfl

end SourceOrientedInvariantTransportEquiv

/-- The oriented source variety as a subtype. -/
abbrev SourceOrientedVariety (d n : ℕ) :=
  {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n}

/-- An actual source tuple, packaged as a point of the oriented source
variety via its oriented Minkowski invariant. -/
noncomputable def sourceTupleOrientedVarietyPoint
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    SourceOrientedVariety d n :=
  ⟨sourceOrientedMinkowskiInvariant d n z, ⟨z, rfl⟩⟩

@[simp]
theorem sourceTupleOrientedVarietyPoint_val
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    (sourceTupleOrientedVarietyPoint d n z).1 =
      sourceOrientedMinkowskiInvariant d n z :=
  rfl

/-- Underlying ambient set of a subtype set in the oriented source variety. -/
def sourceOrientedVarietyUnderlyingSet
    (d n : ℕ) (S : Set (SourceOrientedVariety d n)) :
    Set (SourceOrientedGramData d n) :=
  Subtype.val '' S

/-- The underlying ambient set of a parameterized subtype image is the image
of the underlying ambient-valued map. -/
theorem sourceOrientedVarietyUnderlyingSet_image
    {d n : ℕ} {α : Type*}
    (f : α → SourceOrientedVariety d n) (s : Set α) :
    sourceOrientedVarietyUnderlyingSet d n (f '' s) =
      (fun a => (f a).1) '' s := by
  ext G
  constructor
  · rintro ⟨H, hH, rfl⟩
    rcases hH with ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, rfl⟩

/-- Underlying sets of subtype sets are contained in the oriented source
variety. -/
theorem sourceOrientedVarietyUnderlyingSet_subset_variety
    {d n : ℕ} (S : Set (SourceOrientedVariety d n)) :
    sourceOrientedVarietyUnderlyingSet d n S ⊆
      sourceOrientedGramVariety d n := by
  rintro G ⟨H, _hH, rfl⟩
  exact H.2

/-- An open subtype set gives a relatively open ambient set in the oriented
source variety. -/
theorem sourceOrientedVarietyUnderlyingSet_relOpen_of_isOpen
    {d n : ℕ}
    {S : Set (SourceOrientedVariety d n)}
    (hS : IsOpen S) :
    IsRelOpenInSourceOrientedGramVariety d n
      (sourceOrientedVarietyUnderlyingSet d n S) := by
  rcases isOpen_induced_iff.mp hS with ⟨U0, hU0_open, hpre⟩
  refine ⟨U0, hU0_open, ?_⟩
  ext G
  constructor
  · rintro ⟨H, hHS, rfl⟩
    constructor
    · show H ∈ Subtype.val ⁻¹' U0
      rw [hpre]
      exact hHS
    · exact H.2
  · rintro ⟨hGU0, hGvar⟩
    refine ⟨⟨G, hGvar⟩, ?_, rfl⟩
    show ⟨G, hGvar⟩ ∈ S
    rw [← hpre]
    exact hGU0

/-- A homeomorphic transport internal to the oriented source variety, preserving
the maximal-rank predicate.  This is the correct interface for transports
whose determinant-coordinate formula is only meant on actual alternating
oriented invariant data. -/
structure SourceOrientedVarietyTransportEquiv (d n : ℕ) where
  toHomeomorph : SourceOrientedVariety d n ≃ₜ SourceOrientedVariety d n
  maxRank_iff :
    ∀ G,
      SourceOrientedMaxRankAt d n (toHomeomorph G).1 ↔
        SourceOrientedMaxRankAt d n G.1

namespace SourceOrientedVarietyTransportEquiv

variable {d n : ℕ}

/-- Forward variety transport. -/
def toFun (T : SourceOrientedVarietyTransportEquiv d n) :
    SourceOrientedVariety d n → SourceOrientedVariety d n :=
  T.toHomeomorph

/-- Inverse variety transport. -/
def invFun (T : SourceOrientedVarietyTransportEquiv d n) :
    SourceOrientedVariety d n → SourceOrientedVariety d n :=
  T.toHomeomorph.symm

/-- The inverse transport is a left inverse to the forward transport. -/
theorem left_inv (T : SourceOrientedVarietyTransportEquiv d n) :
    Function.LeftInverse T.invFun T.toFun := by
  intro G
  exact T.toHomeomorph.left_inv G

/-- The inverse transport is a right inverse to the forward transport. -/
theorem right_inv (T : SourceOrientedVarietyTransportEquiv d n) :
    Function.RightInverse T.invFun T.toFun := by
  intro G
  exact T.toHomeomorph.right_inv G

/-- Forward variety transport is continuous. -/
theorem continuous_toFun (T : SourceOrientedVarietyTransportEquiv d n) :
    Continuous T.toFun :=
  T.toHomeomorph.continuous

/-- Inverse variety transport is continuous. -/
theorem continuous_invFun (T : SourceOrientedVarietyTransportEquiv d n) :
    Continuous T.invFun :=
  T.toHomeomorph.symm.continuous

/-- The inverse variety transport preserves the maximal-rank predicate. -/
theorem invFun_maxRank_iff
    (T : SourceOrientedVarietyTransportEquiv d n)
    (G : SourceOrientedVariety d n) :
    SourceOrientedMaxRankAt d n (T.invFun G).1 ↔
      SourceOrientedMaxRankAt d n G.1 := by
  have h := T.maxRank_iff (T.invFun G)
  have h' :
      SourceOrientedMaxRankAt d n G.1 ↔
        SourceOrientedMaxRankAt d n (T.invFun G).1 := by
    simpa [toFun, invFun] using h
  exact h'.symm

/-- Identity transport internal to the oriented source variety. -/
def refl (d n : ℕ) :
    SourceOrientedVarietyTransportEquiv d n where
  toHomeomorph := Homeomorph.refl (SourceOrientedVariety d n)
  maxRank_iff := by
    intro G
    rfl

/-- Images under the inverse variety transport of open subtype sets are open
in the oriented source variety. -/
theorem isOpen_invFun_image
    (T : SourceOrientedVarietyTransportEquiv d n)
    {Ω : Set (SourceOrientedVariety d n)}
    (hΩ : IsOpen Ω) :
    IsOpen (T.invFun '' Ω) := by
  simpa [invFun] using T.toHomeomorph.symm.isOpenMap Ω hΩ

end SourceOrientedVarietyTransportEquiv

/-- Membership in a transported open set intersected with the oriented variety
can be tested after applying the forward transport. -/
theorem sourceOrientedInvariantTransport_mem_inter_iff
    {d n : ℕ}
    (T : SourceOrientedInvariantTransportEquiv d n)
    {Ω : Set (SourceOrientedGramData d n)}
    {G : SourceOrientedGramData d n} :
    T.toFun G ∈ Ω ∩ sourceOrientedGramVariety d n ↔
      G ∈ T.invFun '' Ω ∩ sourceOrientedGramVariety d n := by
  constructor
  · rintro ⟨hΩ, hvar⟩
    refine ⟨?_, (T.mem_variety_iff G).1 hvar⟩
    exact ⟨T.toFun G, hΩ, T.left_inv G⟩
  · rintro ⟨hΩ, hvar⟩
    rcases hΩ with ⟨H, hHΩ, hHG⟩
    refine ⟨?_, (T.mem_variety_iff G).2 hvar⟩
    have hto : T.toFun G = H := by
      calc
        T.toFun G = T.toFun (T.invFun H) := by rw [hHG]
        _ = H := T.right_inv H
    simpa [hto] using hHΩ

/-- The inverse transport of an open set, intersected with the oriented
variety, is relatively open in the oriented source variety. -/
theorem sourceOrientedInvariantTransport_invFun_image_inter_variety_relOpen
    {d n : ℕ}
    (T : SourceOrientedInvariantTransportEquiv d n)
    {Ω : Set (SourceOrientedGramData d n)}
    (hΩ : IsOpen Ω) :
    IsRelOpenInSourceOrientedGramVariety d n
      ((T.invFun '' Ω) ∩ sourceOrientedGramVariety d n) :=
  ⟨T.invFun '' Ω, T.isOpen_invFun_image hΩ, rfl⟩

/-- A normal-coordinate image-surjectivity statement transports through
`invFun`.  This is the generic set-theoretic step used when a residual Schur
chart first proves `Ω ∩ variety ⊆ f '' parameterBox` in normal coordinates
and then moves the chart back to the original coordinates. -/
theorem sourceOrientedInvariantTransport_invFun_image_inter_variety_subset_image
    {d n : ℕ}
    (T : SourceOrientedInvariantTransportEquiv d n)
    {α : Type*}
    {Ω : Set (SourceOrientedGramData d n)}
    {s : Set α}
    {f : α → SourceOrientedGramData d n}
    (hsurj :
      Ω ∩ sourceOrientedGramVariety d n ⊆ f '' s) :
    (T.invFun '' Ω) ∩ sourceOrientedGramVariety d n ⊆
      (fun a => T.invFun (f a)) '' s := by
  intro G hG
  have hto :
      T.toFun G ∈ Ω ∩ sourceOrientedGramVariety d n :=
    (sourceOrientedInvariantTransport_mem_inter_iff
      (d := d) (n := n) T).2 hG
  rcases hsurj hto with ⟨a, ha, hfa⟩
  refine ⟨a, ha, ?_⟩
  calc
    T.invFun (f a) = T.invFun (T.toFun G) := by rw [hfa]
    _ = G := T.left_inv G

/-- If a normal-coordinate parameter map has image exactly the normal open
variety slice, then the inverse-transported parameter map has image exactly
the inverse-transported open variety slice. -/
theorem sourceOrientedInvariantTransport_invFun_image_eq_inter_variety
    {d n : ℕ}
    (T : SourceOrientedInvariantTransportEquiv d n)
    {α : Type*}
    {Ω : Set (SourceOrientedGramData d n)}
    {s : Set α}
    {f : α → SourceOrientedGramData d n}
    (hsurj :
      Ω ∩ sourceOrientedGramVariety d n ⊆ f '' s)
    (hmem :
      ∀ a ∈ s, f a ∈ Ω ∩ sourceOrientedGramVariety d n) :
    (fun a => T.invFun (f a)) '' s =
      (T.invFun '' Ω) ∩ sourceOrientedGramVariety d n := by
  ext G
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hfa := hmem a ha
    exact
      ⟨⟨f a, hfa.1, rfl⟩,
        (T.invFun_mem_variety_iff (f a)).2 hfa.2⟩
  · intro hG
    exact
      sourceOrientedInvariantTransport_invFun_image_inter_variety_subset_image
        (d := d) (n := n) T hsurj hG

/-- If a normal max-rank parameter image is dense at a point, then the
inverse-transported parameter image is dense at the inverse-transported point.
The max-rank predicate in the parameter subset is transported by
`invFun_maxRank_iff`. -/
theorem sourceOrientedInvariantTransport_closure_maxRankDense
    {d n : ℕ}
    (T : SourceOrientedInvariantTransportEquiv d n)
    {α : Type*}
    {s : Set α}
    {f : α → SourceOrientedGramData d n}
    {a : α}
    (h :
      f a ∈
        closure
          (f ''
            {a' : α |
              a' ∈ s ∧ SourceOrientedMaxRankAt d n (f a')})) :
    T.invFun (f a) ∈
      closure
        ((fun a' => T.invFun (f a')) ''
          {a' : α |
            a' ∈ s ∧
              SourceOrientedMaxRankAt d n (T.invFun (f a'))}) := by
  let A : Set α :=
    {a' | a' ∈ s ∧ SourceOrientedMaxRankAt d n (f a')}
  let B : Set α :=
    {a' | a' ∈ s ∧ SourceOrientedMaxRankAt d n (T.invFun (f a'))}
  have hcl :
      T.invFun (f a) ∈ closure (T.invFun '' (f '' A)) := by
    exact
      image_closure_subset_closure_image T.continuous_invFun
        ⟨f a, h, rfl⟩
  have hsubset :
      T.invFun '' (f '' A) ⊆
        (fun a' => T.invFun (f a')) '' B := by
    rintro y ⟨x, hx, rfl⟩
    rcases hx with ⟨a', ha', rfl⟩
    rcases ha' with ⟨ha's, hmax⟩
    refine ⟨a', ⟨ha's, ?_⟩, rfl⟩
    exact (T.invFun_maxRank_iff (f a')).2 hmax
  exact closure_mono hsubset hcl

/-- A subtype normal-coordinate image-surjectivity statement transports
through `SourceOrientedVarietyTransportEquiv.invFun`. -/
theorem sourceOrientedVarietyTransport_invFun_image_subset_image
    {d n : ℕ}
    (T : SourceOrientedVarietyTransportEquiv d n)
    {α : Type*}
    {Ω : Set (SourceOrientedVariety d n)}
    {s : Set α}
    {f : α → SourceOrientedVariety d n}
    (hsurj : Ω ⊆ f '' s) :
    T.invFun '' Ω ⊆ (fun a => T.invFun (f a)) '' s := by
  rintro G ⟨H, hHΩ, rfl⟩
  rcases hsurj hHΩ with ⟨a, ha, hfa⟩
  refine ⟨a, ha, ?_⟩
  exact congrArg T.invFun hfa

/-- If a subtype normal-coordinate parameter map has image exactly a normal
open set, then its inverse-transported image is exactly the transported open
set. -/
theorem sourceOrientedVarietyTransport_invFun_image_eq
    {d n : ℕ}
    (T : SourceOrientedVarietyTransportEquiv d n)
    {α : Type*}
    {Ω : Set (SourceOrientedVariety d n)}
    {s : Set α}
    {f : α → SourceOrientedVariety d n}
    (hsurj : Ω ⊆ f '' s)
    (hmem : ∀ a ∈ s, f a ∈ Ω) :
    (fun a => T.invFun (f a)) '' s = T.invFun '' Ω := by
  ext G
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨f a, hmem a ha, rfl⟩
  · intro hG
    exact
      sourceOrientedVarietyTransport_invFun_image_subset_image
        (d := d) (n := n) T hsurj hG

/-- The underlying ambient image of an inverse-transported open subtype set is
relatively open in the oriented source variety. -/
theorem sourceOrientedVarietyTransport_invFun_image_underlying_relOpen
    {d n : ℕ}
    (T : SourceOrientedVarietyTransportEquiv d n)
    {Ω : Set (SourceOrientedVariety d n)}
    (hΩ : IsOpen Ω) :
    IsRelOpenInSourceOrientedGramVariety d n
      (sourceOrientedVarietyUnderlyingSet d n (T.invFun '' Ω)) :=
  sourceOrientedVarietyUnderlyingSet_relOpen_of_isOpen
    (d := d) (n := n) (T.isOpen_invFun_image hΩ)

/-- If a normal max-rank parameter image is dense at a subtype point, then the
inverse-transported parameter image is dense at the inverse-transported point.
The max-rank predicate in the parameter subset is transported by
`SourceOrientedVarietyTransportEquiv.invFun_maxRank_iff`. -/
theorem sourceOrientedVarietyTransport_closure_maxRankDense
    {d n : ℕ}
    (T : SourceOrientedVarietyTransportEquiv d n)
    {α : Type*}
    {s : Set α}
    {f : α → SourceOrientedVariety d n}
    {a : α}
    (h :
      f a ∈
        closure
          (f ''
            {a' : α |
              a' ∈ s ∧ SourceOrientedMaxRankAt d n (f a').1})) :
    T.invFun (f a) ∈
      closure
        ((fun a' => T.invFun (f a')) ''
          {a' : α |
            a' ∈ s ∧
              SourceOrientedMaxRankAt d n (T.invFun (f a')).1}) := by
  let A : Set α :=
    {a' | a' ∈ s ∧ SourceOrientedMaxRankAt d n (f a').1}
  let B : Set α :=
    {a' | a' ∈ s ∧ SourceOrientedMaxRankAt d n (T.invFun (f a')).1}
  have hcl :
      T.invFun (f a) ∈ closure (T.invFun '' (f '' A)) := by
    exact
      image_closure_subset_closure_image T.continuous_invFun
        ⟨f a, h, rfl⟩
  have hsubset :
      T.invFun '' (f '' A) ⊆
        (fun a' => T.invFun (f a')) '' B := by
    rintro y ⟨x, hx, rfl⟩
    rcases hx with ⟨a', ha', rfl⟩
    rcases ha' with ⟨ha's, hmax⟩
    refine ⟨a', ⟨ha's, ?_⟩, rfl⟩
    exact (T.invFun_maxRank_iff (f a')).2 hmax
  exact closure_mono hsubset hcl

end BHW
