import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2Invariants
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2LorentzInvariantRoute
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.OverlapAnchor

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

variable {d : ℕ}

/-- Deferred geometric input (`d ≥ 2`): connectedness of the permutation seed set. -/
theorem blocker_isConnected_permSeedSet_dge2_nontrivial
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d)
    (hn2 : ¬ n ≤ 1) (hσ : σ ≠ 1) :
    IsConnected (permSeedSet (d := d) n σ) := by
  -- Remaining nontrivial branch (`n ≥ 2`, `σ ≠ 1`):
  -- closure route uses connectedness of forward-overlap index sets.
  sorry

/-- Deferred geometric input (`d ≥ 2`): connectedness of the permutation seed set. -/
theorem blocker_isConnected_permSeedSet_dge2
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    IsConnected (permSeedSet (d := d) n σ) := by
  by_cases hn : n ≤ 1
  · have hsub : Subsingleton (Fin n) := by
      refine ⟨?_⟩
      intro a b
      apply Fin.ext
      have ha0 : a.val = 0 := by omega
      have hb0 : b.val = 0 := by omega
      omega
    letI : Subsingleton (Fin n) := hsub
    have hσ : σ = 1 := Subsingleton.elim σ 1
    subst hσ
    have hset : permSeedSet (d := d) n (1 : Equiv.Perm (Fin n)) = ForwardTube d n := by
      ext z
      constructor
      · intro hz
        simpa [permSeedSet, PermutedForwardTube, permAct] using hz.2
      · intro hz
        exact ⟨forwardTube_subset_extendedTube hz,
          by simpa [PermutedForwardTube, permAct] using hz⟩
    simpa [hset] using
      (show IsConnected (ForwardTube d n) from
        ⟨forwardTube_nonempty (d := d) (n := n), forwardTube_convex.isPreconnected⟩)
  · -- Remaining nontrivial branch (`n ≥ 2`): geometric connectedness input.
    by_cases hσ : σ = 1
    · subst hσ
      have hset : permSeedSet (d := d) n (1 : Equiv.Perm (Fin n)) = ForwardTube d n := by
        ext z
        constructor
        · intro hz
          simpa [permSeedSet, PermutedForwardTube, permAct] using hz.2
        · intro hz
          exact ⟨forwardTube_subset_extendedTube hz,
            by simpa [PermutedForwardTube, permAct] using hz⟩
      simpa [hset] using
        (show IsConnected (ForwardTube d n) from
          ⟨forwardTube_nonempty (d := d) (n := n), forwardTube_convex.isPreconnected⟩)
    · -- Remaining nontrivial branch (`n ≥ 2`, `σ ≠ 1`):
      exact blocker_isConnected_permSeedSet_dge2_nontrivial
        (d := d) n σ hd2 hn hσ

/-- Deferred geometric input (`d = 1`): connectedness of the permutation seed set. -/
theorem blocker_isConnected_permSeedSet_d1_nontrivial
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hn2 : ¬ n ≤ 1) (hσ : σ ≠ 1) :
    IsConnected (permSeedSet (d := 1) n σ) := by
  -- Remaining nontrivial branch (`n ≥ 2`, `σ ≠ 1`).
  sorry

/-- Deferred geometric input (`d = 1`): connectedness of the permutation seed set. -/
theorem blocker_isConnected_permSeedSet_d1
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsConnected (permSeedSet (d := 1) n σ) := by
  by_cases hn : n ≤ 1
  · have hsub : Subsingleton (Fin n) := by
      refine ⟨?_⟩
      intro a b
      apply Fin.ext
      have ha0 : a.val = 0 := by omega
      have hb0 : b.val = 0 := by omega
      omega
    letI : Subsingleton (Fin n) := hsub
    have hσ : σ = 1 := Subsingleton.elim σ 1
    subst hσ
    have hset : permSeedSet (d := 1) n (1 : Equiv.Perm (Fin n)) = ForwardTube 1 n := by
      ext z
      constructor
      · intro hz
        simpa [permSeedSet, PermutedForwardTube, permAct] using hz.2
      · intro hz
        exact ⟨forwardTube_subset_extendedTube hz,
          by simpa [PermutedForwardTube, permAct] using hz⟩
    simpa [hset] using
      (show IsConnected (ForwardTube 1 n) from
        ⟨forwardTube_nonempty (d := 1) (n := n), forwardTube_convex.isPreconnected⟩)
  · by_cases hσ : σ = 1
    · subst hσ
      have hset : permSeedSet (d := 1) n (1 : Equiv.Perm (Fin n)) = ForwardTube 1 n := by
        ext z
        constructor
        · intro hz
          simpa [permSeedSet, PermutedForwardTube, permAct] using hz.2
        · intro hz
          exact ⟨forwardTube_subset_extendedTube hz,
            by simpa [PermutedForwardTube, permAct] using hz⟩
      simpa [hset] using
        (show IsConnected (ForwardTube 1 n) from
          ⟨forwardTube_nonempty (d := 1) (n := n), forwardTube_convex.isPreconnected⟩)
    · -- Remaining nontrivial branch (`n ≥ 2`, `σ ≠ 1`) is deferred.
      exact blocker_isConnected_permSeedSet_d1_nontrivial n σ hn hσ

/-- `d=1,n=2`: connectedness of the adjacent forward-overlap slice from the
seed-set connectedness blocker bridge. -/
theorem d1N2_isConnected_adjSwapForwardOverlapSet_of_seedConnectedBlocker :
    IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)) := by
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  have hseed : IsConnected (permSeedSet (d := 1) 2 τ) :=
    blocker_isConnected_permSeedSet_d1_nontrivial 2 τ (by decide) (by decide)
  have hfwd : IsConnected (permForwardOverlapSet (d := 1) 2 τ) :=
    (isConnected_permSeedSet_iff_permForwardOverlapSet (d := 1) 2 τ).1 hseed
  have hset :
      adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) =
        permForwardOverlapSet (d := 1) 2 τ := by
    ext w
    constructor <;> intro hw <;>
      simpa [adjSwapForwardOverlapSet, permForwardOverlapSet, τ, permAct] using hw
  simpa [hset] using hfwd

/-- Nontrivial permutations of `Fin 2` are exactly the adjacent swap. -/
theorem fin2_perm_ne_one_eq_swap01 (τ : Equiv.Perm (Fin 2)) (hτ : τ ≠ 1) :
    τ = Equiv.swap (0 : Fin 2) 1 := by
  fin_cases τ <;> simp at hτ ⊢

/-- On `FT_{1,2}`, equal signed invariant quadruples force equality of field
values under the source holomorphy + real-Lorentz invariance package. -/
theorem d1N2Field_eq_of_sameInvariantQuad_onFT
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    {z w : Fin 2 → Fin (1 + 1) → ℂ}
    (hz : z ∈ ForwardTube 1 2)
    (hw : w ∈ ForwardTube 1 2)
    (hquad : d1InvariantQuad z = d1InvariantQuad w) :
    F z = F w := by
  rcases d1_exists_lorentz_of_sameInvariantQuad_on_FT hz hw hquad with ⟨Λ, hw_eq⟩
  have hΛzFT : complexLorentzAction Λ z ∈ ForwardTube 1 2 := by
    rw [← hw_eq]
    exact hw
  have hinv :
      F (complexLorentzAction Λ z) = F z :=
    complex_lorentz_invariance 2 F hF_holo hF_lorentz Λ z hz hΛzFT
  calc
    F z = F (complexLorentzAction Λ z) := hinv.symm
    _ = F w := by rw [hw_eq]

/-- `d=1,n=2` invariant-function step A (deferred):
factorization of `F` on `FT` through Lorentz invariants `(Q₀,Q₁,P,S)`. -/
theorem blocker_d1N2InvariantFactorization_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ,
      ∀ z, z ∈ ForwardTube 1 2 →
        F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := by
  let _ := hF_bv
  let _ := hF_local
  let f : ℂ → ℂ → ℂ → ℂ → ℂ :=
    fun a b c s =>
      if h : ∃ z : Fin 2 → Fin (1 + 1) → ℂ,
          z ∈ ForwardTube 1 2 ∧ d1InvariantQuad z = (a, b, c, s)
      then F h.choose
      else 0
  refine ⟨f, ?_⟩
  intro z hz
  have hex :
      ∃ w : Fin 2 → Fin (1 + 1) → ℂ,
        w ∈ ForwardTube 1 2 ∧
          d1InvariantQuad w = (d1Q0 z, d1Q1 z, d1P01 z, d1S01 z) :=
    ⟨z, hz, by rfl⟩
  have hf_eq :
      f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) = F hex.choose := by
    simp [f, hex]
  have hchooseFT : hex.choose ∈ ForwardTube 1 2 := hex.choose_spec.1
  have hchooseQuad :
      d1InvariantQuad hex.choose = (d1Q0 z, d1Q1 z, d1P01 z, d1S01 z) :=
    hex.choose_spec.2
  have hquadEq : d1InvariantQuad z = d1InvariantQuad hex.choose := by
    simpa [d1InvariantQuad] using hchooseQuad.symm
  have hFz_eq_hchoose : F z = F hex.choose :=
    d1N2Field_eq_of_sameInvariantQuad_onFT
      F hF_holo hF_lorentz hz hchooseFT hquadEq
  calc
    F z = F hex.choose := hFz_eq_hchoose
    _ = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hf_eq.symm

/-- Pure invariant-function swap law on the `d=1,n=2` invariant quadric. -/
def d1N2InvariantKernelSwapOnQuadric (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      f q0 q1 p s = f q1 q0 p (-s)

/-- Equivalent invariant-only formulation:
the swap-difference kernel vanishes on the quadric
`s^2 = 4*(p^2 - q0*q1)`. -/
def d1N2InvariantKernelDiffZeroOnQuadric (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      f q0 q1 p s - f q1 q0 p (-s) = 0

/-- From vanishing swap-difference on the quadric, recover the swap law. -/
theorem d1N2InvariantKernelSwapOnQuadric_of_diffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hzero : d1N2InvariantKernelDiffZeroOnQuadric f) :
    d1N2InvariantKernelSwapOnQuadric f := by
  intro q0 q1 p s hquad
  exact sub_eq_zero.mp (hzero q0 q1 p s hquad)

/-- Invariant quadruple `(q0,q1,p,s)` is realized by an `FT_{1,2}` point. -/
def d1N2InvariantRealizable (q0 q1 p s : ℂ) : Prop :=
  ∃ z : Fin 2 → Fin (1 + 1) → ℂ,
    z ∈ ForwardTube 1 2 ∧ d1InvariantQuad z = (q0, q1, p, s)

/-- Canonical-section realizability: points in the explicit section domain are
realizable by `FT_{1,2}` configurations in invariant coordinates. -/
lemma d1N2InvariantRealizable_of_sectionDomain
    {q0 p s : ℂ}
    (hdom : d1N2InvariantSectionDomain q0 p s) :
    d1N2InvariantRealizable
      (-q0) (-(d1N2InvariantSectionSwapQ0 q0 p s)) (-p) s := by
  let z : Fin 2 → Fin (1 + 1) → ℂ := d1N2InvariantSectionPoint q0 p s
  refine ⟨z, ?_, ?_⟩
  · exact d1N2InvariantSectionPoint_mem_forwardTube_of_domain hdom
  · rcases hdom with ⟨hq0, _, _, _⟩
    simpa [z] using d1InvariantQuad_invariantSectionPoint q0 p s hq0

/-- Swap-side canonical-section realizability on the transformed section
parameters. -/
lemma d1N2InvariantRealizable_swap_of_sectionDomain
    {q0 p s : ℂ}
    (hq0 : q0 ≠ 0)
    (hΔ : d1N2InvariantSectionSwapQ0 q0 p s ≠ 0)
    (hdomSwap :
      d1N2InvariantSectionDomain (d1N2InvariantSectionSwapQ0 q0 p s) p (-s)) :
    d1N2InvariantRealizable
      (-(d1N2InvariantSectionSwapQ0 q0 p s)) (-q0) (-p) (-s) := by
  let y : Fin 2 → Fin (1 + 1) → ℂ :=
    d1N2InvariantSectionPoint (d1N2InvariantSectionSwapQ0 q0 p s) p (-s)
  refine ⟨y, ?_, ?_⟩
  · exact d1N2InvariantSectionPoint_mem_forwardTube_of_domain hdomSwap
  · simpa [y] using d1InvariantQuad_invariantSectionPoint_swapParams q0 p s hq0 hΔ

/-- Swap-difference vanishes on quadric points that are realized by `FT_{1,2}`
configurations. This is the maximal statement forced by `hf_onFT` data alone. -/
def d1N2InvariantKernelDiffZeroOnRealizableQuadric
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
    d1N2InvariantRealizable q0 q1 p s →
      f q0 q1 p s - f q1 q0 p (-s) = 0

/-- Invariant quadruple `(q0,q1,p,s)` is represented by a forward configuration
whose swapped image is forwardizable by some complex Lorentz witness. -/
def d1N2InvariantForwardizableSwap (q0 q1 p s : ℂ) : Prop :=
  ∃ z : Fin 2 → Fin (1 + 1) → ℂ, ∃ Γ : ComplexLorentzGroup 1,
    z ∈ ForwardTube 1 2 ∧
    complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 ∧
    d1InvariantQuad z = (q0, q1, p, s)

/-- Swap-difference vanishes on quadric points that are forwardizable in the
`d=1,n=2` swap sense. -/
def d1N2InvariantKernelDiffZeroOnForwardizableQuadric
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
    d1N2InvariantForwardizableSwap q0 q1 p s →
      f q0 q1 p s - f q1 q0 p (-s) = 0

/-- A forwardizable invariant tuple is realizable in `FT_{1,2}` both before and
after swap-sign action on invariants. -/
lemma d1N2InvariantRealizable_pair_of_forwardizable
    {q0 q1 p s : ℂ}
    (hfw : d1N2InvariantForwardizableSwap q0 q1 p s) :
    d1N2InvariantRealizable q0 q1 p s ∧
      d1N2InvariantRealizable q1 q0 p (-s) := by
  rcases hfw with ⟨z, Γ, hz, hΓswap, hquadZ⟩
  refine ⟨⟨z, hz, hquadZ⟩, ?_⟩
  let y : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
  have hyFT : y ∈ ForwardTube 1 2 := by
    simpa [y] using hΓswap
  have hquadY : d1InvariantQuad y = (q1, q0, p, -s) := by
    calc
      d1InvariantQuad y
          = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
              simp [y, d1InvariantQuad_lorentzAction]
      _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
      _ = (q1, q0, p, -s) := by
            simpa [d1InvariantQuad] using congrArg
              (fun t => (t.2.1, t.1, t.2.2.1, -t.2.2.2)) hquadZ
  exact ⟨y, hyFT, hquadY⟩

/-- If both a `d=1,n=2` invariant tuple and its swap-sign image are realizable
by `FT_{1,2}` points, then the tuple is forwardizable. -/
lemma d1N2InvariantForwardizable_of_realizable_pair
    {q0 q1 p s : ℂ}
    (hreal : d1N2InvariantRealizable q0 q1 p s)
    (hswapReal : d1N2InvariantRealizable q1 q0 p (-s)) :
    d1N2InvariantForwardizableSwap q0 q1 p s := by
  rcases hreal with ⟨z, hz, hquadZ⟩
  rcases hswapReal with ⟨y, hy, hquadY⟩
  let zswap : Fin 2 → Fin (1 + 1) → ℂ :=
    permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z
  have hquadZswap : d1InvariantQuad zswap = (q1, q0, p, -s) := by
    calc
      d1InvariantQuad zswap
          = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
              rfl
      _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
      _ = (q1, q0, p, -s) := by
            simpa [d1InvariantQuad] using congrArg
              (fun t => (t.2.1, t.1, t.2.2.1, -t.2.2.2)) hquadZ
  have hU0_zswap_ne : d1U0 zswap ≠ 0 := by
    simpa [zswap, d1U0, permAct] using d1U1_ne_zero_of_forward z hz
  have hU0_y_ne : d1U0 y ≠ 0 := d1U0_ne_zero_of_forward y hy
  have hV0_y_ne : d1V0 y ≠ 0 := d1V0_ne_zero_of_forward y hy
  have hquadEq : d1InvariantQuad zswap = d1InvariantQuad y := by
    exact hquadZswap.trans hquadY.symm
  rcases d1_exists_lorentz_of_sameInvariantQuad_of_nonzeroU0V0
      hU0_zswap_ne hU0_y_ne hV0_y_ne hquadEq with ⟨Γ, hΓ⟩
  refine ⟨z, Γ, hz, ?_, hquadZ⟩
  have hyFT' : complexLorentzAction Γ zswap ∈ ForwardTube 1 2 := by
    simpa [hΓ] using hy
  simpa [zswap] using hyFT'

/-- Invariant forwardizability is equivalent to realizability of both the
original and swap-sign invariant tuples. -/
theorem d1N2InvariantForwardizableSwap_iff_realizable_pair
    {q0 q1 p s : ℂ} :
    d1N2InvariantForwardizableSwap q0 q1 p s ↔
      d1N2InvariantRealizable q0 q1 p s ∧
      d1N2InvariantRealizable q1 q0 p (-s) := by
  constructor
  · intro hfw
    exact d1N2InvariantRealizable_pair_of_forwardizable hfw
  · intro hpair
    exact d1N2InvariantForwardizable_of_realizable_pair hpair.1 hpair.2

/-- The doubly-realizable invariant locus in the `d=1,n=2` swap setting is
nonempty. -/
theorem d1N2InvariantRealizable_pair_nonempty :
    ∃ q0 q1 p s : ℂ,
      s ^ 2 = 4 * (p ^ 2 - q0 * q1) ∧
      d1N2InvariantRealizable q0 q1 p s ∧
      d1N2InvariantRealizable q1 q0 p (-s) := by
  rcases adjSwapForwardOverlap_nonempty (d := 1) 2 (0 : Fin 2) (by decide) with
    ⟨w, hwFT, hswapET⟩
  rcases Set.mem_iUnion.mp hswapET with ⟨Γ, u, huFT, hrepr⟩
  have hrepr' :
      permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w = complexLorentzAction Γ u := by
    simpa [permAct] using hrepr
  have hΓswap :
      complexLorentzAction Γ⁻¹
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 := by
    simpa [hrepr', complexLorentzAction_inv] using huFT
  let q0 : ℂ := d1Q0 w
  let q1 : ℂ := d1Q1 w
  let p : ℂ := d1P01 w
  let s : ℂ := d1S01 w
  refine ⟨q0, q1, p, s, ?_, ?_, ?_⟩
  · simpa [q0, q1, p, s] using d1_invariant_quadric_relation w
  · exact ⟨w, hwFT, by simp [q0, q1, p, s, d1InvariantQuad]⟩
  · have hpair :
        d1N2InvariantRealizable q0 q1 p s ∧
          d1N2InvariantRealizable q1 q0 p (-s) :=
      d1N2InvariantRealizable_pair_of_forwardizable
        (q0 := q0) (q1 := q1) (p := p) (s := s)
        ⟨w, Γ⁻¹, hwFT, hΓswap, by simp [q0, q1, p, s, d1InvariantQuad]⟩
    exact hpair.2

/-- Realizable-pair involution equality and forwardizable diff-zero are
equivalent formulations of the same `d=1,n=2` invariant kernel condition. -/
theorem d1N2InvariantKernelPairSwapOnRealizable_iff_forwardizableDiffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s)) ↔
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  constructor
  · intro hpair q0 q1 p s hrel hfw
    rcases d1N2InvariantRealizable_pair_of_forwardizable hfw with ⟨hreal, hswapReal⟩
    exact sub_eq_zero.mpr (hpair q0 q1 p s hrel hreal hswapReal)
  · intro hdiff q0 q1 p s hrel hreal hswapReal
    have hfw : d1N2InvariantForwardizableSwap q0 q1 p s :=
      d1N2InvariantForwardizable_of_realizable_pair hreal hswapReal
    exact sub_eq_zero.mp (hdiff q0 q1 p s hrel hfw)

/-- Full-quadric vanishing implies the forwardizable-quadric specialization. -/
theorem d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_quadric
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquad : d1N2InvariantKernelDiffZeroOnQuadric f) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  intro q0 q1 p s hrel _hfw
  exact hquad q0 q1 p s hrel

/-- `Q₀` cannot vanish on `FT_{1,2}`. -/
lemma d1Q0_ne_zero_of_mem_forwardTube_d1_n2
    (z : Fin 2 → Fin (1 + 1) → ℂ)
    (hz : z ∈ ForwardTube 1 2) :
    d1Q0 z ≠ 0 := by
  rw [d1Q0_eq_neg_U0_mul_V0]
  refine neg_ne_zero.mpr ?_
  exact mul_ne_zero (d1U0_ne_zero_of_forward z hz) (d1V0_ne_zero_of_forward z hz)

/-- Source package for an invariant kernel arising from the `d=1,n=2`
Wightman assumptions and FT factorization data. -/
def d1N2InvariantKernelSource (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∃ F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ,
    DifferentiableOn ℂ F (ForwardTube 1 2) ∧
    (∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) ∧
    (∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ))) ∧
    (∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) ∧
    (∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))

/-- Source-form orbit constancy on `FT_{1,2}`: equal invariant quadruples imply
equal source-field values. -/
theorem d1N2InvariantKernelSource_eq_of_sameInvariantQuad_onFT
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    {z w : Fin 2 → Fin (1 + 1) → ℂ}
    (hz : z ∈ ForwardTube 1 2)
    (hw : w ∈ ForwardTube 1 2)
    (hquad : d1InvariantQuad z = d1InvariantQuad w) :
    (Classical.choose hsource) z = (Classical.choose hsource) w := by
  exact d1N2Field_eq_of_sameInvariantQuad_onFT
    (Classical.choose hsource)
    (Classical.choose_spec hsource).1
    (Classical.choose_spec hsource).2.1
    hz hw hquad

/-- The source package alone does not force full-quadric involution
`g ≡ 0` for an arbitrary representative `f`; off-image values of `f` are
unconstrained by `hf_onFT`. -/
theorem d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero :
    ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ,
      d1N2InvariantKernelSource f ∧
      ¬ d1N2InvariantKernelDiffZeroOnQuadric f := by
  let f : ℂ → ℂ → ℂ → ℂ → ℂ :=
    fun q0 q1 p s =>
      if q0 = 0 ∧ q1 = 0 ∧ p = (1 : ℂ) ∧ s = (2 : ℂ) then (1 : ℂ) else 0
  refine ⟨f, ?_, ?_⟩
  · refine ⟨(fun _ => (0 : ℂ)), ?_, ?_, ?_, ?_, ?_⟩
    · exact (differentiableOn_const (c := (0 : ℂ)) :
        DifferentiableOn ℂ (fun _ : Fin 2 → Fin (1 + 1) → ℂ => (0 : ℂ))
          (ForwardTube 1 2))
    · intro Λ z hz
      simp
    · intro x
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : Fin 2 → Fin (1 + 1) → ℂ => (0 : ℂ))
          (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    · intro i hi x hx
      simp
    · intro z hz
      have hq0_ne : d1Q0 z ≠ 0 := d1Q0_ne_zero_of_mem_forwardTube_d1_n2 z hz
      have hcond_false :
          ¬ (d1Q0 z = 0 ∧ d1Q1 z = 0 ∧ d1P01 z = (1 : ℂ) ∧ d1S01 z = (2 : ℂ)) := by
        intro h
        exact hq0_ne h.1
      simp [f, hcond_false]
  · intro hzero
    have hrel : ((2 : ℂ) ^ 2) = 4 * (((1 : ℂ) ^ 2) - (0 : ℂ) * (0 : ℂ)) := by
      norm_num
    have h := hzero 0 0 1 2 hrel
    have h1 : f 0 0 1 2 = (1 : ℂ) := by
      simp [f]
    have hneq : (-2 : ℂ) ≠ (2 : ℂ) := by
      norm_num
    have hm1 : f 0 0 1 (-2) = (0 : ℂ) := by
      simp [f, hneq]
    have : (1 : ℂ) = 0 := by
      have h' := h
      simp [h1, hm1] at h'
    exact one_ne_zero this

/-- Reduce the `FT` kernel-swap condition to a pure invariant-quadric swap law. -/
theorem blocker_d1N2InvariantKernelSwap_core_of_quadricSwapLaw
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquadSwap : d1N2InvariantKernelSwapOnQuadric f) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  intro z _hz _Γ _hΓswap
  exact hquadSwap (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
    (d1_invariant_quadric_relation z)

/-- Reduce the `FT` kernel-swap condition to vanishing of the invariant swap-
difference on realizable quadric points. -/
theorem blocker_d1N2InvariantKernelSwap_core_of_realizableQuadricDiffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquadDiff : d1N2InvariantKernelDiffZeroOnRealizableQuadric f) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  intro z hz _Γ _hΓswap
  apply sub_eq_zero.mp
  exact hquadDiff (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
    (d1_invariant_quadric_relation z) ⟨z, hz, rfl⟩

/-- Reduce the `FT` kernel-swap condition to vanishing of the invariant swap-
difference on forwardizable quadric points. -/
theorem blocker_d1N2InvariantKernelSwap_core_of_forwardizableQuadricDiffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquadDiff : d1N2InvariantKernelDiffZeroOnForwardizableQuadric f) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  intro z hz Γ hΓswap
  apply sub_eq_zero.mp
  exact hquadDiff (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
    (d1_invariant_quadric_relation z) ⟨z, Γ, hz, hΓswap, rfl⟩

/-- If forward-swap equality holds on `FT_{1,2}`, then any `FT` invariant kernel
representation has vanishing swap-difference on forwardizable invariant points. -/
theorem d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_forwardSwapEq
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  intro q0 q1 p s _hquad hfw
  rcases hfw with ⟨z, Γ, hz, hΓswap, hquadZ⟩
  let y : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
  have hyFT : y ∈ ForwardTube 1 2 := by
    simpa [y] using hΓswap
  have hF_forward : F y = F z := by
    simpa [y] using hforward z hz Γ hΓswap
  have hleft : f q0 q1 p s = F z := by
    have hq :
        f q0 q1 p s = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := by
      simpa [d1InvariantQuad] using
        (congrArg (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadZ).symm
    calc
      f q0 q1 p s = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hq
      _ = F z := by simpa using (hf_onFT z hz).symm
  have hquadY :
      d1InvariantQuad y = (q1, q0, p, -s) := by
    calc
      d1InvariantQuad y
          = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
              simp [y, d1InvariantQuad_lorentzAction]
      _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
      _ = (q1, q0, p, -s) := by
            simpa [d1InvariantQuad] using congrArg
              (fun t => (t.2.1, t.1, t.2.2.1, -t.2.2.2)) hquadZ
  have hright : f q1 q0 p (-s) = F y := by
    have hq :
        f q1 q0 p (-s) = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := by
      simpa [d1InvariantQuad] using
        (congrArg (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadY).symm
    calc
      f q1 q0 p (-s) = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hq
      _ = F y := by simpa using (hf_onFT y hyFT).symm
  calc
    f q0 q1 p s - f q1 q0 p (-s) = F z - F y := by rw [hleft, hright]
    _ = 0 := sub_eq_zero.mpr hF_forward.symm

/-- Witness-form reformulation of forwardizable invariant-kernel diff-zero. -/
theorem d1N2InvariantKernelDiffZeroOnForwardizableQuadric_iff_witnessForm
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f ↔
    (∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) -
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) = 0) := by
  constructor
  · intro hquad z hz Γ hΓswap
    exact hquad (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
      (d1_invariant_quadric_relation z) ⟨z, Γ, hz, hΓswap, rfl⟩
  · intro hwit q0 q1 p s _hquad hfw
    rcases hfw with ⟨z, Γ, hz, hΓswap, hquadZ⟩
    have h := hwit z hz Γ hΓswap
    have hq0 : d1Q0 z = q0 := by
      simpa [d1InvariantQuad] using congrArg Prod.fst hquadZ
    have hq1 : d1Q1 z = q1 := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.1) hquadZ
    have hp : d1P01 z = p := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquadZ
    have hs : d1S01 z = s := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquadZ
    simpa [hq0, hq1, hp, hs] using h

/-- For fixed `hf_onFT`, the forward-swap equality on `FT_{1,2}` and
forwardizable invariant-kernel diff-zero are equivalent. -/
theorem d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) :
    (∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) ↔
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  constructor
  · intro hforward
    exact d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_forwardSwapEq
      F f hf_onFT hforward
  · intro hquadDiff z hz Γ hΓswap
    let y : Fin 2 → Fin (1 + 1) → ℂ :=
      complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
    have hyFT : y ∈ ForwardTube 1 2 := by
      simpa [y] using hΓswap
    have hzero :
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) -
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) = 0 :=
      hquadDiff (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
        (d1_invariant_quadric_relation z) ⟨z, Γ, hz, hΓswap, rfl⟩
    have hker :
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
      sub_eq_zero.mp hzero
    have hFy :
        F y = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
      have hquadY :
          d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
        calc
          d1InvariantQuad y
              = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
                  simp [y, d1InvariantQuad_lorentzAction]
          _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
      calc
        F y = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hf_onFT y hyFT
        _ = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
              simpa [d1InvariantQuad] using congrArg
                (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadY
    have hFz :
        F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hf_onFT z hz
    calc
      F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z))
          = F y := by rfl
      _ = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := hFy
      _ = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hker.symm
      _ = F z := hFz.symm

/-- For fixed `hf_onFT`, forward-swap equality on `FT_{1,2}` is already
sufficient to force the invariant forwardizable involution law. -/
theorem d1N2InvariantKernelSwapOnForwardizable_of_forwardSwapEq
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantForwardizableSwap q0 q1 p s →
      f q0 q1 p s = f q1 q0 p (-s) := by
  have hdiff :
      d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
    (d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric
      F f hf_onFT).1 hforward
  intro q0 q1 p s hquad hfw
  exact sub_eq_zero.mp (hdiff q0 q1 p s hquad hfw)

/-- For fixed `hf_onFT`, forward-swap equality on `FT_{1,2}` implies
realizable-pair involution symmetry in invariant coordinates. -/
theorem d1N2InvariantKernelPairSwapOnRealizable_of_forwardSwapEq
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  intro q0 q1 p s hquad hreal hswapReal
  have hfw : d1N2InvariantForwardizableSwap q0 q1 p s :=
    d1N2InvariantForwardizable_of_realizable_pair hreal hswapReal
  exact d1N2InvariantKernelSwapOnForwardizable_of_forwardSwapEq
    F f hf_onFT hforward q0 q1 p s hquad hfw

/-- For fixed `hf_onFT`, realizable-pair involution symmetry in invariant
coordinates implies forward-swap equality on `FT_{1,2}`. -/
theorem d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hpair :
      ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s)) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  have hdiff :
      d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
    (d1N2InvariantKernelPairSwapOnRealizable_iff_forwardizableDiffZero f).1 hpair
  exact (d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric
    F f hf_onFT).2 hdiff

/-- For fixed `hf_onFT`, forward-swap equality on `FT_{1,2}` is equivalent to
realizable-pair involution symmetry in invariant coordinates. -/
theorem d1N2ForwardSwapEq_onFT_iff_invariantKernelPairSwapOnRealizable
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) :
    (∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) ↔
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s)) := by
  constructor
  · intro hforward
    exact d1N2InvariantKernelPairSwapOnRealizable_of_forwardSwapEq
      F f hf_onFT hforward
  · intro hpair
    exact d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable
      F f hf_onFT hpair

/-- `d=1,n=2` geometric package sufficient for EOW-based forward-swap equality. -/
def d1N2ForwardSwapEOWGeometryPackage : Prop :=
  IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)) ∧
  ∃ x0 : Fin 2 → Fin (1 + 1) → ℝ,
    (∑ μ, minkowskiSignature 1 μ * (x0 1 μ - x0 0 μ) ^ 2 > 0) ∧
    realEmbed x0 ∈ ExtendedTube 1 2 ∧
    realEmbed (fun k => x0 (Equiv.swap (0 : Fin 2) 1 k)) ∈ ExtendedTube 1 2

/-- `d=1,n=2` complex-anchor forward-swap bridge:
if the adjacent forward-overlap slice is connected and one has a nonempty
complex-open anchor subset of the forward-overlap base where
`extendF(swap·w)=F(w)`, then forward-swap equality on `FT_{1,2}` follows. -/
theorem d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hFwd_conn :
      IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)))
    (W : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hW_open : IsOpen W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1))
    (hW_eq : ∀ w ∈ W,
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) = F w) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  have hset :
      adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) =
        permForwardOverlapSet (d := 1) 2 τ := by
    ext w
    constructor <;> intro hw <;>
      simpa [adjSwapForwardOverlapSet, permForwardOverlapSet, τ, permAct] using hw
  have hΩ_conn : IsConnected (permForwardOverlapSet (d := 1) 2 τ) := by
    simpa [hset] using hFwd_conn
  have hbase :
      ∀ w, w ∈ permForwardOverlapSet (d := 1) 2 τ →
        extendF F (permAct (d := 1) τ w) = F w :=
    forward_base_eq_of_open_anchor (d := 1) (n := 2)
      F hF_holo hF_lorentz τ hΩ_conn W hW_open hW_ne
      (by simpa [τ] using hW_sub)
      (by simpa [τ] using hW_eq)
  intro z hz Γ hΓswap
  let y : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Γ (permAct (d := 1) τ z)
  have hswapET : permAct (d := 1) τ z ∈ ExtendedTube 1 2 := by
    have hyET : y ∈ ExtendedTube 1 2 :=
      forwardTube_subset_extendedTube hΓswap
    have hback :
        complexLorentzAction Γ⁻¹ y ∈ ExtendedTube 1 2 :=
      complexLorentzAction_mem_extendedTube (d := 1) (n := 2) (Λ := Γ⁻¹) hyET
    simpa [y, τ, complexLorentzAction_inv] using hback
  have hzΩ : z ∈ permForwardOverlapSet (d := 1) 2 τ := ⟨hz, hswapET⟩
  have hExt_swap : extendF F (permAct (d := 1) τ z) = F z := hbase z hzΩ
  have hExt_swap_as_Fy :
      extendF F (permAct (d := 1) τ z) = F y := by
    calc
      extendF F (permAct (d := 1) τ z)
          = extendF F (complexLorentzAction Γ⁻¹ y) := by
              simp [y, τ, complexLorentzAction_inv]
      _ = extendF F y :=
          extendF_complex_lorentz_invariant (d := 1) 2 F hF_holo hF_lorentz Γ⁻¹ y
            (forwardTube_subset_extendedTube hΓswap)
      _ = F y := extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz y hΓswap
  calc
    F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z))
        = F y := by rfl
    _ = extendF F (permAct (d := 1) τ z) := hExt_swap_as_Fy.symm
    _ = F z := hExt_swap

/-- `d=1,n=2` strengthened forward-swap bridge:
if the adjacent forward-overlap slice is connected and a real spacelike overlap
witness is available, then forward-swap equality on `FT_{1,2}` follows from the
standard EOW/identity infrastructure. -/
theorem d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_realWitness
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (hFwd_conn :
      IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)))
    (x0 : Fin 2 → Fin (1 + 1) → ℝ)
    (hx0_sp : ∑ μ, minkowskiSignature 1 μ *
      (x0 1 μ - x0 0 μ) ^ 2 > 0)
    (hx0_ET : realEmbed x0 ∈ ExtendedTube 1 2)
    (hx0_swapET :
      realEmbed (fun k => x0 (Equiv.swap (0 : Fin 2) 1 k)) ∈ ExtendedTube 1 2) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  have hF_bv_realEmbed :
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ContinuousWithinAt F (ForwardTube 1 2) (realEmbed x) := by
    intro x
    simpa [realEmbed] using hF_bv x
  intro z hz Γ hΓswap
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  let y : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Γ (permAct (d := 1) τ z)
  have hswapET : permAct (d := 1) τ z ∈ ExtendedTube 1 2 := by
    have hyET : y ∈ ExtendedTube 1 2 :=
      forwardTube_subset_extendedTube hΓswap
    have hback :
        complexLorentzAction Γ⁻¹ y ∈ ExtendedTube 1 2 :=
      complexLorentzAction_mem_extendedTube (d := 1) (n := 2) (Λ := Γ⁻¹) hyET
    simpa [y, τ, complexLorentzAction_inv] using hback
  have hExt_swap :
      extendF F (permAct (d := 1) τ z) = extendF F z := by
    exact extendF_adjSwap_eq_of_connected_forwardOverlap
      (d := 1) 2 F hF_holo hF_lorentz hF_bv_realEmbed hF_local
      (0 : Fin 2) (by decide) hFwd_conn x0
      (by simpa using hx0_sp) hx0_ET hx0_swapET
      z (forwardTube_subset_extendedTube hz)
      (by simpa [τ] using hswapET)
  have hExt_swap_as_Fy :
      extendF F (permAct (d := 1) τ z) = F y := by
    calc
      extendF F (permAct (d := 1) τ z)
          = extendF F (complexLorentzAction Γ⁻¹ y) := by
              simp [y, τ, complexLorentzAction_inv]
      _ = extendF F y :=
          extendF_complex_lorentz_invariant (d := 1) 2 F hF_holo hF_lorentz Γ⁻¹ y
            (forwardTube_subset_extendedTube hΓswap)
      _ = F y := extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz y hΓswap
  have hExt_z_as_Fz : extendF F z = F z :=
    extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz z hz
  calc
    F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z))
        = F y := by rfl
    _ = extendF F (permAct (d := 1) τ z) := hExt_swap_as_Fy.symm
    _ = extendF F z := hExt_swap
    _ = F z := hExt_z_as_Fz

/-- `d=1,n=2` forward-swap equality from the bundled EOW geometry package. -/
theorem d1N2ForwardSwapEq_onFT_of_EOWGeometryPackage
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (hgeom : d1N2ForwardSwapEOWGeometryPackage) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  rcases hgeom with ⟨hFwd_conn, x0, hx0_sp, hx0_ET, hx0_swapET⟩
  exact d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_realWitness
    F hF_holo hF_lorentz hF_bv hF_local hFwd_conn x0 hx0_sp hx0_ET hx0_swapET

/-- Under the bundled EOW geometry package, one gets a nonempty complex-open
anchor subset of the forward-overlap base where `extendF(swap·w)=F(w)`. -/
theorem d1N2ForwardBaseOpenAnchor_of_EOWGeometryPackage
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (hgeom : d1N2ForwardSwapEOWGeometryPackage) :
    ∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) = F w) := by
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  let W : Set (Fin 2 → Fin (1 + 1) → ℂ) := permForwardOverlapSet (d := 1) 2 τ
  have hW_open : IsOpen W := by
    have hset :
        adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) = W := by
      ext w
      constructor <;> intro hw <;>
        simpa [adjSwapForwardOverlapSet, permForwardOverlapSet, τ, permAct] using hw
    simpa [hset] using
      isOpen_adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)
  have hW_ne : W.Nonempty := by
    have hneAdj :
        (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)).Nonempty :=
      adjSwapForwardOverlap_nonempty (d := 1) 2 (0 : Fin 2) (by decide)
    have hset :
        adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) = W := by
      ext w
      constructor <;> intro hw <;>
        simpa [adjSwapForwardOverlapSet, permForwardOverlapSet, τ, permAct] using hw
    simpa [hset] using hneAdj
  refine ⟨W, hW_open, hW_ne, ?_, ?_⟩
  · intro w hwW
    simpa [W, τ] using hwW
  · intro w hwW
    rcases hwW with ⟨hwFT, hswapET⟩
    rcases Set.mem_iUnion.mp hswapET with ⟨Λ, u, huFT, hswap_eq⟩
    let y : Fin 2 → Fin (1 + 1) → ℂ :=
      complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)
    have hyFT : y ∈ ForwardTube 1 2 := by
      dsimp [y]
      simpa [hswap_eq, complexLorentzAction_inv] using huFT
    have hforward :
        F y = F w := by
      have hyEq :
          F (complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)) = F w :=
        d1N2ForwardSwapEq_onFT_of_EOWGeometryPackage
          F hF_holo hF_lorentz hF_bv hF_local hgeom
          w hwFT Λ⁻¹ hyFT
      simpa [y] using hyEq
    have hExt :
        extendF F (permAct (d := 1) τ w) = F y := by
      calc
        extendF F (permAct (d := 1) τ w)
            = extendF F (complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)) := by
                symm
                exact extendF_complex_lorentz_invariant
                  (d := 1) 2 F hF_holo hF_lorentz Λ⁻¹
                  (permAct (d := 1) τ w) hswapET
        _ = F y := by
              simpa [y] using
                extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz y hyFT
    calc
      extendF F (permAct (d := 1) τ w) = F y := hExt
      _ = F w := hforward

/-- Under the bundled EOW geometry package, every source kernel carries the
required nonempty complex-open forward-base anchor package. -/
theorem blocker_d1N2ForwardBaseOpenAnchor_source_of_EOWGeometryPackage
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hgeom : d1N2ForwardSwapEOWGeometryPackage) :
    ∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF (Classical.choose hsource)
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) =
        (Classical.choose hsource) w) := by
  have hF_holo :
      DifferentiableOn ℂ (Classical.choose hsource) (ForwardTube 1 2) :=
    (Classical.choose_spec hsource).1
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup 1)
        (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
        (Classical.choose hsource)
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        (Classical.choose hsource) z :=
    (Classical.choose_spec hsource).2.1
  have hF_bv :
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ContinuousWithinAt (Classical.choose hsource) (ForwardTube 1 2)
          (fun k μ => (x k μ : ℂ)) :=
    (Classical.choose_spec hsource).2.2.1
  have hF_local :
      ∀ (i : Fin 2) (hi : i.val + 1 < 2),
        ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
          ∑ μ, minkowskiSignature 1 μ *
            (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
          (Classical.choose hsource)
            (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          (Classical.choose hsource) (fun k μ => (x k μ : ℂ)) :=
    (Classical.choose_spec hsource).2.2.2.1
  have hf_onFT :
      ∀ z, z ∈ ForwardTube 1 2 →
        (Classical.choose hsource) z =
          f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
    (Classical.choose_spec hsource).2.2.2.2
  let _ := hf_onFT
  exact d1N2ForwardBaseOpenAnchor_of_EOWGeometryPackage
    (Classical.choose hsource) hF_holo hF_lorentz hF_bv hF_local hgeom

/-- From source data plus the EOW geometry package, deduce forwardizable
invariant-kernel diff-zero (`d=1,n=2`). -/
theorem blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_of_EOWGeometryPackage
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hgeom : d1N2ForwardSwapEOWGeometryPackage) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  rcases hsource with ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    d1N2ForwardSwapEq_onFT_of_EOWGeometryPackage
      F hF_holo hF_lorentz hF_bv hF_local hgeom
  exact d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_forwardSwapEq
    F f hf_onFT hforward

/-- Under the bundled EOW geometry package, source kernels satisfy realizable-
pair involution symmetry (`d=1,n=2`). -/
theorem blocker_d1N2InvariantKernelPairSwapOnRealizable_source_of_EOWGeometryPackage
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hgeom : d1N2ForwardSwapEOWGeometryPackage) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  have hdiff :
      d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
    blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_of_EOWGeometryPackage
      f hsource hgeom
  exact (d1N2InvariantKernelPairSwapOnRealizable_iff_forwardizableDiffZero f).2 hdiff

/-- From source data plus connected `d=1,n=2` forward overlap and a nonempty
complex-open forward-base anchor where `extendF(swap·w)=F(w)`, deduce
realizable-pair involution symmetry of the source kernel. -/
theorem d1N2InvariantKernelPairSwapOnRealizable_source_of_connectedOpenAnchor
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hFwd_conn :
      IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)))
    (W : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hW_open : IsOpen W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1))
    (hW_eq : ∀ w ∈ W,
      extendF (Classical.choose hsource)
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) =
      (Classical.choose hsource) w) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  let F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ := Classical.choose hsource
  have hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2) :=
    (Classical.choose_spec hsource).1
  have hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z :=
    (Classical.choose_spec hsource).2.1
  have hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)) :=
    (Classical.choose_spec hsource).2.2.1
  have hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)) :=
    (Classical.choose_spec hsource).2.2.2.1
  have hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
    (Classical.choose_spec hsource).2.2.2.2
  let _ := hF_bv
  let _ := hF_local
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor
      F hF_holo hF_lorentz hFwd_conn W hW_open hW_ne
      (by simpa using hW_sub) hW_eq
  exact d1N2InvariantKernelPairSwapOnRealizable_of_forwardSwapEq
    F f hf_onFT hforward

/-- From realizable-pair involution symmetry of an invariant kernel model,
construct a nonempty complex-open forward-base anchor where
`extendF(swap·w)=F(w)`. -/
theorem d1N2ForwardBaseOpenAnchor_of_pairSwap
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hpair :
      ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s)) :
    ∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) = F w) := by
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable
      F f hf_onFT hpair
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  let W : Set (Fin 2 → Fin (1 + 1) → ℂ) := permForwardOverlapSet (d := 1) 2 τ
  have hW_open : IsOpen W := by
    have hset :
        adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) = W := by
      ext w
      constructor <;> intro hw <;>
        simpa [adjSwapForwardOverlapSet, permForwardOverlapSet, τ, permAct] using hw
    simpa [hset] using
      isOpen_adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)
  have hW_ne : W.Nonempty := by
    have hneAdj :
        (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)).Nonempty :=
      adjSwapForwardOverlap_nonempty (d := 1) 2 (0 : Fin 2) (by decide)
    have hset :
        adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) = W := by
      ext w
      constructor <;> intro hw <;>
        simpa [adjSwapForwardOverlapSet, permForwardOverlapSet, τ, permAct] using hw
    simpa [hset] using hneAdj
  refine ⟨W, hW_open, hW_ne, ?_, ?_⟩
  · intro w hwW
    simpa [W, τ] using hwW
  · intro w hwW
    rcases hwW with ⟨hwFT, hswapET⟩
    rcases Set.mem_iUnion.mp hswapET with ⟨Λ, u, huFT, hswap_eq⟩
    let y : Fin 2 → Fin (1 + 1) → ℂ :=
      complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)
    have hyFT : y ∈ ForwardTube 1 2 := by
      dsimp [y]
      simpa [hswap_eq, complexLorentzAction_inv] using huFT
    have hforward_eq :
        F y = F w := by
      have hyEq :
          F (complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)) = F w :=
        hforward w hwFT Λ⁻¹ hyFT
      simpa [y] using hyEq
    have hExt :
        extendF F (permAct (d := 1) τ w) = F y := by
      calc
        extendF F (permAct (d := 1) τ w)
            = extendF F (complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)) := by
                symm
                exact extendF_complex_lorentz_invariant
                  (d := 1) 2 F hF_holo hF_lorentz Λ⁻¹
                  (permAct (d := 1) τ w) hswapET
        _ = F y := by
              simpa [y] using
                extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz y hyFT
    calc
      extendF F (permAct (d := 1) τ w) = F y := hExt
      _ = F w := hforward_eq

/-- From source data and realizable-pair involution symmetry, construct a
nonempty complex-open forward-base anchor where `extendF(swap·w)=F(w)`. -/
theorem d1N2ForwardBaseOpenAnchor_source_of_pairSwap
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hpair :
      ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s)) :
    ∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF (Classical.choose hsource)
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) =
        (Classical.choose hsource) w) := by
  let F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ := Classical.choose hsource
  have hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2) :=
    (Classical.choose_spec hsource).1
  have hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z :=
    (Classical.choose_spec hsource).2.1
  have hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
    (Classical.choose_spec hsource).2.2.2.2
  exact d1N2ForwardBaseOpenAnchor_of_pairSwap
    F hF_holo hF_lorentz f hf_onFT hpair

/-- Exact reduction (`d=1,n=2`):
for source data and connected adjacent forward-overlap, realizable-pair
involution symmetry is equivalent to existence of a nonempty complex-open
forward-base anchor where `extendF(swap·w)=F(w)`. -/
theorem d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor_of_connectedForwardOverlap
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hFwd_conn :
      IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide))) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s)) ↔
    (∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF (Classical.choose hsource)
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) =
        (Classical.choose hsource) w)) := by
  constructor
  · intro hpair
    exact d1N2ForwardBaseOpenAnchor_source_of_pairSwap f hsource hpair
  · intro hanchor
    rcases hanchor with ⟨W, hW_open, hW_ne, hW_sub, hW_eq⟩
    exact d1N2InvariantKernelPairSwapOnRealizable_source_of_connectedOpenAnchor
      f hsource hFwd_conn W hW_open hW_ne hW_sub hW_eq

/-- Exact reduction (`d=1,n=2`):
for source data, realizable-pair involution symmetry is equivalent to the
existence of a nonempty complex-open forward-base anchor where
`extendF(swap·w)=F(w)`. -/
theorem d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s)) ↔
    (∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF (Classical.choose hsource)
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) =
        (Classical.choose hsource) w)) := by
  have hFwd_conn :
      IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)) :=
    d1N2_isConnected_adjSwapForwardOverlapSet_of_seedConnectedBlocker
  exact
    d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor_of_connectedForwardOverlap
      f hsource hFwd_conn

/-- Transfer principle (`d=1,n=2`):
for fixed `F`, any two invariant kernels that represent `F` on `FT_{1,2}`
induce the same forwardizable swap-difference vanishing law. -/
theorem d1N2InvariantKernelDiffZeroOnForwardizableQuadric_transfer
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f g : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hg_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = g (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hgfw : d1N2InvariantKernelDiffZeroOnForwardizableQuadric g) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    (d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric
      F g hg_onFT).2 hgfw
  exact (d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric
    F f hf_onFT).1 hforward

/-- For `d=1,n=2`, a swapped-invariant relation between two forward points
provides an explicit Lorentz witness from `swap·z` to `y`. -/
lemma d1N2_exists_forwardizingWitness_of_swappedInvariantQuad
    (z y : Fin 2 → Fin (1 + 1) → ℂ)
    (hz : z ∈ ForwardTube 1 2)
    (hy : y ∈ ForwardTube 1 2)
    (hquad : d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z)) :
    ∃ Γ : ComplexLorentzGroup 1,
      y = complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∧
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 := by
  let zswap : Fin 2 → Fin (1 + 1) → ℂ :=
    permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z
  have hquadZswap :
      d1InvariantQuad zswap = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
    calc
      d1InvariantQuad zswap
          = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
              rfl
      _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
  have hquadEq : d1InvariantQuad zswap = d1InvariantQuad y := by
    exact hquadZswap.trans hquad.symm
  have hU0_zswap_ne : d1U0 zswap ≠ 0 := by
    simpa [zswap, d1U0, permAct] using d1U1_ne_zero_of_forward z hz
  have hU0_y_ne : d1U0 y ≠ 0 := d1U0_ne_zero_of_forward y hy
  have hV0_y_ne : d1V0 y ≠ 0 := d1V0_ne_zero_of_forward y hy
  rcases d1_exists_lorentz_of_sameInvariantQuad_of_nonzeroU0V0
      hU0_zswap_ne hU0_y_ne hV0_y_ne hquadEq with ⟨Γ, hΓ⟩
  refine ⟨Γ, hΓ, ?_⟩
  simpa [hΓ] using hy

/-- Forward-swap equality on `FT_{1,2}` implies the swapped-invariant forward
equality statement used in the source invariant core. -/
theorem d1N2Source_swappedInvariantForwardEq_of_forwardSwapEq
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) :
    ∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
      z ∈ ForwardTube 1 2 →
      y ∈ ForwardTube 1 2 →
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
      F y = F z := by
  intro z y hz hy hquad
  rcases d1N2_exists_forwardizingWitness_of_swappedInvariantQuad z y hz hy hquad with
    ⟨Γ, hΓ, hΓswap⟩
  calc
    F y
        = F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) := by simp [hΓ]
    _ = F z := hforward z hz Γ hΓswap

/-- `d=1,n=2` exact reduction:
swapped-invariant forward equality for `F` is equivalent to base equality
`extendF(swap·z) = F(z)` on `FT_{1,2}` whenever `swap·z ∈ ET_{1,2}`. -/
theorem d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
    (∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
      z ∈ ForwardTube 1 2 →
      y ∈ ForwardTube 1 2 →
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
      F y = F z) ↔
    (∀ z, z ∈ ForwardTube 1 2 →
      permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 →
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F z) := by
  constructor
  · intro hswap z hz hswapET
    rcases Set.mem_iUnion.mp hswapET with ⟨Λ, u, huFT, hrepr⟩
    have hquadU :
        d1InvariantQuad u = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
      calc
        d1InvariantQuad u
            = d1InvariantQuad (complexLorentzAction Λ u) := by
                simpa using (d1InvariantQuad_lorentzAction Λ u).symm
        _ = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
              simp [hrepr]
        _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
    have hFuFz : F u = F z := hswap z u hz huFT hquadU
    calc
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
          = extendF F (complexLorentzAction Λ u) := by simp [hrepr]
      _ = extendF F u := by
            exact extendF_complex_lorentz_invariant
              (d := 1) 2 F hF_holo hF_lorentz Λ u
              (forwardTube_subset_extendedTube huFT)
      _ = F u := extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz u huFT
      _ = F z := hFuFz
  · intro hbase z y hz hy hquad
    rcases d1N2_exists_forwardizingWitness_of_swappedInvariantQuad z y hz hy hquad with
      ⟨Γ, hΓ, hΓswap⟩
    have hswapET :
        permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 := by
      have hyET : y ∈ ExtendedTube 1 2 := forwardTube_subset_extendedTube hy
      have hback :
          complexLorentzAction Γ⁻¹ y ∈ ExtendedTube 1 2 :=
        complexLorentzAction_mem_extendedTube (d := 1) (n := 2) (Λ := Γ⁻¹) hyET
      simpa [hΓ, complexLorentzAction_inv] using hback
    have hbaseEq :
        extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F z :=
      hbase z hz hswapET
    have hExtY :
        extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F y := by
      calc
        extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
            = extendF F (complexLorentzAction Γ
                (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) := by
                  symm
                  exact extendF_complex_lorentz_invariant
                    (d := 1) 2 F hF_holo hF_lorentz Γ
                    (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) hswapET
        _ = F (complexLorentzAction Γ
              (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) := by
                exact extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz
                  _ hΓswap
        _ = F y := by simp [hΓ]
    calc
      F y = extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := hExtY.symm
      _ = F z := hbaseEq

/-- Exact reduction (`d=1,n=2`, explicit source-field form):
realizable-pair involution symmetry for an invariant kernel is equivalent to the
swapped-invariant forward equality statement for the source field. -/
theorem d1N2InvariantKernelPairSwapOnRealizable_of_sourceField_iff_swappedInvariantForwardEq
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s)) ↔
    (∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
      z ∈ ForwardTube 1 2 →
      y ∈ ForwardTube 1 2 →
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
      F y = F z) := by
  constructor
  · intro hpair z y hz hy hquad
    have hquadRel :
        (d1S01 z) ^ 2 = 4 * ((d1P01 z) ^ 2 - d1Q0 z * d1Q1 z) :=
      d1_invariant_quadric_relation z
    have hreal :
        d1N2InvariantRealizable (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
      ⟨z, hz, rfl⟩
    have hswapReal :
        d1N2InvariantRealizable (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
      ⟨y, hy, hquad⟩
    have hker :
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
      hpair (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) hquadRel hreal hswapReal
    have hFy :
        F y = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
      calc
        F y = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hf_onFT y hy
        _ = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
              simpa [d1InvariantQuad] using congrArg
                (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquad
    have hFz :
        F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
      hf_onFT z hz
    have hFyFz : F y = F z := by
      calc
        F y = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := hFy
        _ = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hker.symm
        _ = F z := hFz.symm
    exact hFyFz
  · intro hswap q0 q1 p s _hquad hreal hswapReal
    rcases hreal with ⟨z, hz, hquadZ⟩
    rcases hswapReal with ⟨y, hy, hquadY⟩
    have hq0 : d1Q0 z = q0 := by
      simpa [d1InvariantQuad] using congrArg Prod.fst hquadZ
    have hq1 : d1Q1 z = q1 := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.1) hquadZ
    have hp : d1P01 z = p := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquadZ
    have hs : d1S01 z = s := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquadZ
    have hswapQuad :
        d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
      calc
        d1InvariantQuad y = (q1, q0, p, -s) := hquadY
        _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
              simp [hq0, hq1, hp, hs]
    have hFyFz : F y = F z := hswap z y hz hy hswapQuad
    have hleft : f q0 q1 p s = F z := by
      have hq :
          f q0 q1 p s = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := by
        simp [hq0, hq1, hp, hs]
      calc
        f q0 q1 p s = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hq
        _ = F z := by simpa using (hf_onFT z hz).symm
    have hright : f q1 q0 p (-s) = F y := by
      have hq :
          f q1 q0 p (-s) = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := by
        simpa [d1InvariantQuad] using
          (congrArg (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadY).symm
      calc
        f q1 q0 p (-s) = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hq
        _ = F y := by simpa using (hf_onFT y hy).symm
    calc
      f q0 q1 p s = F z := hleft
      _ = F y := hFyFz.symm
      _ = f q1 q0 p (-s) := hright.symm

/-- Exact reduction (`d=1,n=2`, source form):
realizable-pair involution symmetry for a source kernel is equivalent to the
swapped-invariant forward equality statement for the sourced field. -/
theorem d1N2InvariantKernelPairSwapOnRealizable_source_iff_swappedInvariantForwardEq
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s)) ↔
    (∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
      z ∈ ForwardTube 1 2 →
      y ∈ ForwardTube 1 2 →
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
      (Classical.choose hsource) y = (Classical.choose hsource) z) := by
  exact d1N2InvariantKernelPairSwapOnRealizable_of_sourceField_iff_swappedInvariantForwardEq
    (F := Classical.choose hsource) (f := f)
    ((Classical.choose_spec hsource).2.2.2.2)

/-- Exact reduction (`d=1,n=2`, source form):
swap-difference vanishing on realizable invariant pairs is equivalent to the
sourced swapped-invariant forward equality statement. -/
theorem d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_swappedInvariantForwardEq
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
    (∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
      z ∈ ForwardTube 1 2 →
      y ∈ ForwardTube 1 2 →
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
      (Classical.choose hsource) y = (Classical.choose hsource) z) := by
  have hpairiff :
      (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
      (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s)) := by
    constructor
    · intro hdiff q0 q1 p s hquad hreal hswapReal
      exact sub_eq_zero.mp (hdiff q0 q1 p s hquad hreal hswapReal)
    · intro hpair q0 q1 p s hquad hreal hswapReal
      exact sub_eq_zero.mpr (hpair q0 q1 p s hquad hreal hswapReal)
  exact hpairiff.trans
    (d1N2InvariantKernelPairSwapOnRealizable_source_iff_swappedInvariantForwardEq
      f hsource)

/-- Exact reduction (`d=1,n=2`, source form):
the realizable-pair invariant diff-zero statement is equivalent to forward-swap
equality on `FT_{1,2}` for the sourced field. -/
theorem d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_forwardSwapEq_onFT
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
    (∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        (Classical.choose hsource)
          (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) =
          (Classical.choose hsource) z) := by
  have hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      (Classical.choose hsource) z =
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
    (Classical.choose_spec hsource).2.2.2.2
  have hdiff_pair :
      (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
      (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s)) := by
    constructor
    · intro hdiff q0 q1 p s hquad hreal hswapReal
      exact sub_eq_zero.mp (hdiff q0 q1 p s hquad hreal hswapReal)
    · intro hpair q0 q1 p s hquad hreal hswapReal
      exact sub_eq_zero.mpr (hpair q0 q1 p s hquad hreal hswapReal)
  have hpair_forward :
      (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s)) ↔
      (∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          (Classical.choose hsource)
            (complexLorentzAction Γ
              (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) =
          (Classical.choose hsource) z) :=
    (d1N2ForwardSwapEq_onFT_iff_invariantKernelPairSwapOnRealizable
      (Classical.choose hsource) f hf_onFT).symm
  exact hdiff_pair.trans hpair_forward

/-- Exact reduction (`d=1,n=2`, source form):
the realizable-pair invariant diff-zero statement is equivalent to existence of
a nonempty complex-open forward-base anchor where `extendF(swap·w)=F(w)`. -/
theorem d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_openAnchor
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
    (∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF (Classical.choose hsource)
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) =
        (Classical.choose hsource) w)) := by
  have hdiff_pair :
      (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
      (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s)) := by
    constructor
    · intro hdiff q0 q1 p s hquad hreal hswapReal
      exact sub_eq_zero.mp (hdiff q0 q1 p s hquad hreal hswapReal)
    · intro hpair q0 q1 p s hquad hreal hswapReal
      exact sub_eq_zero.mpr (hpair q0 q1 p s hquad hreal hswapReal)
  exact hdiff_pair.trans
    (d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor f hsource)

/-- Under the bundled `d=1,n=2` EOW geometry package, source assumptions imply
the forward-base equality core statement. -/
theorem d1N2ForwardBaseEq_of_EOWGeometryPackage
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ)))
    (hgeom : d1N2ForwardSwapEOWGeometryPackage) :
    ∀ z, z ∈ ForwardTube 1 2 →
      permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 →
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F z := by
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    d1N2ForwardSwapEq_onFT_of_EOWGeometryPackage
      F hF_holo hF_lorentz hF_bv hF_local hgeom
  have hswapInv :
      ∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
        z ∈ ForwardTube 1 2 →
        y ∈ ForwardTube 1 2 →
        d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
        F y = F z :=
    d1N2Source_swappedInvariantForwardEq_of_forwardSwapEq F hforward
  exact (d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq
    F hF_holo hF_lorentz).1 hswapInv

/-- If adjacent forward-overlap is connected and one has a nonempty complex-open
forward-base anchor where `extendF(swap·w)=F(w)`, then the `d=1,n=2`
forward-base equality core follows. -/
theorem d1N2ForwardBaseEq_of_connectedForwardOverlap_and_openAnchor
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hFwd_conn :
      IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)))
    (W : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hW_open : IsOpen W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1))
    (hW_eq : ∀ w ∈ W,
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) = F w) :
    ∀ z, z ∈ ForwardTube 1 2 →
      permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 →
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F z := by
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor
      F hF_holo hF_lorentz hFwd_conn W hW_open hW_ne hW_sub hW_eq
  have hswapInv :
      ∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
        z ∈ ForwardTube 1 2 →
        y ∈ ForwardTube 1 2 →
        d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
        F y = F z :=
    d1N2Source_swappedInvariantForwardEq_of_forwardSwapEq F hforward
  exact (d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq
    F hF_holo hF_lorentz).1 hswapInv

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
vanishing of the swap-difference kernel on invariant tuples whose two swap-sign
partners are both realizable by `FT_{1,2}` points. -/
theorem blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0 := by
  -- Remaining invariant-only analytic core (`d=1,n=2`): involution symmetry
  -- on realizable invariant tuples.
  sorry

/-- Deferred invariant-function source core (`d=1,n=2`, open-anchor form):
the invariant-only realizable diff-zero core implies existence of a nonempty
complex-open forward-base anchor where `extendF(swap·w)=F(w)`. -/
theorem blocker_d1N2OpenAnchor_source_invariantAnalytic_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF (Classical.choose hsource)
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) =
        (Classical.choose hsource) w) := by
  exact
    (d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_openAnchor
      f hsource).1
      (blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred
        f hsource)

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
for source data, swapped-invariant equality on `FT_{1,2}` points. -/
theorem blocker_d1N2Source_swappedInvariantForwardEq_fromSource_invariantOnly_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
      z ∈ ForwardTube 1 2 →
      y ∈ ForwardTube 1 2 →
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
      (Classical.choose hsource) y = (Classical.choose hsource) z := by
  exact
    (d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_swappedInvariantForwardEq
      f hsource).1
      (blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred
        f hsource)

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
for a source kernel `f`, establish involution symmetry on invariant tuples whose
two swap-sign partners are both realizable by `FT_{1,2}` points. -/
theorem blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  intro q0 q1 p s hquad hreal hswapReal
  exact sub_eq_zero.mp
    (blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred
      f hsource q0 q1 p s hquad hreal hswapReal)

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
for source data `(F,hF_*)`, equal swapped invariant quadruples on `FT_{1,2}`
force equality of `F` values. -/
theorem blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ))) :
    ∀ z, z ∈ ForwardTube 1 2 →
      permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 →
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F z := by
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with
    ⟨f, hf_onFT⟩
  have hsource : d1N2InvariantKernelSource f :=
    ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hpair :
      ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s) :=
    blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred
      f hsource
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable
      F f hf_onFT hpair
  intro z hz hswapET
  rcases Set.mem_iUnion.mp hswapET with ⟨Λ, u, huFT, hswap_eq⟩
  let y : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Λ⁻¹ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
  have hyFT : y ∈ ForwardTube 1 2 := by
    dsimp [y]
    simpa [hswap_eq, complexLorentzAction_inv] using huFT
  have hforward_eq : F y = F z := by
    have hyEq :
        F (complexLorentzAction Λ⁻¹
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
      hforward z hz Λ⁻¹ hyFT
    simpa [y] using hyEq
  have hExt :
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F y := by
    calc
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
          = extendF F (complexLorentzAction Λ⁻¹
              (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) := by
                symm
                exact extendF_complex_lorentz_invariant
                  (d := 1) 2 F hF_holo hF_lorentz Λ⁻¹
                  (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) hswapET
      _ = F y := by
            simpa [y] using
              extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz y hyFT
  calc
    extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F y := hExt
    _ = F z := hforward_eq

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
for source data `(F,hF_*)`, equal swapped invariant quadruples on `FT_{1,2}`
force equality of `F` values. -/
theorem blocker_d1N2Source_swappedInvariantForwardEq_invariantOnly_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          F (fun k μ => (x k μ : ℂ))) :
    ∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
      z ∈ ForwardTube 1 2 →
      y ∈ ForwardTube 1 2 →
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
      F y = F z := by
  have hbase :
      ∀ z, z ∈ ForwardTube 1 2 →
        permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 →
        extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F z :=
    blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local
  exact
    (d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq
      F hF_holo hF_lorentz).2 hbase

/-- Deferred invariant-function source core (`d=1,n=2`, anchor-wrapper form):
deduce a nonempty complex-open forward-base anchor from the invariant-only
realizable-pair involution statement. -/
theorem blocker_d1N2ForwardBaseOpenAnchor_source_invariant_core_main_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF (Classical.choose hsource)
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) =
        (Classical.choose hsource) w) := by
  have hpair :
      ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s) :=
    blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred
      f hsource
  exact d1N2ForwardBaseOpenAnchor_source_of_pairSwap f hsource hpair

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
for a source kernel `f`, establish involution symmetry on invariant tuples whose
two swap-sign partners are both realizable by `FT_{1,2}` points. -/
theorem blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_main_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  exact blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred
    f hsource

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
for source data `(F,hF_*)`, equal swapped invariant quadruples on `FT_{1,2}`
force equality of `F` values. -/
theorem blocker_d1N2Source_swappedInvariantForwardEq_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
      z ∈ ForwardTube 1 2 →
      y ∈ ForwardTube 1 2 →
      d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
      F y = F z := by
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with
    ⟨f, hf_onFT⟩
  have hsource : d1N2InvariantKernelSource f :=
    ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hpair :
      ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s) :=
    blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_main_deferred
      f hsource
  intro z y hz hy hquad
  have hquadRel :
      (d1S01 z) ^ 2 = 4 * ((d1P01 z) ^ 2 - d1Q0 z * d1Q1 z) :=
    d1_invariant_quadric_relation z
  have hreal :
      d1N2InvariantRealizable (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
    ⟨z, hz, rfl⟩
  have hswapReal :
      d1N2InvariantRealizable (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
    ⟨y, hy, hquad⟩
  have hkernel :
      f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
        f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
    hpair (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) hquadRel hreal hswapReal
  have hFy :
      F y = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
    calc
      F y = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hf_onFT y hy
      _ = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
            simpa [d1InvariantQuad] using congrArg
              (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquad
  have hFz :
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
    hf_onFT z hz
  calc
    F y = f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := hFy
    _ = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hkernel.symm
    _ = F z := hFz.symm

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
for a source kernel `f`, establish involution symmetry on invariant tuples whose
two swap-sign partners are both realizable by `FT_{1,2}` points. -/
theorem blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  exact blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_main_deferred
    f hsource

/-- Deferred `d=1,n=2` source-open-anchor core:
from source hypotheses, construct a nonempty complex-open anchor subset of the
forward-overlap base where `extendF(swap·w)=F(w)` holds. -/
theorem blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) = F w) := by
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with
    ⟨f, hf_onFT⟩
  have hsource : d1N2InvariantKernelSource f :=
    ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hpair :
      ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s) :=
    blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred
      f hsource
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable
      F f hf_onFT hpair
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  let W : Set (Fin 2 → Fin (1 + 1) → ℂ) := permForwardOverlapSet (d := 1) 2 τ
  have hW_open : IsOpen W := by
    have hset :
        adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) = W := by
      ext w
      constructor <;> intro hw <;>
        simpa [adjSwapForwardOverlapSet, permForwardOverlapSet, τ, permAct] using hw
    simpa [hset] using
      isOpen_adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)
  have hW_ne : W.Nonempty := by
    have hneAdj :
        (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)).Nonempty :=
      adjSwapForwardOverlap_nonempty (d := 1) 2 (0 : Fin 2) (by decide)
    have hset :
        adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) = W := by
      ext w
      constructor <;> intro hw <;>
        simpa [adjSwapForwardOverlapSet, permForwardOverlapSet, τ, permAct] using hw
    simpa [hset] using hneAdj
  refine ⟨W, hW_open, hW_ne, ?_, ?_⟩
  · intro w hwW
    simpa [W, τ] using hwW
  · intro w hwW
    rcases hwW with ⟨hwFT, hswapET⟩
    rcases Set.mem_iUnion.mp hswapET with ⟨Λ, u, huFT, hswap_eq⟩
    let y : Fin 2 → Fin (1 + 1) → ℂ :=
      complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)
    have hyFT : y ∈ ForwardTube 1 2 := by
      dsimp [y]
      simpa [hswap_eq, complexLorentzAction_inv] using huFT
    have hforward_eq :
        F y = F w := by
      have hyEq :
          F (complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)) = F w :=
        hforward w hwFT Λ⁻¹ hyFT
      simpa [y] using hyEq
    have hExt :
        extendF F (permAct (d := 1) τ w) = F y := by
      calc
        extendF F (permAct (d := 1) τ w)
            = extendF F (complexLorentzAction Λ⁻¹ (permAct (d := 1) τ w)) := by
                symm
                exact extendF_complex_lorentz_invariant
                  (d := 1) 2 F hF_holo hF_lorentz Λ⁻¹
                  (permAct (d := 1) τ w) hswapET
        _ = F y := by
              simpa [y] using
                extendF_eq_on_forwardTube 2 F hF_holo hF_lorentz y hyFT
    calc
      extendF F (permAct (d := 1) τ w) = F y := hExt
      _ = F w := hforward_eq

/-- Exact reduction (`d=1,n=2`, source form):
the forward-base equality core is equivalent to existence of a nonempty
complex-open forward-base anchor, using the connected forward-overlap bridge. -/
theorem d1N2ForwardBaseEq_source_iff_openAnchor
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    (∀ z, z ∈ ForwardTube 1 2 →
      permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 →
      extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) = F z) ↔
    (∃ W : Set (Fin 2 → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      (∀ w ∈ W,
        extendF F (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) = F w)) := by
  constructor
  · intro hbase
    rcases blocker_d1N2InvariantFactorization_core_deferred
        F hF_holo hF_lorentz hF_bv hF_local with ⟨f, hf_onFT⟩
    have hswapInv :
        ∀ z y : Fin 2 → Fin (1 + 1) → ℂ,
          z ∈ ForwardTube 1 2 →
          y ∈ ForwardTube 1 2 →
          d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) →
          F y = F z :=
      (d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq
        F hF_holo hF_lorentz).2 hbase
    have hpair :
        ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
          d1N2InvariantRealizable q0 q1 p s →
          d1N2InvariantRealizable q1 q0 p (-s) →
          f q0 q1 p s = f q1 q0 p (-s) := by
      intro q0 q1 p s _hquad hreal hswapReal
      rcases hreal with ⟨z, hz, hquadZ⟩
      rcases hswapReal with ⟨y, hy, hquadY⟩
      have hq0 : d1Q0 z = q0 := by
        simpa [d1InvariantQuad] using congrArg Prod.fst hquadZ
      have hq1 : d1Q1 z = q1 := by
        simpa [d1InvariantQuad] using congrArg (fun t => t.2.1) hquadZ
      have hp : d1P01 z = p := by
        simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquadZ
      have hs : d1S01 z = s := by
        simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquadZ
      have hswapQuad :
          d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
        calc
          d1InvariantQuad y = (q1, q0, p, -s) := hquadY
          _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := by
                simp [hq0, hq1, hp, hs]
      have hFyFz : F y = F z := hswapInv z y hz hy hswapQuad
      have hleft : f q0 q1 p s = F z := by
        have hq :
            f q0 q1 p s = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := by
          simp [hq0, hq1, hp, hs]
        calc
          f q0 q1 p s = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hq
          _ = F z := by simpa using (hf_onFT z hz).symm
      have hright : f q1 q0 p (-s) = F y := by
        have hq :
            f q1 q0 p (-s) = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := by
          simpa [d1InvariantQuad] using
            (congrArg (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadY).symm
        calc
          f q1 q0 p (-s) = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hq
          _ = F y := by simpa using (hf_onFT y hy).symm
      calc
        f q0 q1 p s = F z := hleft
        _ = F y := hFyFz.symm
        _ = f q1 q0 p (-s) := hright.symm
    exact d1N2ForwardBaseOpenAnchor_of_pairSwap
      F hF_holo hF_lorentz f hf_onFT hpair
  · intro hanchor
    have hFwd_conn :
        IsConnected (adjSwapForwardOverlapSet (d := 1) 2 (0 : Fin 2) (by decide)) :=
      d1N2_isConnected_adjSwapForwardOverlapSet_of_seedConnectedBlocker
    rcases hanchor with ⟨W, hW_open, hW_ne, hW_sub, hW_eq⟩
    exact d1N2ForwardBaseEq_of_connectedForwardOverlap_and_openAnchor
      F hF_holo hF_lorentz hFwd_conn W hW_open hW_ne hW_sub hW_eq

/-- Deferred invariant-function source core (`d=1,n=2`, realizable-pair form):
for a source kernel `f`, establish involution symmetry on invariant tuples whose
two swap-sign partners are both realizable by `FT_{1,2}` points. -/
theorem blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  exact blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred
    f hsource

/-- Deferred invariant-function analytic core (`d=1,n=2`):
existence of an invariant kernel model on `FT_{1,2}` whose swap-difference
vanishes on the full invariant quadric. -/
theorem blocker_d1N2InvariantQuadricModel_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ g : ℂ → ℂ → ℂ → ℂ → ℂ,
      (∀ z, z ∈ ForwardTube 1 2 →
        F z = g (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) ∧
      d1N2InvariantKernelDiffZeroOnQuadric g := by
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with
    ⟨f, hf_onFT⟩
  have hsource : d1N2InvariantKernelSource f :=
    ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hpair :
      ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantRealizable q0 q1 p s →
        d1N2InvariantRealizable q1 q0 p (-s) →
        f q0 q1 p s = f q1 q0 p (-s) :=
    blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred f hsource
  let g : ℂ → ℂ → ℂ → ℂ → ℂ :=
    fun q0 q1 p s =>
      if hq : d1N2InvariantRealizable q0 q1 p s then
        if hqs : d1N2InvariantRealizable q1 q0 p (-s) then
          (f q0 q1 p s + f q1 q0 p (-s)) / 2
        else
          f q0 q1 p s
      else
        if hqs : d1N2InvariantRealizable q1 q0 p (-s) then
          f q1 q0 p (-s)
        else
          0
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    have hq : d1N2InvariantRealizable (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
      ⟨z, hz, rfl⟩
    by_cases hqs : d1N2InvariantRealizable (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z)
    · have heq :
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
        hpair (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
          (d1_invariant_quadric_relation z) hq hqs
      calc
        F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hf_onFT z hz
        _ = (f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) +
              f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z)) / 2 := by
              rw [heq]
              ring
        _ = g (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := by
              simp [g, hq, hqs]
    · calc
        F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hf_onFT z hz
        _ = g (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := by
              simp [g, hq, hqs]
  · intro q0 q1 p s _hrel
    by_cases hq : d1N2InvariantRealizable q0 q1 p s
    · by_cases hqs : d1N2InvariantRealizable q1 q0 p (-s)
      · apply sub_eq_zero.mpr
        simp [g, hq, hqs, neg_neg, add_comm]
      · apply sub_eq_zero.mpr
        simp [g, hq, hqs, neg_neg]
    · by_cases hqs : d1N2InvariantRealizable q1 q0 p (-s)
      · apply sub_eq_zero.mpr
        simp [g, hq, hqs, neg_neg]
      · apply sub_eq_zero.mpr
        simp [g, hq, hqs, neg_neg]

/-- Deferred invariant-function source core (`d=1,n=2`):
from the Wightman-source package, deduce vanishing of the invariant-kernel
swap-difference on forwardizable quadric points. -/
theorem blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  intro q0 q1 p s hquad hfw
  rcases d1N2InvariantRealizable_pair_of_forwardizable hfw with ⟨hreal, hswapReal⟩
  have heq :
      f q0 q1 p s = f q1 q0 p (-s) :=
    blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred
      f hsource q0 q1 p s hquad hreal hswapReal
  exact sub_eq_zero.mpr heq

/-- Deferred invariant-function source core (`d=1,n=2`):
from the Wightman-source package, prove the forwardizable involution law
directly in invariant coordinates. -/
theorem blocker_d1N2InvariantKernelSwapOnForwardizable_source_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantForwardizableSwap q0 q1 p s →
      f q0 q1 p s = f q1 q0 p (-s) := by
  intro q0 q1 p s hquad hfw
  have hzero :
      f q0 q1 p s - f q1 q0 p (-s) = 0 :=
    blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred
      f hsource q0 q1 p s hquad hfw
  exact sub_eq_zero.mp hzero

/-- Deferred invariant-function source core (`d=1,n=2`):
from the Wightman-source package, deduce vanishing of the invariant-kernel
swap-difference on forwardizable quadric points. -/
theorem blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  intro q0 q1 p s hquad hfw
  exact blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred
    f hsource q0 q1 p s hquad hfw

/-- Reduce forward-swap equality on `FT_{1,2}` to pointwise existence of a
slice anchor that already realizes equality on the swapped-forwardized point. -/
theorem d1N2ForwardSwapEq_onFT_of_pointwiseSliceAnchor
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hanchor :
      ∀ z, z ∈ ForwardTube 1 2 →
        (∃ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2) →
        ∃ Λ₀ : ComplexLorentzGroup 1,
          complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 ∧
          F (complexLorentzAction Λ₀
              (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  intro z hz Γ hΓswap
  rcases hanchor z hz ⟨Γ, hΓswap⟩ with ⟨Λ₀, hΛ₀swap, hΛ₀eq⟩
  let w : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Λ₀
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
  have hwFT : w ∈ ForwardTube 1 2 := by
    simpa [w] using hΛ₀swap
  have hΓ_from_w :
      complexLorentzAction (Γ * Λ₀⁻¹) w =
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
    dsimp [w]
    simp [complexLorentzAction_mul, complexLorentzAction_inv]
  have hΓ_from_wFT :
      complexLorentzAction (Γ * Λ₀⁻¹) w ∈ ForwardTube 1 2 := by
    simpa [hΓ_from_w] using hΓswap
  have hΓ_eq_Λ₀ :
      F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z))
        = F w := by
    have hinv := complex_lorentz_invariance 2 F hF_holo hF_lorentz
      (Γ * Λ₀⁻¹) w hwFT hΓ_from_wFT
    simpa [hΓ_from_w] using hinv
  calc
    F (complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z))
        = F w := hΓ_eq_Λ₀
    _ = F z := by simpa [w] using hΛ₀eq

/-- Pointwise slice-anchor propagation at fixed `w` (`d=1,n=2`):
if one anchor witness already matches `F w`, then every forwardizing witness
gives the same value. -/
theorem d1N2ForwardEq_of_sliceAnchorAtPoint
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (w : Fin 2 → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (hΓswap :
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2)
    (hanchorAt :
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) :
    F (complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w := by
  rcases hanchorAt with ⟨Λ₀, hΛ₀swap, hΛ₀eq⟩
  let z₀ : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Λ₀
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)
  have htarget :
      complexLorentzAction (Γ * Λ₀⁻¹) z₀ =
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) := by
    dsimp [z₀]
    simp [complexLorentzAction_mul, complexLorentzAction_inv]
  have hcinv :
      F (complexLorentzAction (Γ * Λ₀⁻¹) z₀) = F z₀ :=
    complex_lorentz_invariance 2 F hF_holo hF_lorentz (Γ * Λ₀⁻¹) z₀
      (by simpa [z₀] using hΛ₀swap)
      (by simpa [htarget] using hΓswap)
  calc
    F (complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w))
        = F (complexLorentzAction (Γ * Λ₀⁻¹) z₀) := by
            simp [htarget]
    _ = F z₀ := hcinv
    _ = F (complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) := by simp [z₀]
    _ = F w := hΛ₀eq

/-- On prepared neighborhoods (`d=1,n=2`), eventual slice-anchor existence and
eventual fixed-witness forward equality are equivalent. -/
theorem d1N2EventuallySliceAnchor_iff_eventuallyForwardEq_fixedWitness
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (w0 : Fin 2 → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    (∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) ↔
    (∀ᶠ w in 𝓝 w0, w ∈ U →
      F (complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) := by
  constructor
  · intro hanchor
    filter_upwards [hanchor] with w hwAnchor hwU
    have hΓswap :
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 :=
      (hU_good w hwU).2
    exact d1N2ForwardEq_of_sliceAnchorAtPoint
      F hF_holo hF_lorentz w Γ hΓswap (hwAnchor hwU)
  · intro hforward
    filter_upwards [hforward] with w hwForward hwU
    refine ⟨Γ, (hU_good w hwU).2, hwForward hwU⟩

/-- Deferred local fixed-witness forward equality core (`d=1,n=2`):
on a prepared neighborhood with fixed witness `Γ`, prove eventual
`F(Γ·(swap·w)) = F(w)`. -/
theorem blocker_d1N2LocalForwardEqNhd_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (w0 : Fin 2 → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      F (complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w := by
  let _ := hU_open
  let _ := hw0U
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with
    ⟨f, hf_onFT⟩
  have hsource : d1N2InvariantKernelSource f :=
    ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hquadDiff :
      d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
    blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred
      f hsource
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Λ : ComplexLorentzGroup 1,
          complexLorentzAction Λ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Λ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    (d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric
      F f hf_onFT).2 hquadDiff
  exact Filter.Eventually.of_forall (fun w hwU => by
    exact hforward w (hU_good w hwU).1.1 Γ (hU_good w hwU).2)

/-- Deferred local prepared-neighborhood anchor extraction (`d=1,n=2`):
on a prepared neighborhood with fixed witness `Γ`, produce eventual slice
anchors carrying `F`-equality. -/
theorem blocker_d1N2LocalSliceAnchorNhd_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (w0 : Fin 2 → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w := by
  have hforward :
      ∀ᶠ w in 𝓝 w0, w ∈ U →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w :=
    blocker_d1N2LocalForwardEqNhd_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local w0 Γ U hU_open hw0U hU_good
  exact (d1N2EventuallySliceAnchor_iff_eventuallyForwardEq_fixedWitness
    F hF_holo hF_lorentz w0 Γ U hU_good).2 hforward

/-- For `d=1,n=2`, pointwise slice-anchor existence and full forward-swap
equality on `FT_{1,2}` are equivalent. -/
theorem d1N2PointwiseSliceAnchor_iff_forwardSwapEq_onFT
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
    (∀ z, z ∈ ForwardTube 1 2 →
      (∃ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2) →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) ↔
    (∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) := by
  constructor
  · intro hanchor
    exact d1N2ForwardSwapEq_onFT_of_pointwiseSliceAnchor
      F hF_holo hF_lorentz hanchor
  · intro hforward z hz hex
    rcases hex with ⟨Γ, hΓswap⟩
    exact ⟨Γ, hΓswap, hforward z hz Γ hΓswap⟩

/-- Exact reduction (`d=1,n=2`, source form):
the realizable-pair invariant diff-zero statement is equivalent to pointwise
slice-anchor existence for the sourced field. -/
theorem d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_pointwiseSliceAnchor
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
    (∀ z, z ∈ ForwardTube 1 2 →
      (∃ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2) →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 ∧
        (Classical.choose hsource)
          (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) =
          (Classical.choose hsource) z) := by
  have hF_holo :
      DifferentiableOn ℂ (Classical.choose hsource) (ForwardTube 1 2) :=
    (Classical.choose_spec hsource).1
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup 1)
        (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
        (Classical.choose hsource)
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        (Classical.choose hsource) z :=
    (Classical.choose_spec hsource).2.1
  calc
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantRealizable q0 q1 p s →
      d1N2InvariantRealizable q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
        (∀ z, z ∈ ForwardTube 1 2 →
          ∀ Γ : ComplexLorentzGroup 1,
            complexLorentzAction Γ
              (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
            (Classical.choose hsource)
              (complexLorentzAction Γ
                (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) =
            (Classical.choose hsource) z) :=
      d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_forwardSwapEq_onFT
        f hsource
    _ ↔
      (∀ z, z ∈ ForwardTube 1 2 →
        (∃ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2) →
        ∃ Λ₀ : ComplexLorentzGroup 1,
          complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 ∧
          (Classical.choose hsource)
            (complexLorentzAction Λ₀
              (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) =
            (Classical.choose hsource) z) := by
        symm
        exact d1N2PointwiseSliceAnchor_iff_forwardSwapEq_onFT
          (Classical.choose hsource) hF_holo hF_lorentz

/-- Deferred invariant-function source core (`d=1,n=2`, pointwise form):
from the active realizable-pair diff-zero core, extract pointwise slice-anchor
existence for the sourced field on `FT_{1,2}`. -/
theorem blocker_d1N2PointwiseSliceAnchor_fromSource_invariantOnly_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ z, z ∈ ForwardTube 1 2 →
      (∃ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2) →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 ∧
        (Classical.choose hsource)
          (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) =
          (Classical.choose hsource) z := by
  exact
    (d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_pointwiseSliceAnchor
      f hsource).1
      (blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred
        f hsource)

/-- Deferred local analytic anchor extraction (`d=1,n=2`):
for each forwardizable `z ∈ FT_{1,2}`, produce one slice anchor `Λ₀` already
satisfying `F(Λ₀·(swap·z)) = F(z)`. -/
theorem blocker_d1N2PointwiseSliceAnchor_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∀ z, z ∈ ForwardTube 1 2 →
      (∃ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2) →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  intro z hz hfw
  rcases hfw with ⟨Γ, hΓswap⟩
  let τ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  let U : Set (Fin 2 → Fin (1 + 1) → ℂ) :=
    permForwardOverlapSet (d := 1) 2 τ ∩
    {w | complexLorentzAction Γ (permAct (d := 1) τ w) ∈ ForwardTube 1 2}
  have hperm_cont :
      Continuous (fun w : Fin 2 → Fin (1 + 1) → ℂ => permAct (d := 1) τ w) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (τ k))
  have hU_open : IsOpen U := by
    have hΩ_open : IsOpen (permForwardOverlapSet (d := 1) 2 τ) := by
      change IsOpen (ForwardTube 1 2 ∩ (permAct (d := 1) τ) ⁻¹' ExtendedTube 1 2)
      exact isOpen_forwardTube.inter (isOpen_extendedTube.preimage hperm_cont)
    have hΓswap_open :
        IsOpen {w : Fin 2 → Fin (1 + 1) → ℂ |
          complexLorentzAction Γ (permAct (d := 1) τ w) ∈ ForwardTube 1 2} := by
      exact isOpen_forwardTube.preimage
        ((continuous_complexLorentzAction_snd Γ).comp hperm_cont)
    exact hΩ_open.inter hΓswap_open
  have hswapET : permAct (d := 1) τ z ∈ ExtendedTube 1 2 := by
    have hΓswapET :
        complexLorentzAction Γ (permAct (d := 1) τ z) ∈ ExtendedTube 1 2 :=
      forwardTube_subset_extendedTube hΓswap
    have hback :
        complexLorentzAction Γ⁻¹
          (complexLorentzAction Γ (permAct (d := 1) τ z)) ∈ ExtendedTube 1 2 :=
      complexLorentzAction_mem_extendedTube (d := 1) (n := 2) (Λ := Γ⁻¹) hΓswapET
    simpa [complexLorentzAction_inv] using hback
  have hzU : z ∈ U := by
    refine ⟨?_, hΓswap⟩
    exact ⟨hz, hswapET⟩
  have hU_good :
      ∀ w ∈ U,
        w ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 := by
    intro w hwU
    simpa [U, τ] using hwU
  have hlocal :
      ∀ᶠ w in 𝓝 z, w ∈ U →
        ∃ Λ₀ : ComplexLorentzGroup 1,
          complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
          F (complexLorentzAction Λ₀
              (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w :=
    blocker_d1N2LocalSliceAnchorNhd_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local z Γ U hU_open hzU hU_good
  have hz_local :
      z ∈ {w : Fin 2 → Fin (1 + 1) → ℂ |
        w ∈ U →
          ∃ Λ₀ : ComplexLorentzGroup 1,
            complexLorentzAction Λ₀
              (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
            F (complexLorentzAction Λ₀
                (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w} :=
    Filter.Eventually.self_of_nhds hlocal
  exact hz_local hzU

/-- Deferred invariant-function analytic core (`d=1,n=2`):
pure quadric-level involution law on Lorentz invariants. -/
theorem blocker_d1N2InvariantKernelSwapOnQuadric_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquadDiff : d1N2InvariantKernelDiffZeroOnQuadric f) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  exact d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_quadric f hquadDiff

/-- Deferred analytic core (`d=1,n=2`, invariant route):
from the Wightman-source package and `FT` invariant factorization, prove that
the invariant-kernel swap-difference vanishes on forwardizable quadric points. -/
theorem blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  have hsource : d1N2InvariantKernelSource f :=
    ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  exact blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred
    f hsource

/-- `d=1,n=2` invariant-function core (deferred):
construct a swap-compatible invariant-kernel model on `FT`. -/
theorem blocker_d1N2InvariantModel_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    d1N2InvariantModel F := by
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with
    ⟨f, hf_onFT⟩
  have hquadDiff :
      d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
    blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local f hf_onFT
  have hf_swap :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
            f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
    blocker_d1N2InvariantKernelSwap_core_of_forwardizableQuadricDiffZero
      f hquadDiff
  exact ⟨f, hf_onFT, hf_swap⟩

/-- Deferred bridge (`d=1,n=2`): extract the forwardizable invariant
swap-difference vanishing statement from the Wightman-source package. -/
theorem blocker_d1N2InvariantKernelSwapOnForwardizable_core_fromSource_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  rcases hsource with ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  exact blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local f hf_onFT

/-- `d=1,n=2` invariant-function step B:
kernel swap symmetry reduced to forward-swap equality from the invariant model. -/
theorem blocker_d1N2InvariantKernelSwap_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  have hsource : d1N2InvariantKernelSource f :=
    ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hquadDiff : d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
    blocker_d1N2InvariantKernelSwapOnForwardizable_core_fromSource_deferred f hsource
  exact blocker_d1N2InvariantKernelSwap_core_of_forwardizableQuadricDiffZero
    f hquadDiff

/-- `d=1,n=2` forward swap equality on `FT`, reduced to the invariant model. -/
theorem blocker_d1N2ForwardSwapEq_on_FT_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with
    ⟨f, hf_onFT⟩
  have hkernel :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
            f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) :=
    blocker_d1N2InvariantKernelSwap_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local f hf_onFT
  exact (d1_n2_forwardSwapEq_iff_invariantKernelSwapRule F f hf_onFT).2 hkernel

/-- Deferred `d=1` local slice-anchor input at a prepared adjacent-swap anchor. -/
theorem blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial
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
    (τ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n τ ∧
      complexLorentzAction Γ (permAct (d := 1) τ w) ∈ ForwardTube 1 n)
    (hn2 : ¬ n ≤ 1)
    (hτ : τ ≠ 1) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀ (permAct (d := 1) τ w) ∈ ForwardTube 1 n ∧
        F (complexLorentzAction Λ₀ (permAct (d := 1) τ w)) = F w := by
  by_cases h2 : n = 2
  · subst h2
    have hτswap : τ = Equiv.swap (0 : Fin 2) 1 :=
      fin2_perm_ne_one_eq_swap01 τ hτ
    subst hτswap
    exact blocker_d1N2LocalSliceAnchorNhd_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local w0 Γ U hU_open hw0U hU_good
  · -- Remaining nontrivial local branches (`n = 3` and `4 ≤ n`) stay deferred.
    sorry

/-- Deferred `d=1` local slice-anchor input at a prepared adjacent-swap anchor. -/
theorem blocker_eventually_slice_anchor_on_prepared_nhds_d1
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
    (τ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n τ ∧
      complexLorentzAction Γ (permAct (d := 1) τ w) ∈ ForwardTube 1 n) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀ (permAct (d := 1) τ w) ∈ ForwardTube 1 n ∧
        F (complexLorentzAction Λ₀ (permAct (d := 1) τ w)) = F w := by
  by_cases hτ : τ = 1
  · subst hτ
    exact Filter.Eventually.of_forall (fun w hwU => by
      refine ⟨(1 : ComplexLorentzGroup 1), ?_, ?_⟩
      · have hwFT : w ∈ ForwardTube 1 n := (hU_good w hwU).1.1
        simpa [permAct, complexLorentzAction_one] using hwFT
      · have hperm : permAct (d := 1) (1 : Equiv.Perm (Fin n)) w = w := by
          ext k μ
          simp [permAct]
        simp [complexLorentzAction_one, hperm])
  · by_cases hn : n ≤ 1
    · have hsub : Subsingleton (Fin n) := by
        refine ⟨?_⟩
        intro a b
        apply Fin.ext
        have ha0 : a.val = 0 := by omega
        have hb0 : b.val = 0 := by omega
        omega
      letI : Subsingleton (Fin n) := hsub
      exact (hτ (Subsingleton.elim τ 1)).elim
    · -- Remaining nontrivial branch (`n ≥ 2`, `τ ≠ 1`) is deferred.
      exact blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial
        n F hF_holo hF_lorentz hF_bv hF_local
        τ w0 Γ U hU_open hw0U hU_good hn hτ

/-- Deferred `d=1` geometric input B (`n ≥ 4` branch): forward-triple witness. -/
theorem blocker_d1_forward_triple_nonempty_nge4
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hσ : σ ≠ (1 : Equiv.Perm (Fin n)))
    (hστ : σ ≠ Equiv.swap i ⟨i.val + 1, hi⟩)
    (hn4 : 4 ≤ n) :
    ({w : Fin n → Fin (1 + 1) → ℂ |
        w ∈ ForwardTube 1 n ∧
        permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) w ∈ ExtendedTube 1 n ∧
        permAct (d := 1) σ w ∈ ExtendedTube 1 n
    }).Nonempty := by
  sorry

end BHW
