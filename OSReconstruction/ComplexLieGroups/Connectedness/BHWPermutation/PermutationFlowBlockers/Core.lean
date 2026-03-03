import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2Invariants
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2LorentzInvariantRoute
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2RealWitnessObstruction
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

/-- Scalar light-cone witness form: a forward point whose invariants are
`(q0,q1,p,s)`. -/
def d1N2InvariantLightConeWitness (q0 q1 p s : ℂ) : Prop :=
  ∃ z : Fin 2 → Fin (1 + 1) → ℂ,
    z ∈ ForwardTube 1 2 ∧
    d1Q0 z = q0 ∧ d1Q1 z = q1 ∧ d1P01 z = p ∧ d1S01 z = s

/-- Unfolding lemma for `d1N2InvariantLightConeWitness`. -/
theorem d1N2InvariantLightConeWitness_iff_exists_forwardInvariants
    (q0 q1 p s : ℂ) :
    d1N2InvariantLightConeWitness q0 q1 p s ↔
      ∃ z : Fin 2 → Fin (1 + 1) → ℂ,
        z ∈ ForwardTube 1 2 ∧
        d1Q0 z = q0 ∧ d1Q1 z = q1 ∧ d1P01 z = p ∧ d1S01 z = s := by
  rfl

/-- Equivalent scalar light-cone witness form of `d1N2InvariantRealizable`. -/
lemma d1N2InvariantRealizable_iff_lightConeWitness
    (q0 q1 p s : ℂ) :
    d1N2InvariantRealizable q0 q1 p s ↔
      d1N2InvariantLightConeWitness q0 q1 p s := by
  constructor
  · rintro ⟨z, hz, hquad⟩
    have hq0 : d1Q0 z = q0 := by
      simpa [d1InvariantQuad] using congrArg Prod.fst hquad
    have hq1 : d1Q1 z = q1 := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.1) hquad
    have hp : d1P01 z = p := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquad
    have hs : d1S01 z = s := by
      simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquad
    exact (d1N2InvariantLightConeWitness_iff_exists_forwardInvariants q0 q1 p s).2
      ⟨z, hz, hq0, hq1, hp, hs⟩
  · intro hwit
    rcases (d1N2InvariantLightConeWitness_iff_exists_forwardInvariants q0 q1 p s).1 hwit with
      ⟨z, hz, hq0, hq1, hp, hs⟩
    refine ⟨z, hz, ?_⟩
    simp [d1InvariantQuad, hq0, hq1, hp, hs]

/-- The swapped probe tuple `(-9,-1,-3,0)` is not realized by any
`FT_{1,2}` configuration. -/
lemma d1N2InvariantRealizable_swappedProbe_not :
    ¬ d1N2InvariantRealizable (-9 : ℂ) (-1 : ℂ) (-3 : ℂ) 0 := by
  intro hreal
  rcases hreal with ⟨z, hz, hquad⟩
  have hQ0 : d1Q0 z = (-9 : ℂ) := by
    simpa [d1InvariantQuad] using congrArg Prod.fst hquad
  have hP : d1P01 z = (-3 : ℂ) := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquad
  have hS : d1S01 z = (0 : ℂ) := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquad
  have hU0V0 : d1U0 z * d1V0 z = (9 : ℂ) := by
    apply neg_injective
    simpa [d1Q0_eq_neg_U0_mul_V0] using hQ0
  have hR : d1R01 z = (3 : ℂ) := by
    calc
      d1R01 z = (d1S01 z - (2 : ℂ) * d1P01 z) / 2 := d1R01_eq_of_P01_S01 z
      _ = (3 : ℂ) := by simp [hS, hP]
  have hU0_ne : d1U0 z ≠ 0 := d1U0_ne_zero_of_forward z hz
  have hV1_eq : d1V1 z = ((1 : ℂ) / 3) * d1V0 z := by
    apply (mul_left_cancel₀ hU0_ne)
    calc
      d1U0 z * d1V1 z = d1R01 z := by simp [d1R01]
      _ = (3 : ℂ) := hR
      _ = ((1 : ℂ) / 3) * (9 : ℂ) := by norm_num
      _ = ((1 : ℂ) / 3) * (d1U0 z * d1V0 z) := by rw [hU0V0]
      _ = d1U0 z * (((1 : ℂ) / 3) * d1V0 z) := by ring
  have hDiffPos : 0 < (d1V1 z - d1V0 z).im := by
    rcases (forwardTube_d1_n2_iff z).1 hz with ⟨_hz0cone, hzdiffcone⟩
    have hpmd := (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).1 hzdiffcone
    have hdiff :
        (fun μ => (z 1 μ - z 0 μ).im) 0 -
          (fun μ => (z 1 μ - z 0 μ).im) 1 =
        (d1V1 z - d1V0 z).im := by
      simp [d1V0, d1V1, Complex.sub_im]
      ring
    exact hdiff ▸ hpmd.2
  have hV0ImPos : 0 < (d1V0 z).im := d1V0_im_pos_of_forward z hz
  have hDiffNeg : (d1V1 z - d1V0 z).im < 0 := by
    rw [hV1_eq]
    have hrewrite :
        ((1 : ℂ) / 3) * d1V0 z - d1V0 z =
          (((1 : ℂ) / 3) - 1) * d1V0 z := by ring
    rw [hrewrite]
    have hcoeff :
        ((((1 : ℂ) / 3 - 1) * d1V0 z).im) = ((-(2 : ℝ) / 3) * (d1V0 z).im) := by
      norm_num [Complex.mul_im]
    rw [hcoeff]
    have hcoef_neg : (-(2 : ℝ) / 3) < 0 := by norm_num
    exact mul_neg_of_neg_of_pos hcoef_neg hV0ImPos
  linarith

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

/-- Invariant forwardizability is equivalent to having light-cone witnesses for
both the original and swap-sign invariant tuples. -/
theorem d1N2InvariantForwardizableSwap_iff_lightConeWitness_pair
    {q0 q1 p s : ℂ} :
    d1N2InvariantForwardizableSwap q0 q1 p s ↔
      d1N2InvariantLightConeWitness q0 q1 p s ∧
      d1N2InvariantLightConeWitness q1 q0 p (-s) := by
  constructor
  · intro hfw
    rcases (d1N2InvariantForwardizableSwap_iff_realizable_pair
      (q0 := q0) (q1 := q1) (p := p) (s := s)).1 hfw with ⟨hreal, hswapReal⟩
    refine ⟨?_, ?_⟩
    · exact (d1N2InvariantRealizable_iff_lightConeWitness q0 q1 p s).1 hreal
    · exact (d1N2InvariantRealizable_iff_lightConeWitness q1 q0 p (-s)).1 hswapReal
  · intro hLC
    rcases hLC with ⟨hLC, hswapLC⟩
    refine (d1N2InvariantForwardizableSwap_iff_realizable_pair
      (q0 := q0) (q1 := q1) (p := p) (s := s)).2 ?_
    refine ⟨?_, ?_⟩
    · exact (d1N2InvariantRealizable_iff_lightConeWitness q0 q1 p s).2 hLC
    · exact (d1N2InvariantRealizable_iff_lightConeWitness q1 q0 p (-s)).2 hswapLC

/-- Invariant-level paired witness condition (`d=1,n=2`):
both the original and swap-sign tuples admit forward light-cone witnesses. -/
def d1N2InvariantSectionWitnessPair (q0 q1 p s : ℂ) : Prop :=
  d1N2InvariantLightConeWitness q0 q1 p s ∧
    d1N2InvariantLightConeWitness q1 q0 p (-s)

/-- Forwardizability is equivalent to paired light-cone witness existence on the
original and swap-sign invariant tuples. -/
theorem d1N2InvariantForwardizableSwap_iff_sectionWitness_pair
    {q0 q1 p s : ℂ} :
    d1N2InvariantForwardizableSwap q0 q1 p s ↔
      d1N2InvariantSectionWitnessPair q0 q1 p s := by
  simpa [d1N2InvariantSectionWitnessPair] using
    (d1N2InvariantForwardizableSwap_iff_lightConeWitness_pair
      (q0 := q0) (q1 := q1) (p := p) (s := s))

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

/-- The `d=1,n=2` forwardizable-swap invariant locus is nonempty. -/
theorem d1N2InvariantForwardizableSwap_nonempty :
    ∃ q0 q1 p s : ℂ,
      s ^ 2 = 4 * (p ^ 2 - q0 * q1) ∧
      d1N2InvariantForwardizableSwap q0 q1 p s := by
  rcases d1N2InvariantRealizable_pair_nonempty with
    ⟨q0, q1, p, s, hrel, hreal, hswapReal⟩
  exact ⟨q0, q1, p, s, hrel,
    d1N2InvariantForwardizable_of_realizable_pair hreal hswapReal⟩

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

/-- Light-cone-witness diff-zero and forwardizable diff-zero are equivalent
formulations of the same `d=1,n=2` invariant-kernel condition. -/
theorem d1N2InvariantKernelDiffZeroOnLightConeWitness_iff_forwardizableDiffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) :
    (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantLightConeWitness q0 q1 p s →
      d1N2InvariantLightConeWitness q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0) ↔
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  constructor
  · intro hLC q0 q1 p s hrel hfw
    rcases (d1N2InvariantForwardizableSwap_iff_lightConeWitness_pair
      (q0 := q0) (q1 := q1) (p := p) (s := s)).1 hfw with ⟨hLC0, hLCswap⟩
    exact hLC q0 q1 p s hrel hLC0 hLCswap
  · intro hfw q0 q1 p s hrel hLC0 hLCswap
    have hfw' :
        d1N2InvariantForwardizableSwap q0 q1 p s :=
      (d1N2InvariantForwardizableSwap_iff_lightConeWitness_pair
        (q0 := q0) (q1 := q1) (p := p) (s := s)).2 ⟨hLC0, hLCswap⟩
    exact hfw q0 q1 p s hrel hfw'

/-- Section-witness reformulation of forwardizable invariant-kernel diff-zero:
one may quantify over explicit original/swapped section representatives instead
of the abstract forwardizable predicate. -/
theorem d1N2InvariantKernelDiffZeroOnForwardizableQuadric_iff_sectionWitnessDiffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f ↔
      (∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        d1N2InvariantSectionWitnessPair q0 q1 p s →
        f q0 q1 p s - f q1 q0 p (-s) = 0) := by
  constructor
  · intro hfw q0 q1 p s hquad hsecPair
    have hforw :
        d1N2InvariantForwardizableSwap q0 q1 p s :=
      (d1N2InvariantForwardizableSwap_iff_sectionWitness_pair
        (q0 := q0) (q1 := q1) (p := p) (s := s)).2 hsecPair
    exact hfw q0 q1 p s hquad hforw
  · intro hsec q0 q1 p s hquad hforw
    exact hsec q0 q1 p s hquad
      ((d1N2InvariantForwardizableSwap_iff_sectionWitness_pair
        (q0 := q0) (q1 := q1) (p := p) (s := s)).1 hforw)

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

/-- Variable-chart anchor hypothesis (`d=1,n=2`):
for each doubly-witnessed invariant tuple on the quadric, all paired original/
swapped variable-section representatives lying in `FT_{1,2}` have equal source
field values. -/
def d1N2PairedChartAnchorConnected
    (F : D1N2Config → ℂ) : Prop :=
  ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
    d1N2InvariantSectionWitnessPair q0 q1 p s →
    ∀ v0 w0,
      d1N2SectionOrig q0 q1 p s v0 ∈ ForwardTube 1 2 →
      d1N2SectionSwap q0 q1 p s w0 ∈ ForwardTube 1 2 →
      F (d1N2SectionSwap q0 q1 p s w0) = F (d1N2SectionOrig q0 q1 p s v0)

/-- Conditional `d=1,n=2` closure from the variable-chart anchor hypothesis:
source package + paired-chart anchor connectivity imply light-cone witness
swap-difference vanishing for the invariant kernel. -/
theorem d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_of_pairedChartAnchorConnected
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hanchor : d1N2PairedChartAnchorConnected (Classical.choose hsource)) :
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantLightConeWitness q0 q1 p s →
      d1N2InvariantLightConeWitness q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0 := by
  intro q0 q1 p s hquad hLC hswapLC
  rcases (d1N2InvariantLightConeWitness_iff_exists_forwardInvariants q0 q1 p s).1 hLC with
    ⟨z, hz, hq0, hq1, hp, hs⟩
  rcases (d1N2InvariantLightConeWitness_iff_exists_forwardInvariants q1 q0 p (-s)).1 hswapLC with
    ⟨y, hy, hyq0, hyq1, hyp, hys⟩
  have hsecPair : d1N2InvariantSectionWitnessPair q0 q1 p s := ⟨hLC, hswapLC⟩
  have hquadY : d1InvariantQuad y = (q1, q0, p, -s) := by
    simp [d1InvariantQuad, hyq0, hyq1, hyp, hys]
  have hzSecEq :
      d1N2SectionOrig q0 q1 p s (d1V0 z) = z := by
    have hzEq :
        d1N2SectionOrig (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) (d1V0 z) = z :=
      d1N2SectionOrig_eq_of_forward z hz
    simpa [hq0, hq1, hp, hs] using hzEq
  have hySecEq :
      d1N2SectionSwap q0 q1 p s (d1V0 y) = y := by
    exact d1N2SectionSwap_eq_of_forward_invariants
      (q0 := q0) (q1 := q1) (p := p) (s := s) y hy hquadY
  have hzSecFT :
      d1N2SectionOrig q0 q1 p s (d1V0 z) ∈ ForwardTube 1 2 := by
    simpa [hzSecEq] using hz
  have hySecFT :
      d1N2SectionSwap q0 q1 p s (d1V0 y) ∈ ForwardTube 1 2 := by
    simpa [hySecEq] using hy
  have hF_sections :
      (Classical.choose hsource) (d1N2SectionSwap q0 q1 p s (d1V0 y)) =
        (Classical.choose hsource) (d1N2SectionOrig q0 q1 p s (d1V0 z)) :=
    hanchor q0 q1 p s hquad hsecPair (d1V0 z) (d1V0 y) hzSecFT hySecFT
  have hF_yz :
      (Classical.choose hsource) y = (Classical.choose hsource) z := by
    calc
      (Classical.choose hsource) y
          = (Classical.choose hsource) (d1N2SectionSwap q0 q1 p s (d1V0 y)) := by
              simp [hySecEq]
      _ = (Classical.choose hsource) (d1N2SectionOrig q0 q1 p s (d1V0 z)) := hF_sections
      _ = (Classical.choose hsource) z := by
            simp [hzSecEq]
  have hf_onFT :
      ∀ z, z ∈ ForwardTube 1 2 →
        (Classical.choose hsource) z =
          f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) :=
    (Classical.choose_spec hsource).2.2.2.2
  have hFz :
      (Classical.choose hsource) z = f q0 q1 p s := by
    calc
      (Classical.choose hsource) z
          = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hf_onFT z hz
      _ = f q0 q1 p s := by simp [hq0, hq1, hp, hs]
  have hFy :
      (Classical.choose hsource) y = f q1 q0 p (-s) := by
    calc
      (Classical.choose hsource) y
          = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hf_onFT y hy
      _ = f q1 q0 p (-s) := by simp [hyq0, hyq1, hyp, hys]
  apply sub_eq_zero.mpr
  calc
    f q0 q1 p s = (Classical.choose hsource) z := hFz.symm
    _ = (Classical.choose hsource) y := hF_yz.symm
    _ = f q1 q0 p (-s) := hFy

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

/-- In `d=1,n=2`, the EOW real-witness package is inconsistent:
no real configuration can satisfy both `x ∈ ET` and `swap·x ∈ ET` together with
the adjacent spacelike condition. -/
theorem d1N2ForwardSwapEOWGeometryPackage_false :
    ¬ d1N2ForwardSwapEOWGeometryPackage := by
  intro hgeom
  rcases hgeom with ⟨_hconn, x0, hx0_sp, hx0_ET, hx0_swapET⟩
  exact d1N2_no_real_adjacent_spacelike_witness_swap ⟨x0, hx0_sp, hx0_ET, hx0_swapET⟩

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
