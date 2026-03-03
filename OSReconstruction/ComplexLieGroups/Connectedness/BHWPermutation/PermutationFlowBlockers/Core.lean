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
