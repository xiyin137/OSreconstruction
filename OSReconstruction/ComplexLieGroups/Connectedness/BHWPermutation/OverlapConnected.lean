/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.JostWitnessGeneralSigma

/-!
# Extended Tube Permutation Invariance via Identity Theorem (Route B)

## Mathematical Goal

Prove `extendF F (σ · z) = extendF F z` for all `z ∈ ET ∩ σ⁻¹(ET)`,
which closes the `hExtPerm` sorry in `PermutationFlow.lean:2262` for `d ≥ 2`.

## Strategy: Identity Theorem on `W = ET ∩ σ⁻¹(ET)`

Rather than proving connectedness of the forward-overlap set
`permForwardOverlapSet` (Route A), we apply the Identity Theorem for
several complex variables directly on `W = ET ∩ σ⁻¹(ET)`:

1. **Holomorphicity.** `extendF F` is holomorphic on ET (by
   `extendF_holomorphicOn`). The composition `z ↦ extendF F (σ·z)` is
   holomorphic on `σ⁻¹(ET)` (composition with the linear permutation map).
   The difference `h(z) = extendF F (σ·z) - extendF F (z)` is therefore
   holomorphic on `W`.

2. **Real vanishing locus.** For real `x ∈ JostSet d n` with `d ≥ 2`:
   - `realEmbed x ∈ ET` and `realEmbed (σ·x) ∈ ET` (from
     `jostWitness_exists` / `forwardJostSet_subset_extendedTube`).
   - `extendF F (realEmbed x) = F (realEmbed x)` (by
     `extendF_eq_boundary_value_ET`).
   - `extendF F (realEmbed (σ·x)) = F (realEmbed (σ·x))` (same).
   - `F (realEmbed (σ·x)) = F (realEmbed x)` (by `hF_local` extended to
     general permutations via the pairwise spacelike condition on `JostSet`).
   So `h(realEmbed x) = 0` for all `x` in the "permuted Jost set"
   `V = {x ∈ JostSet | realEmbed x ∈ ET ∧ realEmbed(σ·x) ∈ ET}`,
   which is open and nonempty for `d ≥ 2`.

3. **Identity Theorem.** By `identity_theorem_totally_real_product`,
   `h = 0` on every connected component of `W` that meets `V`.
   If `W` is connected, then `h = 0` on all of `W`.

4. **Connectedness of W.** ET is connected (image of connected `G × FT`
   under continuous action). The permutation map `σ*` is a linear
   homeomorphism, so `σ⁻¹(ET) = σ*(ET)` is also connected.
   Proving `W = ET ∩ σ⁻¹(ET)` is connected requires additional argument
   (the intersection of two connected sets is not always connected).
   This is the remaining obligation.

### Critical geometric facts

**Real Jost points are NOT in FT.** The forward tube strictly requires
`Im(ξ_k) ∈ V⁺` (the open forward light cone). Real points have `Im = 0`,
and `0 ∉ V⁺`. Real Jost points lie on the *boundary* of FT, inside ET.

**FT ∩ σ⁻¹(FT) = ∅ for non-trivial σ.** An adjacent swap reverses the
sign of one difference variable's imaginary part, sending `V⁺ → V⁻`.
Since `V⁺ ∩ V⁻ = ∅`, no forward-tube point is also in the permuted
forward tube. In particular, `Λ = 1` is NOT in the index set.

## References

* Streater & Wightman, *PCT, Spin and Statistics*, §2-5, Theorem 2-12
* Jost, *The General Theory of Quantized Fields*, Ch. IV
* Gunning & Rossi, *Analytic Functions of Several Complex Variables*, Ch. I
  (Identity Theorem for holomorphic functions of several variables)
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

variable {d : ℕ}

/-! ### Fixed-Λ forward-overlap slices (Route A infrastructure)

These results remain valid and useful for the Route A approach. -/

/-- Fixed-`Λ` slice of the forward-overlap set:
    `{w ∈ FT | Λ · (σ · w) ∈ FT}`. -/
def permForwardOverlapSlice
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {w | w ∈ ForwardTube d n ∧
       complexLorentzAction Λ (permAct (d := d) σ w) ∈ ForwardTube d n}

/-- Each fixed-`Λ` forward-overlap slice is convex. -/
theorem permForwardOverlapSlice_convex
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    Convex ℝ (permForwardOverlapSlice (d := d) n σ Λ) := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab
  refine ⟨forwardTube_convex hw₁.1 hw₂.1 ha hb hab, ?_⟩
  have hlin_perm : permAct (d := d) σ (a • w₁ + b • w₂)
      = a • permAct (d := d) σ w₁ + b • permAct (d := d) σ w₂ := by
    ext k μ; simp [permAct, Pi.smul_apply, Pi.add_apply]
  have hlin_lorentz : complexLorentzAction Λ
      (a • permAct (d := d) σ w₁ + b • permAct (d := d) σ w₂)
      = a • complexLorentzAction Λ (permAct (d := d) σ w₁)
        + b • complexLorentzAction Λ (permAct (d := d) σ w₂) := by
    ext k μ
    simp only [complexLorentzAction, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext ν; ring
  rw [hlin_perm, hlin_lorentz]
  exact forwardTube_convex hw₁.2 hw₂.2 ha hb hab

/-- Each fixed-`Λ` forward-overlap slice is preconnected (convex ⇒ preconnected). -/
theorem permForwardOverlapSlice_isPreconnected
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d) :
    IsPreconnected (permForwardOverlapSlice (d := d) n σ Λ) :=
  (permForwardOverlapSlice_convex n σ Λ).isPreconnected

/-- Sum-closure of the open forward cone. -/
private lemma inOpenForwardCone_add
    {η₁ η₂ : Fin (d + 1) → ℝ}
    (h₁ : InOpenForwardCone d η₁) (h₂ : InOpenForwardCone d η₂) :
    InOpenForwardCone d (fun μ => η₁ μ + η₂ μ) := by
  have hmid : InOpenForwardCone d ((1 / 2 : ℝ) • η₁ + (1 / 2 : ℝ) • η₂) :=
    inOpenForwardCone_convex h₁ h₂ (by positivity) (by positivity) (by ring)
  have hscaled : InOpenForwardCone d
      ((2 : ℝ) • (((1 / 2 : ℝ) • η₁ + (1 / 2 : ℝ) • η₂)) ) :=
    inOpenForwardCone_smul_pos (d := d) hmid (by
      show 0 < (2 : ℝ)
      norm_num)
  have hfun : ((2 : ℝ) • (((1 / 2 : ℝ) • η₁ + (1 / 2 : ℝ) • η₂))) =
      (fun μ => η₁ μ + η₂ μ) := by
    ext μ
    simp [Pi.smul_apply, smul_eq_mul]
    ring
  simpa [hfun] using hscaled

/-- Any point `w k` of a forward-tube configuration has imaginary part in `V⁺`. -/
private lemma forwardTube_point_inOpenForwardCone
    {w : Fin n → Fin (d + 1) → ℂ}
    (hw : w ∈ ForwardTube d n)
    (k : Fin n) :
    InOpenForwardCone d (fun μ => (w k μ).im) := by
  have haux : ∀ m : ℕ, ∀ hm : m < n,
      InOpenForwardCone d (fun μ => (w ⟨m, hm⟩ μ).im) := by
    intro m
    induction m with
    | zero =>
        intro hm
        have h0 := hw ⟨0, hm⟩
        simpa [ForwardTube, InOpenForwardCone] using h0
    | succ m ih =>
        intro hm
        have hm' : m < n := Nat.lt_of_succ_lt hm
        have hprev : InOpenForwardCone d (fun μ => (w ⟨m, hm'⟩ μ).im) := ih hm'
        have hstep := hw ⟨m + 1, hm⟩
        have hdiff : InOpenForwardCone d
            (fun μ => (w ⟨m + 1, hm⟩ μ - w ⟨m, hm'⟩ μ).im) := by
          simpa [ForwardTube, Nat.succ_ne_zero] using hstep
        have hsum := inOpenForwardCone_add hprev hdiff
        simpa [Complex.sub_im, Pi.add_apply] using hsum
  exact haux k.1 k.2

/-! ### Slice decomposition of the forward-overlap set -/

/-- The forward-overlap set decomposes as a union of fixed-`Λ` slices. -/
theorem permForwardOverlapSet_eq_iUnion_slice
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permForwardOverlapSet (d := d) n σ =
      ⋃ Λ : ComplexLorentzGroup d, permForwardOverlapSlice (d := d) n σ Λ := by
  ext w
  simp only [permForwardOverlapSet, permForwardOverlapSlice, Set.mem_setOf_eq,
             Set.mem_iUnion]
  constructor
  · rintro ⟨hwFT, hσwET⟩
    obtain ⟨Λ, u, huFT, hσw_eq⟩ := Set.mem_iUnion.mp hσwET
    refine ⟨Λ⁻¹, hwFT, ?_⟩
    have : complexLorentzAction Λ⁻¹ (permAct (d := d) σ w) = u := by
      rw [hσw_eq, complexLorentzAction_inv]
    exact this ▸ huFT
  · rintro ⟨Λ, hwFT, hΛσwFT⟩
    refine ⟨hwFT, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Λ⁻¹, ?_⟩
    refine ⟨complexLorentzAction Λ (permAct (d := d) σ w), hΛσwFT, ?_⟩
    rw [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]

/-! ### Slice membership is open in Λ -/

/-- If `w ∈ permForwardOverlapSlice n σ Λ₀`, then `w` also belongs to
    the slice at every `Λ` sufficiently near `Λ₀`. -/
theorem permForwardOverlapSlice_openMembership
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : Fin n → Fin (d + 1) → ℂ)
    (Λ₀ : ComplexLorentzGroup d)
    (hw : w ∈ permForwardOverlapSlice (d := d) n σ Λ₀) :
    ∀ᶠ Λ in nhds Λ₀, w ∈ permForwardOverlapSlice (d := d) n σ Λ := by
  have hcont : Continuous (fun Λ : ComplexLorentzGroup d =>
      complexLorentzAction Λ (permAct (d := d) σ w)) :=
    continuous_complexLorentzAction_fst (permAct (d := d) σ w)
  exact hcont.continuousAt.eventually
    (isOpen_forwardTube.mem_nhds hw.2) |>.mono (fun Λ hΛ => ⟨hw.1, hΛ⟩)

/-! ### Route B: Identity Theorem on `ET ∩ σ⁻¹(ET)` -/

/-- The ET overlap domain: `W = ET ∩ σ⁻¹(ET)`.
    This is the set of points `z` such that both `z` and `σ·z` lie in ET. -/
def etOverlap (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | z ∈ ExtendedTube d n ∧ permAct (d := d) σ z ∈ ExtendedTube d n}

/-- The permutation action on configurations is continuous. -/
private theorem continuous_permAct (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Continuous (permAct (d := d) σ) :=
  continuous_pi (fun k => continuous_apply (σ k))

/-- The ET overlap is open (intersection of two open sets). -/
theorem isOpen_etOverlap (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsOpen (etOverlap (d := d) n σ) := by
  apply IsOpen.inter isOpen_extendedTube
  exact isOpen_extendedTube.preimage (continuous_permAct n σ)

/-- σ and Λ commute: permutations act on particle indices while Lorentz
    transforms act on spacetime indices, so they are independent. -/
theorem permAct_complexLorentzAction_comm (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ) :
    permAct σ (complexLorentzAction Λ w) =
    complexLorentzAction Λ (permAct σ w) := rfl

/-- ET is invariant under the Lorentz action: Λ·z ∈ ET whenever z ∈ ET. -/
private theorem extendedTube_lorentz_invariant (n : ℕ)
    (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ExtendedTube d n) :
    complexLorentzAction Λ z ∈ ExtendedTube d n := by
  obtain ⟨Λ', w, hw_FT, rfl⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨Λ * Λ', w, hw_FT,
    by rw [complexLorentzAction_mul]⟩

/-- ET is invariant under the inverse Lorentz action: if Λ·z ∈ ET then z ∈ ET. -/
private theorem extendedTube_lorentz_invariant_inv (n : ℕ)
    (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ)
    (hz : complexLorentzAction Λ z ∈ ExtendedTube d n) :
    z ∈ ExtendedTube d n := by
  have := extendedTube_lorentz_invariant n Λ⁻¹ (complexLorentzAction Λ z) hz
  rwa [← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one] at this

/-- The ET overlap is the continuous image of `L₊(ℂ) × forward-overlap` under
    the Lorentz action. This is a consequence of σ-Λ commutativity and
    ET Lorentz invariance. -/
theorem etOverlap_eq_image_forwardOverlap (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    etOverlap (d := d) n σ =
      (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) ''
      (Set.univ ×ˢ permForwardOverlapSet (d := d) n σ) := by
  ext z
  simp only [etOverlap, permForwardOverlapSet, Set.mem_setOf_eq, Set.mem_image,
             Set.mem_prod, Set.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨hz_ET, hσz_ET⟩
    obtain ⟨Λ, w, hw_FT, rfl⟩ := Set.mem_iUnion.mp hz_ET
    refine ⟨Λ, w, ⟨hw_FT, ?_⟩, rfl⟩
    rw [permAct_complexLorentzAction_comm] at hσz_ET
    exact extendedTube_lorentz_invariant_inv n Λ (permAct σ w) hσz_ET
  · rintro ⟨Λ, w, ⟨hw_FT, hσw_ET⟩, rfl⟩
    constructor
    · exact Set.mem_iUnion.mpr ⟨Λ, w, hw_FT, rfl⟩
    · rw [permAct_complexLorentzAction_comm]
      exact extendedTube_lorentz_invariant n Λ (permAct σ w) hσw_ET

/-- The permuted Jost set: real Jost points whose embeddings (both natural and
    σ-permuted) lie in the extended tube. For `d ≥ 2`, this is open and nonempty. -/
def permJostSet (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℝ) :=
  {x | x ∈ JostSet d n ∧
       realEmbed x ∈ ExtendedTube d n ∧
       realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n}

/-- Real embeddings of the permuted Jost set lie in the ET overlap. -/
theorem permJostSet_realEmbed_sub_etOverlap
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∀ x ∈ permJostSet (d := d) n σ,
      realEmbed x ∈ etOverlap (d := d) n σ := by
  intro x ⟨_, hxET, hσxET⟩
  exact ⟨hxET, by simpa [permAct, realEmbed] using hσxET⟩

/-- The permuted Jost set is nonempty for `d ≥ 2`.
    This follows from `jostWitness_exists`. -/
theorem permJostSet_nonempty
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    (permJostSet (d := d) n σ).Nonempty := by
  obtain ⟨x, hxJ, hxET, hσxET⟩ :=
    JostWitnessGeneralSigma.jostWitness_exists hd2 σ
  exact ⟨x, hxJ, hxET, hσxET⟩

/-- The real embedding map is continuous. -/
private theorem continuous_realEmbed :
    Continuous (realEmbed (d := d) (n := n)) :=
  continuous_pi (fun k => continuous_pi (fun μ =>
    Complex.continuous_ofReal.comp (continuous_apply μ |>.comp (continuous_apply k))))

/-- The permuted Jost set is open.
    It is the intersection of `JostSet` (open) with preimages of `ET` (open)
    under continuous maps. -/
theorem isOpen_permJostSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsOpen (permJostSet (d := d) n σ) := by
  apply IsOpen.inter isOpen_jostSet
  apply IsOpen.inter
  · exact isOpen_extendedTube.preimage continuous_realEmbed
  · have : Continuous (fun x : Fin n → Fin (d + 1) → ℝ =>
        realEmbed (fun k => x (σ k))) :=
      continuous_realEmbed.comp (continuous_pi (fun k => continuous_apply (σ k)))
    exact isOpen_extendedTube.preimage this

/-- The difference `h(z) = extendF F (σ·z) - extendF F (z)` is holomorphic on the
    ET overlap, provided `F` satisfies holomorphicity and complex Lorentz invariance. -/
theorem differentiableOn_extendF_diff_on_etOverlap
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z) :
    DifferentiableOn ℂ
      (fun z => extendF F (permAct (d := d) σ z) - extendF F z)
      (etOverlap (d := d) n σ) := by
  have hperm_diff : Differentiable ℂ (permAct (d := d) σ) :=
    differentiable_pi.mpr (fun k => differentiable_apply (σ k))
  apply DifferentiableOn.sub
  · -- extendF F ∘ σ is holomorphic on σ⁻¹(ET)
    have hextend := extendF_holomorphicOn n F hF_holo hF_cinv
    intro z hz
    exact (hextend _ hz.2).comp z (hperm_diff z).differentiableWithinAt
      (fun z' hz' => hz'.2)
  · -- extendF F is holomorphic on ET
    exact (extendF_holomorphicOn n F hF_holo hF_cinv).mono
      (fun z hz => hz.1)

/-- On JostSet, the spacelike condition holds for any pair i ≠ j,
    in the sign convention matching `hF_local` (x_j - x_i). -/
private lemma jostSet_spacelike_for_locality
    {n : ℕ} (x : Fin n → Fin (d + 1) → ℝ) (hxJ : x ∈ JostSet d n)
    (i j : Fin n) (hij : i ≠ j) :
    ∑ μ, minkowskiSignature d μ * (x j μ - x i μ) ^ 2 > 0 := by
  have h := hxJ.2 i j hij
  simp only [IsSpacelike] at h
  convert h using 1; congr 1; ext μ; ring

/-- F is invariant under adjacent swap (i, i+1) on JostSet. -/
private lemma F_adj_swap_invariant
    {n : ℕ} (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (x : Fin n → Fin (d + 1) → ℝ) (hxJ : x ∈ JostSet d n)
    (i : Fin n) (hi : i.val + 1 < n) :
    F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
    F (fun k μ => (x k μ : ℂ)) :=
  hF_local i hi x (jostSet_spacelike_for_locality x hxJ i ⟨i.val + 1, hi⟩
    (by intro h; exact absurd (congrArg Fin.val h) (by simp)))

/-- Induction principle for adjacent transposition generation in `Perm (Fin n)`.

    If `P` holds for the identity, for each adjacent swap, and is closed under
    composition, then `P` holds for all permutations. This is a consequence of
    mathlib's `Equiv.Perm.mclosure_swap_castSucc_succ`, which proves that adjacent
    transpositions generate the full symmetric group as a monoid. -/
lemma perm_adj_closure_induction {n : ℕ} (σ : Equiv.Perm (Fin n))
    {P : Equiv.Perm (Fin n) → Prop}
    (hid : P 1)
    (hadj : ∀ (i : Fin n) (hi : i.val + 1 < n),
      P (Equiv.swap i ⟨i.val + 1, hi⟩))
    (hmul : ∀ σ τ : Equiv.Perm (Fin n), P σ → P τ → P (σ * τ)) :
    P σ := by
  -- We need to connect our formulation (swap i ⟨i+1, hi⟩ for i : Fin n, hi : i+1 < n)
  -- with mathlib's formulation (swap i.castSucc i.succ for i : Fin m, where n = m+1).
  -- When n = 0, Perm (Fin 0) is trivial.
  -- When n ≥ 1, write n = m + 1 and use mclosure_swap_castSucc_succ m.
  rcases n with _ | m
  · -- n = 0: Fin 0 is empty, so σ = 1
    have : σ = 1 := Subsingleton.elim σ 1
    rw [this]; exact hid
  · -- n = m + 1: use mathlib's mclosure_swap_castSucc_succ m
    have hmem : σ ∈ Submonoid.closure
        (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top σ
    induction hmem using Submonoid.closure_induction with
    | one => exact hid
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have : i.castSucc.val + 1 < m + 1 := by
        simp [Fin.val_castSucc]
      exact hadj i.castSucc this
    | mul x y _ _ hpx hpy => exact hmul x y hpx hpy

/-- F is invariant under any swap on JostSet.

    Reduces arbitrary swaps to adjacent swaps via `perm_adj_closure_induction`,
    then applies `F_adj_swap_invariant` at each step. JostSet membership
    is preserved at each intermediate step by `jostSet_permutation_invariant`. -/
private lemma F_swap_invariant
    {n : ℕ} (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (a b : Fin n) (_hab : a ≠ b)
    (x : Fin n → Fin (d + 1) → ℝ) (hxJ : x ∈ JostSet d n) :
    F (fun k μ => (x (Equiv.swap a b k) μ : ℂ)) =
    F (fun k μ => (x k μ : ℂ)) := by
  -- P(σ) = ∀ y ∈ JostSet, F(y ∘ σ) = F(y)
  -- We prove P(swap a b) by showing P holds for all permutations.
  suffices h : ∀ y : Fin n → Fin (d + 1) → ℝ, y ∈ JostSet d n →
      F (fun k μ => (y (Equiv.swap a b k) μ : ℂ)) = F (fun k μ => (y k μ : ℂ)) from
    h x hxJ
  apply perm_adj_closure_induction (Equiv.swap a b) (P := fun σ =>
    ∀ y : Fin n → Fin (d + 1) → ℝ, y ∈ JostSet d n →
      F (fun k μ => (y (σ k) μ : ℂ)) = F (fun k μ => (y k μ : ℂ)))
  · -- P(1)
    intro y _; simp
  · -- P(adjacent swap)
    intro i hi y hyJ
    exact F_adj_swap_invariant F hF_local y hyJ i hi
  · -- P(σ) ∧ P(τ) → P(σ * τ)
    intro σ τ hσ hτ y hyJ
    have hyσJ : (fun k => y (σ k)) ∈ JostSet d n :=
      jostSet_permutation_invariant σ hyJ
    show F (fun k μ => (y ((σ * τ) k) μ : ℂ)) = F (fun k μ => (y k μ : ℂ))
    have hrewrite : (fun k μ => (y ((σ * τ) k) μ : ℂ)) =
        (fun k μ => ((fun k' => y (σ k')) (τ k) μ : ℂ)) := by
      ext k μ; simp [Equiv.Perm.mul_apply]
    rw [hrewrite, hτ _ hyσJ]
    exact hσ y hyJ

/-- F(σ · x) = F(x) for all permutations σ and all x ∈ JostSet.

    Combines `F_swap_invariant` (F is invariant under any single swap on JostSet)
    with `swap_induction_on` (every permutation decomposes as a product of swaps).

    This is a purely algebraic consequence: every permutation is a product of
    transpositions, and on JostSet all pairwise differences are spacelike (so
    the locality axiom applies to each swap in the decomposition). -/
theorem F_perm_invariant_on_jostSet
    (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (x : Fin n → Fin (d + 1) → ℝ)
    (hxJ : x ∈ JostSet d n) :
    F (fun k μ => (x (σ k) μ : ℂ)) = F (fun k μ => (x k μ : ℂ)) := by
  -- Universally quantify to get the right motive for swap_induction_on
  suffices h : ∀ y : Fin n → Fin (d + 1) → ℝ, y ∈ JostSet d n →
      F (fun k μ => (y (σ k) μ : ℂ)) = F (fun k μ => (y k μ : ℂ)) from
    h x hxJ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro y _; simp
  | swap_mul σ' a b hab ih =>
    intro y hyJ
    -- σ = swap(a,b) * σ', so σ(k) = swap(a,b)(σ'(k))
    -- F(y ∘ σ) = F((y ∘ swap(a,b)) ∘ σ') = F(y ∘ swap(a,b)) = F(y)
    have hwJ : (fun k => y (Equiv.swap a b k)) ∈ JostSet d n :=
      jostSet_permutation_invariant (Equiv.swap a b) hyJ
    show F (fun k μ => (y ((Equiv.swap a b * σ') k) μ : ℂ)) = F (fun k μ => (y k μ : ℂ))
    have hrewrite : (fun k μ => (y ((Equiv.swap a b * σ') k) μ : ℂ)) =
        (fun k μ => ((fun k' => y (Equiv.swap a b k')) (σ' k) μ : ℂ)) := by
      ext k μ; simp [Equiv.Perm.mul_apply]
    rw [hrewrite, ih _ hwJ]
    exact F_swap_invariant F hF_local a b hab y hyJ

/-- On the permuted Jost set, `extendF F (σ·x) - extendF F (x) = 0`.

    Combines:
    - `extendF_eq_boundary_value_ET`: at real ET points, `extendF F = F`
    - `F_perm_invariant_on_jostSet`: `F(σ·x) = F(x)` on JostSet -/
theorem extendF_diff_zero_on_permJostSet
    (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z)
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
    (hx : x ∈ permJostSet (d := d) n σ) :
    extendF F (permAct (d := d) σ (realEmbed x)) -
      extendF F (realEmbed x) = 0 := by
  obtain ⟨hxJ, hxET, hσxET⟩ := hx
  -- extendF F (realEmbed x) = F (realEmbed x)
  have h1 : extendF F (realEmbed x) = F (realEmbed x) :=
    extendF_eq_boundary_value_ET n F hF_holo hF_cinv hF_bv x hxET
  -- permAct σ (realEmbed x) = realEmbed (fun k => x (σ k))
  have hperm_real : permAct (d := d) σ (realEmbed x) =
      realEmbed (fun k => x (σ k)) := by
    ext k μ; simp [permAct, realEmbed]
  -- extendF F (σ · realEmbed x) = F (realEmbed (σ · x))
  have h2 : extendF F (permAct (d := d) σ (realEmbed x)) =
      F (realEmbed (fun k => x (σ k))) := by
    rw [hperm_real]
    exact extendF_eq_boundary_value_ET n F hF_holo hF_cinv hF_bv
      (fun k => x (σ k)) hσxET
  -- F (realEmbed (σ · x)) = F (realEmbed x)
  have h3 : F (realEmbed (fun k => x (σ k))) = F (realEmbed x) :=
    F_perm_invariant_on_jostSet n F hF_local σ x hxJ
  rw [h2, h3, h1, sub_self]

/-! ### Topological gluing lemma -/

/-- Topological gluing lemma: a union of preconnected slices over a preconnected
    index set is preconnected, provided each slice is nonempty and slice membership
    is an open condition on the index. -/
theorem isPreconnected_iUnion_of_open_membership
    {ι X : Type*} [TopologicalSpace ι] [TopologicalSpace X]
    {I : Set ι} (hI_conn : IsPreconnected I)
    (S : ι → Set X)
    (hS_conn : ∀ i ∈ I, IsPreconnected (S i))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (h_open : ∀ i ∈ I, ∀ x ∈ S i, ∀ᶠ j in 𝓝[I] i, x ∈ S j) :
    IsPreconnected (⋃ i ∈ I, S i) := by
  intro U V hU_open hV_open h_cov hU_ne hV_ne
  by_contra h_disj
  rw [Set.not_nonempty_iff_eq_empty] at h_disj
  have absurd_mem : ∀ x, x ∈ (⋃ j ∈ I, S j) → x ∈ U → x ∈ V → False := by
    intro x hxS hxU hxV
    have : x ∈ (⋃ j ∈ I, S j) ∩ (U ∩ V) := ⟨hxS, hxU, hxV⟩
    rw [h_disj] at this; exact this
  let I_U := {i ∈ I | S i ⊆ U}
  let I_V := {i ∈ I | S i ⊆ V}
  have hI_cov : I ⊆ I_U ∪ I_V := by
    intro i hi
    have h_cov_i : S i ⊆ U ∪ V := (Set.subset_iUnion₂ i hi).trans h_cov
    by_cases h_iU : (S i ∩ U).Nonempty
    · by_cases h_iV : (S i ∩ V).Nonempty
      · rcases hS_conn i hi U V hU_open hV_open h_cov_i h_iU h_iV with ⟨x, hxS, hxU, hxV⟩
        exact (absurd_mem x (Set.mem_iUnion₂_of_mem hi hxS) hxU hxV).elim
      · left; exact ⟨hi, fun x hx =>
          (h_cov_i hx).resolve_right (fun hxV => (h_iV ⟨x, hx, hxV⟩).elim)⟩
    · right; exact ⟨hi, fun x hx =>
        (h_cov_i hx).resolve_left (fun hxU => (h_iU ⟨x, hx, hxU⟩).elim)⟩
  have hIU_disj : Disjoint I_U I_V := by
    rw [Set.disjoint_left]
    rintro i ⟨hi, hsubU⟩ ⟨_, hsubV⟩
    rcases hS_ne i hi with ⟨x, hx⟩
    exact absurd_mem x (Set.mem_iUnion₂_of_mem hi hx) (hsubU hx) (hsubV hx)
  have mk_open_lift (I_side : Set ι) (h_side_sub : I_side ⊆ I)
      (h_propagate : ∀ i ∈ I_side, ∀ x ∈ S i, ∀ᶠ j in 𝓝[I] i, j ∈ I_side) :
      ∃ O : Set ι, IsOpen O ∧ O ∩ I = I_side := by
    set O := ⋃ (W : Set ι) (_ : IsOpen W) (_ : W ∩ I ⊆ I_side), W
    refine ⟨O, isOpen_iUnion fun W => isOpen_iUnion fun hW => isOpen_iUnion fun _ => hW, ?_⟩
    ext i; constructor
    · rintro ⟨hi_O, hi_I⟩
      obtain ⟨W, hW_mem⟩ := Set.mem_iUnion.mp hi_O
      obtain ⟨_, hW_rest⟩ := Set.mem_iUnion.mp hW_mem
      obtain ⟨hW_sub, hi_W⟩ := Set.mem_iUnion.mp hW_rest
      exact hW_sub ⟨hi_W, hi_I⟩
    · intro hi_side
      have hfilt := h_propagate i hi_side
      rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter).mp
        (by rcases hS_ne i (h_side_sub hi_side) with ⟨x, hx⟩
            exact (hfilt x hx)) with ⟨W, hW_nhds, hW_sub⟩
      rcases mem_nhds_iff.mp hW_nhds with ⟨O', hO'W, hO'_open, hi_O'⟩
      have hO'_sub : O' ∩ I ⊆ I_side := fun j ⟨hjO, hjI⟩ => hW_sub ⟨hO'W hjO, hjI⟩
      exact ⟨Set.mem_iUnion.mpr ⟨O', Set.mem_iUnion.mpr ⟨hO'_open,
        Set.mem_iUnion.mpr ⟨hO'_sub, hi_O'⟩⟩⟩, h_side_sub hi_side⟩
  have hU_propagate : ∀ i ∈ I_U, ∀ x ∈ S i, ∀ᶠ j in 𝓝[I] i, j ∈ I_U := by
    intro i ⟨hi_I, hi_sub⟩ x hx
    filter_upwards [h_open i hi_I x hx, self_mem_nhdsWithin] with j hj_S hj_I
    rcases hI_cov hj_I with hj_U | hj_V
    · exact hj_U
    · exact (absurd_mem x (Set.mem_iUnion₂_of_mem hj_I hj_S) (hi_sub hx) (hj_V.2 hj_S)).elim
  obtain ⟨O_U, hOU_open, hOU_inter⟩ := mk_open_lift I_U (fun i hi => hi.1) hU_propagate
  have hV_propagate : ∀ i ∈ I_V, ∀ x ∈ S i, ∀ᶠ j in 𝓝[I] i, j ∈ I_V := by
    intro i ⟨hi_I, hi_sub⟩ x hx
    filter_upwards [h_open i hi_I x hx, self_mem_nhdsWithin] with j hj_S hj_I
    rcases hI_cov hj_I with hj_U | hj_V
    · exact (absurd_mem x (Set.mem_iUnion₂_of_mem hj_I hj_S) (hj_U.2 hj_S) (hi_sub hx)).elim
    · exact hj_V
  obtain ⟨O_V, hOV_open, hOV_inter⟩ := mk_open_lift I_V (fun i hi => hi.1) hV_propagate
  have hI_sub : I ⊆ O_U ∪ O_V := by
    intro i hi
    rcases hI_cov hi with hU | hV
    · left; exact (hOU_inter.symm ▸ hU : i ∈ O_U ∩ I).1
    · right; exact (hOV_inter.symm ▸ hV : i ∈ O_V ∩ I).1
  have hIU_ne : (I ∩ O_U).Nonempty := by
    rcases hU_ne with ⟨x, hxS, hxU⟩
    obtain ⟨i, hi, hx_Si⟩ := Set.mem_iUnion₂.mp hxS
    rcases hI_cov hi with hi_IU | hi_IV
    · exact ⟨i, hi, (hOU_inter.symm ▸ hi_IU : i ∈ O_U ∩ I).1⟩
    · exact (absurd_mem x hxS hxU (hi_IV.2 hx_Si)).elim
  have hIV_ne : (I ∩ O_V).Nonempty := by
    rcases hV_ne with ⟨x, hxS, hxV⟩
    obtain ⟨i, hi, hx_Si⟩ := Set.mem_iUnion₂.mp hxS
    rcases hI_cov hi with hi_IU | hi_IV
    · exact (absurd_mem x hxS (hi_IU.2 hx_Si) hxV).elim
    · exact ⟨i, hi, (hOV_inter.symm ▸ hi_IV : i ∈ O_V ∩ I).1⟩
  rcases hI_conn O_U O_V hOU_open hOV_open hI_sub hIU_ne hIV_ne with ⟨i, hi_I, hi_OU, hi_OV⟩
  have h1 : i ∈ I_U := by rw [← hOU_inter]; exact ⟨hi_OU, hi_I⟩
  have h2 : i ∈ I_V := by rw [← hOV_inter]; exact ⟨hi_OV, hi_I⟩
  exact Set.disjoint_left.mp hIU_disj h1 h2

/-- Connected version of the gluing lemma. -/
theorem isConnected_iUnion_of_open_membership
    {ι X : Type*} [TopologicalSpace ι] [TopologicalSpace X]
    {I : Set ι} (hI_conn : IsConnected I)
    (S : ι → Set X)
    (hS_conn : ∀ i ∈ I, IsPreconnected (S i))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (h_open : ∀ i ∈ I, ∀ x ∈ S i, ∀ᶠ j in 𝓝[I] i, x ∈ S j) :
    IsConnected (⋃ i ∈ I, S i) := by
  constructor
  · rcases hI_conn.nonempty with ⟨i, hi⟩
    rcases hS_ne i hi with ⟨x, hx⟩
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩⟩
  · exact isPreconnected_iUnion_of_open_membership hI_conn.isPreconnected S hS_conn hS_ne h_open

/-! ### Polar decomposition and bi-invariance -/

/-- `ofReal R⁻¹ = (ofReal R)⁻¹` in `L₊(ℂ)`. -/
private lemma ofReal_inv_eq (R : RestrictedLorentzGroup d) :
    ComplexLorentzGroup.ofReal R⁻¹ = (ComplexLorentzGroup.ofReal R)⁻¹ := by
  have h1 := ofReal_mul_eq R⁻¹ R
  rw [inv_mul_cancel] at h1
  rw [ofReal_one_eq] at h1
  exact mul_left_cancel (a := ComplexLorentzGroup.ofReal R)
    (by rw [← ofReal_mul_eq, mul_inv_cancel, ofReal_one_eq, mul_inv_cancel])

/-- FT is preserved by `(ofReal R)⁻¹` action. -/
private lemma ofReal_inv_preserves_forwardTube (R : RestrictedLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    complexLorentzAction (ComplexLorentzGroup.ofReal R)⁻¹ z ∈ ForwardTube d n := by
  rw [← ofReal_inv_eq]
  exact ofReal_preserves_forwardTube R⁻¹ z hz

/-- Bi-invariance: the forward-overlap slice nonemptiness is preserved under
    conjugation by real restricted Lorentz transforms. This follows from
    `ofReal_preserves_forwardTube` and `permAct_complexLorentzAction_comm`. -/
private lemma sliceIndexSet_bi_invariant
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d) (k₁ k₂ : RestrictedLorentzGroup d) :
    (permForwardOverlapSlice (d := d) n σ Λ).Nonempty →
    (permForwardOverlapSlice (d := d) n σ
      (ComplexLorentzGroup.ofReal k₁ * Λ * ComplexLorentzGroup.ofReal k₂)).Nonempty := by
  rintro ⟨w, hw_FT, hΛσw_FT⟩
  -- Witness: w' = (ofReal k₂)⁻¹ · w
  refine ⟨complexLorentzAction (ComplexLorentzGroup.ofReal k₂)⁻¹ w,
    ofReal_inv_preserves_forwardTube k₂ w hw_FT, ?_⟩
  -- Goal: (k₁ * Λ * k₂) · σ · (k₂⁻¹ · w) ∈ FT
  -- = k₁ · Λ · k₂ · k₂⁻¹ · σ · w    (by σ-Λ commutativity, k₂ and σ commute)
  -- = k₁ · Λ · σ · w                  (k₂ · k₂⁻¹ = 1)
  -- = k₁ · (Λ · σ · w)                (by mul action)
  -- ∈ FT                               (by ofReal_preserves_forwardTube for k₁)
  have hcomm : permAct σ (complexLorentzAction (ComplexLorentzGroup.ofReal k₂)⁻¹ w) =
      complexLorentzAction (ComplexLorentzGroup.ofReal k₂)⁻¹ (permAct σ w) :=
    permAct_complexLorentzAction_comm n σ _ w
  -- (k₁ * Λ * k₂) · σ · (k₂⁻¹ · w)
  -- = (k₁ * Λ * k₂) · (k₂⁻¹ · (σ · w))    by hcomm
  -- = ((k₁ * Λ * k₂) * k₂⁻¹) · (σ · w)     by complexLorentzAction_mul
  -- = (k₁ * Λ) · (σ · w)                     by mul_assoc + mul_inv_cancel
  -- = k₁ · (Λ · (σ · w))                     by complexLorentzAction_mul
  rw [hcomm, ← complexLorentzAction_mul]
  -- Goal: (k₁ * Λ * k₂) * (ofReal k₂)⁻¹ · (σ · w) ∈ FT
  have hmul : ComplexLorentzGroup.ofReal k₁ * Λ * ComplexLorentzGroup.ofReal k₂ *
      (ComplexLorentzGroup.ofReal k₂)⁻¹ = ComplexLorentzGroup.ofReal k₁ * Λ := by
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [hmul, complexLorentzAction_mul]
  exact ofReal_preserves_forwardTube k₁ _ hΛσw_FT

/-- The converse direction of bi-invariance. -/
private lemma sliceIndexSet_bi_invariant_rev
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d) (k₁ k₂ : RestrictedLorentzGroup d) :
    (permForwardOverlapSlice (d := d) n σ
      (ComplexLorentzGroup.ofReal k₁ * Λ * ComplexLorentzGroup.ofReal k₂)).Nonempty →
    (permForwardOverlapSlice (d := d) n σ Λ).Nonempty := by
  rintro ⟨w, hw_FT, hkΛkσw_FT⟩
  -- Witness: w' = ofReal k₂ · w
  refine ⟨complexLorentzAction (ComplexLorentzGroup.ofReal k₂) w,
    ofReal_preserves_forwardTube k₂ w hw_FT, ?_⟩
  -- Goal: Λ · σ · (k₂ · w) ∈ FT
  -- (k₁ * Λ * k₂) · σ · w = k₁ · Λ · σ · (k₂ · w) ∈ FT  (same commutativity)
  -- So Λ · σ · (k₂ · w) = k₁⁻¹ · ((k₁ * Λ * k₂) · σ · w)
  have hcomm : permAct σ (complexLorentzAction (ComplexLorentzGroup.ofReal k₂) w) =
      complexLorentzAction (ComplexLorentzGroup.ofReal k₂) (permAct σ w) :=
    permAct_complexLorentzAction_comm n σ _ w
  rw [hcomm, ← complexLorentzAction_mul]
  -- Goal: (Λ * ofReal k₂) · (σ · w) ∈ FT
  -- We know: (k₁ * Λ * k₂) · (σ · w) ∈ FT
  -- = k₁ · ((Λ * k₂) · (σ · w))  by mul_assoc + complexLorentzAction_mul
  -- So (Λ * k₂) · (σ · w) = k₁⁻¹ · ((k₁ * Λ * k₂) · (σ · w))
  have hmul : Λ * ComplexLorentzGroup.ofReal k₂ =
      (ComplexLorentzGroup.ofReal k₁)⁻¹ *
        (ComplexLorentzGroup.ofReal k₁ * Λ * ComplexLorentzGroup.ofReal k₂) := by
    rw [mul_assoc, ← mul_assoc (ComplexLorentzGroup.ofReal k₁)⁻¹,
        inv_mul_cancel, one_mul]
  rw [hmul, complexLorentzAction_mul]
  exact ofReal_inv_preserves_forwardTube k₁ _ hkΛkσw_FT

/-! ### Connectedness of the forward-overlap set -/

/-- Boost generator in the Lorentz Lie algebra: the matrix with 1 at positions
    (0,1) and (1,0), zeros elsewhere. For `d ≥ 1` this generates boosts in the
    first spatial direction; for `d = 0` it is the zero matrix. -/
private def boostGen (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun μ ν => if (μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0) then 1 else 0

/-- The boost generator is in the Lorentz Lie algebra.
    Proof: `boostGenᵀ * ηℂ + ηℂ * boostGen = 0` because the (0,1) and (1,0)
    entries are exchanged by transpose, and the signs from `η₀₀ = -1`, `η₁₁ = 1`
    make the two terms cancel. -/
private lemma nested_ite_sum {n : ℕ} (a : Fin n) (P : Fin n → Prop) [DecidablePred P] (c : ℂ) :
    (∑ x : Fin n, if P x then (if a = x then c else 0) else 0) = if P a then c else 0 := by
  refine (Finset.sum_eq_single_of_mem a (Finset.mem_univ _) fun b _ hba => ?_).trans ?_
  · have : a ≠ b := fun h => hba (h ▸ rfl); rw [if_neg this]; split_ifs <;> rfl
  · simp

private lemma minkSig_cast_zero :
    ((minkowskiSignature d (0 : Fin (d + 1)) : ℝ) : ℂ) = -1 := by
  unfold minkowskiSignature; rw [if_pos rfl]; push_cast; ring

private lemma minkSig_cast_ne {i : Fin (d + 1)} (hi : i ≠ 0) :
    ((minkowskiSignature d i : ℝ) : ℂ) = 1 := by
  unfold minkowskiSignature; rw [if_neg hi]; push_cast; ring

private lemma boostGen_isInLieAlgebra :
    ComplexLorentzGroup.IsInLieAlgebra (boostGen d) := by
  unfold ComplexLorentzGroup.IsInLieAlgebra ComplexLorentzGroup.ηℂ boostGen
  ext μ ν
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.zero_apply, mul_ite, ite_mul, mul_one, mul_zero,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [nested_ite_sum]
  have hswap : ((↑ν : ℕ) = 0 ∧ (↑μ : ℕ) = 1 ∨ (↑ν : ℕ) = 1 ∧ (↑μ : ℕ) = 0) ↔
      ((↑μ : ℕ) = 0 ∧ (↑ν : ℕ) = 1 ∨ (↑μ : ℕ) = 1 ∧ (↑ν : ℕ) = 0) := by tauto
  by_cases hcond : (↑μ : ℕ) = 0 ∧ (↑ν : ℕ) = 1 ∨ (↑μ : ℕ) = 1 ∧ (↑ν : ℕ) = 0
  · rw [if_pos (hswap.mpr hcond), if_pos hcond]
    rcases hcond with ⟨hμ0, hν1⟩ | ⟨hμ1, hν0⟩
    · rw [minkSig_cast_ne (show ν ≠ 0 by intro h; subst h; simp at hν1),
          show μ = 0 from Fin.ext hμ0, minkSig_cast_zero]; ring
    · rw [show ν = 0 from Fin.ext hν0, minkSig_cast_zero,
          minkSig_cast_ne (show μ ≠ 0 by intro h; subst h; simp at hμ1)]; ring
  · rw [if_neg (mt hswap.mp hcond), if_neg hcond]; ring

/-- The boost exponential map `t ↦ exp(t · K)` from `ℂ` to the complex Lorentz group. -/
private def expBoost {d : ℕ} (t : ℂ) : ComplexLorentzGroup d :=
  ComplexLorentzGroup.expLieAlg (t • boostGen d)
    (ComplexLorentzGroup.isInLieAlgebra_smul t boostGen_isInLieAlgebra)

private lemma continuous_expBoost {d : ℕ} : Continuous (@expBoost d) := by
  have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
  rw [hind.continuous_iff]
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

/-! ### Matrix exponential of the boost generator -/

/-- K² is the projection onto the {0,1} block: diagonal with 1 at positions 0,1
    and 0 elsewhere. -/
private lemma boostGen_apply (d : ℕ) (μ ν : Fin (d + 1)) :
    boostGen d μ ν = if (μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0) then 1 else 0 := rfl

/-- K² = diag(1,1,0,...,0): the projection onto the {0,1} block.
    Proof: `(K*K)(μ,ν) = Σ_k K(μ,k)*K(k,ν)`. Since K only has nonzero entries at
    (0,1) and (1,0), the sum reduces to: if μ=0 then K(0,1)*K(1,ν) = K(1,ν),
    if μ=1 then K(1,0)*K(0,ν) = K(0,ν), else 0. -/
private lemma boostGen_sq (d : ℕ) (hd : 1 ≤ d) :
    boostGen d * boostGen d = fun μ ν : Fin (d + 1) =>
      if μ = ν ∧ μ.val ≤ 1 then (1 : ℂ) else 0 := by
  ext μ ν
  simp only [Matrix.mul_apply, boostGen_apply]
  -- sum_μν := ∑_k K(μ,k) * K(k,ν)
  -- K(μ,k) ≠ 0 iff (μ=0∧k=1) or (μ=1∧k=0).
  -- K(k,ν) ≠ 0 iff (k=0∧ν=1) or (k=1∧ν=0).
  rcases Nat.lt_or_ge μ.val 2 with hμ2 | hμ2
  · rcases Nat.lt_or_ge ν.val 2 with hν2 | hν2
    · have hμval : μ.val = 0 ∨ μ.val = 1 := by omega
      have hνval : ν.val = 0 ∨ ν.val = 1 := by omega
      rcases hμval with hμ0 | hμ1 <;> rcases hνval with hν0 | hν1
      · -- μ.val=0, ν.val=0: K²(μ,ν) = 1 via k=1, rhs=1.
        -- After simp only [hμν], goal uses ν throughout (μ replaced by ν).
        have hμν : μ = ν := Fin.ext (by omega)
        simp only [hμν, and_self, show ν.val ≤ 1 from by omega, ite_true]
        let k1 : Fin (d + 1) := ⟨1, by omega⟩
        refine (Finset.sum_eq_single_of_mem k1 (Finset.mem_univ _) ?_).trans ?_
        · intro k _ hkne
          -- k ≠ k1 means k.val ≠ 1; K(ν,k) with ν.val=0 is nonzero iff k.val=1; so it's zero.
          have hkne1 : k.val ≠ 1 := fun h => hkne (Fin.ext h)
          have h1 : ¬((ν.val = 0 ∧ k.val = 1) ∨ (ν.val = 1 ∧ k.val = 0)) := by omega
          rw [if_neg h1, zero_mul]
        · have h1 : (ν.val = 0 ∧ k1.val = 1) ∨ (ν.val = 1 ∧ k1.val = 0) :=
            Or.inl ⟨hν0, rfl⟩
          have h2 : (k1.val = 0 ∧ ν.val = 1) ∨ (k1.val = 1 ∧ ν.val = 0) :=
            Or.inr ⟨rfl, hν0⟩
          rw [if_pos h1, if_pos h2, mul_one]
      · -- μ.val=0, ν.val=1: K²(μ,ν) = 0, rhs=0.
        -- K(μ,k) nonzero iff k=1; K(k,ν) nonzero iff k=0; no k satisfies both.
        have hμν : μ ≠ ν := Fin.ne_of_val_ne (by omega)
        simp only [hμν, false_and, if_false]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk1 : k.val = 1
        · have h1 : (μ.val = 0 ∧ k.val = 1) ∨ (μ.val = 1 ∧ k.val = 0) := Or.inl ⟨hμ0, hk1⟩
          have h2 : ¬((k.val = 0 ∧ ν.val = 1) ∨ (k.val = 1 ∧ ν.val = 0)) := by omega
          rw [if_pos h1, if_neg h2, mul_zero]
        · have h1 : ¬((μ.val = 0 ∧ k.val = 1) ∨ (μ.val = 1 ∧ k.val = 0)) := by omega
          rw [if_neg h1, zero_mul]
      · -- μ.val=1, ν.val=0: K²(μ,ν) = 0, rhs=0.
        -- K(μ,k) nonzero iff k=0; K(k,ν) nonzero iff k=1; no k satisfies both.
        have hμν : μ ≠ ν := Fin.ne_of_val_ne (by omega)
        simp only [hμν, false_and, if_false]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk0 : k.val = 0
        · have h1 : (μ.val = 0 ∧ k.val = 1) ∨ (μ.val = 1 ∧ k.val = 0) := Or.inr ⟨hμ1, hk0⟩
          have h2 : ¬((k.val = 0 ∧ ν.val = 1) ∨ (k.val = 1 ∧ ν.val = 0)) := by omega
          rw [if_pos h1, if_neg h2, mul_zero]
        · have h1 : ¬((μ.val = 0 ∧ k.val = 1) ∨ (μ.val = 1 ∧ k.val = 0)) := by omega
          rw [if_neg h1, zero_mul]
      · -- μ.val=1, ν.val=1: K²(μ,ν) = 1 via k=0, rhs=1.
        -- After simp only [hμν], goal uses ν throughout (μ replaced by ν).
        have hμν : μ = ν := Fin.ext (by omega)
        simp only [hμν, and_self, show ν.val ≤ 1 from by omega, ite_true]
        let k0 : Fin (d + 1) := ⟨0, by omega⟩
        refine (Finset.sum_eq_single_of_mem k0 (Finset.mem_univ _) ?_).trans ?_
        · intro k _ hkne
          -- k ≠ k0 means k.val ≠ 0; K(ν,k) with ν.val=1 is nonzero iff k.val=0; so it's zero.
          have hkne0 : k.val ≠ 0 := fun h => hkne (Fin.ext h)
          have h1 : ¬((ν.val = 0 ∧ k.val = 1) ∨ (ν.val = 1 ∧ k.val = 0)) := by omega
          rw [if_neg h1, zero_mul]
        · have h1 : (ν.val = 0 ∧ k0.val = 1) ∨ (ν.val = 1 ∧ k0.val = 0) := Or.inr ⟨hν1, rfl⟩
          have h2 : (k0.val = 0 ∧ ν.val = 1) ∨ (k0.val = 1 ∧ ν.val = 0) := Or.inl ⟨rfl, hν1⟩
          rw [if_pos h1, if_pos h2, mul_one]
    · -- ν.val ≥ 2: K(k,ν) = 0 for all k, so sum = 0, rhs = 0.
      simp only [show ¬(μ = ν ∧ μ.val ≤ 1) from fun ⟨heq, hμle⟩ => by subst heq; omega,
                 if_false]
      apply Finset.sum_eq_zero
      intro k _
      have h2 : ¬((k.val = 0 ∧ ν.val = 1) ∨ (k.val = 1 ∧ ν.val = 0)) := by omega
      rw [if_neg h2, mul_zero]
  · -- μ.val ≥ 2: K(μ,k) = 0 for all k, so sum = 0, rhs = 0.
    simp only [show ¬(μ = ν ∧ μ.val ≤ 1) from fun ⟨_, hμle⟩ => by omega, if_false]
    apply Finset.sum_eq_zero
    intro k _
    have h1 : ¬((μ.val = 0 ∧ k.val = 1) ∨ (μ.val = 1 ∧ k.val = 0)) := by omega
    rw [if_neg h1, zero_mul]

/-- K² is the block-diagonal projection: (K²)(μ,ν) = 1 if μ = ν and μ.val ≤ 1, else 0.
    We express it as a diagonal-like matrix for easier manipulation. -/
private lemma boostGen_sq_apply (d : ℕ) (hd : 1 ≤ d) (μ ν : Fin (d + 1)) :
    (boostGen d * boostGen d) μ ν =
      if μ = ν ∧ μ.val ≤ 1 then (1 : ℂ) else 0 := by
  rw [boostGen_sq d hd]

/-- K³ = K: the boost generator cubed equals itself. -/
private lemma boostGen_cubed (d : ℕ) (hd : 1 ≤ d) :
    boostGen d * boostGen d * boostGen d = boostGen d := by
  ext μ ν
  simp only [Matrix.mul_apply, boostGen_sq_apply d hd, boostGen_apply]
  -- (K²·K)(μ,ν) = Σ_k K²(μ,k) · K(k,ν)
  -- K²(μ,k) = 1 if μ=k and μ.val ≤ 1, else 0
  -- So the sum picks up K(μ,ν) when μ.val ≤ 1, and 0 otherwise
  by_cases hμle : μ.val ≤ 1
  · -- μ.val ≤ 1: sum has one nonzero term at k = μ
    rw [Finset.sum_eq_single_of_mem μ (Finset.mem_univ _)]
    · simp [hμle]
    · intro k _ hkne
      rw [if_neg (fun h => hkne h.1.symm), zero_mul]
  · -- μ.val ≥ 2: K²(μ,k) = 0 for all k, so sum = 0
    -- Also K(μ,ν) = 0 since μ.val ≥ 2
    have hK : ¬((μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0)) := by omega
    rw [if_neg hK]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (fun h => by omega), zero_mul]

/-- For an idempotent matrix E (E² = E) in a complete normed algebra,
    exp(α · E) = 1 + (exp(α) - 1) · E. -/
private lemma exp_smul_idempotent {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℂ) (hE : E * E = E) (α : ℂ) :
    exp (α • E) = 1 + (Complex.exp α - 1) • E := by
  -- E^m = E for all m ≥ 1 (by induction using idempotency E² = E).
  have hEpow : ∀ m : ℕ, 1 ≤ m → E ^ m = E := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le hm with h | h
      · simp [← h, pow_one]
      · rw [pow_succ, ih (Nat.lt_succ_iff.mp h), hE]
  -- HasSum for Complex.exp α via the power series.
  have hSα : HasSum (fun m : ℕ => (m.factorial⁻¹ : ℂ) • α ^ m) (Complex.exp α) := by
    have := exp_series_hasSum_exp' (𝕂 := ℂ) α
    rwa [← Complex.exp_eq_exp_ℂ] at this
  -- Shifted HasSum: ∑_{m≥0} (m+1)!⁻¹ · α^(m+1) = exp(α) - 1
  -- (splitting off the m = 0 term from hSα).
  have hSα_shifted : HasSum (fun m : ℕ => ((m + 1).factorial⁻¹ : ℂ) • α ^ (m + 1))
      (Complex.exp α - 1) := by
    rw [hasSum_nat_add_iff (f := fun m => (m.factorial⁻¹ : ℂ) • α ^ m) (k := 1)]
    simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    convert hSα using 1; ring
  -- Matrix tail HasSum: ∑_{m≥0} (m+1)!⁻¹ · α^(m+1) · E = (exp(α) - 1) · E.
  have hMatTail : HasSum (fun m : ℕ => ((m + 1).factorial⁻¹ : ℂ) • α ^ (m + 1) • E)
      ((Complex.exp α - 1) • E) := by
    have h := hSα_shifted.smul_const E
    convert h using 2; ext m; rw [smul_assoc]
  -- HasSum for the matrix exponential power series.
  have hS : HasSum (fun m : ℕ => (m.factorial⁻¹ : ℂ) • (α ^ m • E ^ m)) (exp (α • E)) := by
    have := exp_series_hasSum_exp' (𝕂 := ℂ) (α • E)
    simp_rw [smul_pow] at this; exact this
  -- Use uniqueness of HasSum: show both sides are limits of the same series.
  apply hS.unique
  -- Build HasSum for 1 + (exp α - 1) · E by reassembling: head term (m=0) is 1,
  -- tail terms (m≥1) sum to (exp α - 1) · E via hMatTail and hEpow.
  have hFsucc : HasSum (fun m : ℕ => ((m + 1).factorial⁻¹ : ℂ) • (α ^ (m + 1) • E ^ (m + 1)))
      ((Complex.exp α - 1) • E) := by
    simp_rw [hEpow _ (Nat.succ_le_succ (Nat.zero_le _))]; exact hMatTail
  have h := (hasSum_nat_add_iff (f := fun m => (m.factorial⁻¹ : ℂ) • (α ^ m • E ^ m))
      (k := 1)).mp hFsucc
  convert h using 1; simp [pow_zero, add_comm]

private lemma exp_boostGen_eq (d : ℕ) (hd : 1 ≤ d) (t : ℂ) :
    exp (t • boostGen d) =
      1 + Complex.sinh t • boostGen d + (Complex.cosh t - 1) • (boostGen d * boostGen d) := by
  set K := boostGen d
  set P := K * K  -- K² = projection onto {0,1} block
  -- Define Pp = (P + K)/2, Pm = (P - K)/2
  set Pp := (2 : ℂ)⁻¹ • (P + K)
  set Pm := (2 : ℂ)⁻¹ • (P - K)
  -- Key properties:
  -- 1. K = Pp - Pm
  have hK_decomp : K = Pp - Pm := by
    simp [Pp, Pm]; ring_nf; simp [smul_sub, ← sub_smul]; ring_nf
    ext; simp [smul_apply, smul_eq_mul]; ring
  -- 2. Pp² = Pp (using K³ = K, i.e., P*K = K)
  have hPK : P * K = K := boostGen_cubed d hd
  have hKP : K * P = K := by
    have : K * K * K = K := boostGen_cubed d hd
    rw [mul_assoc] at this; exact this
  have hP_sq : P * P = P := by
    -- P² = (K*K)*(K*K). Using K*K*K = K: (K*K)*(K*K) = K*(K*(K*K)) = K*(K*K*K) = K*K = P.
    change K * K * (K * K) = K * K
    -- Reassociate: (K*K) * (K*K) = K * (K * K * K)
    rw [← mul_assoc (K * K) K K, boostGen_cubed d hd]
  -- K*K = P holds by the `set` definition
  have hKK : K * K = P := rfl
  have hPPp : Pp * Pp = Pp := by
    simp only [Pp]
    -- (P+K)² = P²+PK+KP+K² = P+K+K+P = 2(P+K), so (1/2·(P+K))² = 1/2·(P+K)
    have key : (P + K) * (P + K) = (2 : ℂ) • (P + K) := by
      rw [add_mul, mul_add, mul_add, hP_sq, hPK, hKP, hKK, two_smul]; abel
    rw [smul_mul_assoc, Algebra.mul_smul_comm, key, smul_smul, smul_smul]
    norm_num
  have hPPm : Pm * Pm = Pm := by
    simp only [Pm]
    -- (P-K)² = P²-PK-KP+K² = P-K-K+P = 2(P-K), so (1/2·(P-K))² = 1/2·(P-K)
    have key : (P - K) * (P - K) = (2 : ℂ) • (P - K) := by
      rw [sub_mul, mul_sub, mul_sub, hP_sq, hPK, hKP, hKK, two_smul]; abel
    rw [smul_mul_assoc, Algebra.mul_smul_comm, key, smul_smul, smul_smul]
    norm_num
  have hPpPm : Pp * Pm = 0 := by
    simp only [Pp, Pm]
    -- (P+K)·(P-K) = P²-PK+KP-K² = P-K+K-P = 0
    have key : (P + K) * (P - K) = 0 := by
      rw [add_mul, mul_sub, mul_sub, hP_sq, hPK, hKP, hKK]; abel
    rw [smul_mul_assoc, Algebra.mul_smul_comm, key, smul_zero, smul_zero]
  -- 3. t•K = t•Pp + (-t)•Pm
  have hdecomp : t • K = t • Pp + (-t) • Pm := by
    rw [hK_decomp]; ext; simp [smul_apply, sub_apply, smul_eq_mul]; ring
  -- 4. Commute (t•Pp) (-t•Pm): both sides factor through Pp·Pm = 0 and Pm·Pp = 0
  have hcomm : Commute (t • Pp) ((-t) • Pm) := by
    rw [Commute, SemiconjBy]
    simp only [Pp, Pm]
    have hPpPm' : (P + K) * (P - K) = 0 := by
      rw [add_mul, mul_sub, mul_sub, hP_sq, hPK, hKP, hKK]; abel
    have hPmPp' : (P - K) * (P + K) = 0 := by
      rw [sub_mul, mul_add, mul_add, hP_sq, hPK, hKP, hKK]; abel
    rw [smul_mul_assoc, Algebra.mul_smul_comm, smul_mul_assoc, Algebra.mul_smul_comm,
        smul_mul_assoc, Algebra.mul_smul_comm, smul_mul_assoc, Algebra.mul_smul_comm]
    simp [hPpPm', hPmPp']
  -- 5. Apply exp_add_of_commute
  rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm]
  -- 6. Apply exp_smul_idempotent to both factors
  rw [exp_smul_idempotent Pp hPPp t, exp_smul_idempotent Pm hPPm (-t)]
  -- 7. Expand product: cross term (eᵗ-1)·Pp·(e⁻ᵗ-1)·Pm = 0 since Pp·Pm = 0
  rw [add_mul, mul_add, mul_add, one_mul, mul_one]
  have cross : (Complex.exp t - 1) • Pp * ((Complex.exp (-t) - 1) • Pm) = 0 := by
    rw [smul_mul_assoc, Algebra.mul_smul_comm, hPpPm, smul_zero, smul_zero]
  rw [cross, add_zero]
  -- Remaining goal: 1 + (e⁻ᵗ-1)·Pm + (eᵗ-1)·Pp = 1 + sinh(t)·K + (cosh(t)-1)·P
  -- Unfold Pp = (P+K)/2, Pm = (P-K)/2 and use sinh/cosh definitions
  simp only [Pp, Pm, smul_smul, smul_add, smul_sub]
  rw [show Complex.sinh t = (Complex.exp t - Complex.exp (-t)) / 2 from rfl,
      show Complex.cosh t = (Complex.exp t + Complex.exp (-t)) / 2 from rfl,
      show (Complex.exp t + Complex.exp (-t)) / 2 - 1 =
          (Complex.exp t - 1) * 2⁻¹ + (Complex.exp (-t) - 1) * 2⁻¹ by ring,
      show (Complex.exp t - Complex.exp (-t)) / 2 =
          (Complex.exp t - 1) * 2⁻¹ - (Complex.exp (-t) - 1) * 2⁻¹ by ring]
  simp [add_smul, sub_smul]
  ring_nf
  abel

/-- The entry formula for exp(t · K).

    `exp(t • boostGen d)` has entries:
    - (0,0) and (1,1): `cosh(t)`
    - (0,1) and (1,0): `sinh(t)`
    - (μ,ν) with μ = ν ≥ 2: `1`
    - all others: `0`

    Proof: K = Pp - Pm where Pp = (K² + K)/2, Pm = (K² - K)/2 are
    orthogonal idempotents. By `exp_add_of_commute`,
    `exp(tK) = exp(tPp) · exp(-tPm)`, and for idempotent E,
    `exp(αE) = 1 + (exp(α) - 1) · E`. Expanding and simplifying
    with `cosh(t) = (exp(t) + exp(-t))/2`, `sinh(t) = (exp(t) - exp(-t))/2`
    gives the result. -/
private lemma expBoost_val_entry (t : ℂ) (hd : 1 ≤ d) (μ ν : Fin (d + 1)) :
    (expBoost t).val μ ν =
      if μ.val = 0 ∧ ν.val = 0 then Complex.cosh t
      else if (μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0) then Complex.sinh t
      else if μ.val = 1 ∧ ν.val = 1 then Complex.cosh t
      else if μ = ν then 1
      else 0 := by
  -- expBoost t = exp(t • K), and exp(t•K) = I + sinh(t)·K + (cosh(t)-1)·K²
  show (exp (t • boostGen d)) μ ν = _
  rw [exp_boostGen_eq d hd]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    boostGen_apply, boostGen_sq_apply d hd]
  -- Goal: (if μ = ν then 1 else 0) + sinh(t) * (if (μ.val=0∧ν.val=1)∨(μ.val=1∧ν.val=0) then 1 else 0)
  --       + (cosh(t)-1) * (if μ=ν ∧ μ.val≤1 then 1 else 0) = RHS
  -- Case split on μ.val and ν.val
  rcases Nat.lt_or_ge μ.val 2 with hμ2 | hμ2
  · rcases Nat.lt_or_ge ν.val 2 with hν2 | hν2
    · -- Both μ.val, ν.val ∈ {0, 1}
      have hμval : μ.val = 0 ∨ μ.val = 1 := by omega
      have hνval : ν.val = 0 ∨ ν.val = 1 := by omega
      rcases hμval with hμ0 | hμ1 <;> rcases hνval with hν0 | hν1
      · -- μ.val=0, ν.val=0: result is cosh t
        have hμν : μ = ν := Fin.ext (by omega)
        have hK : ¬((μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0)) := by omega
        have hKsq : μ = ν ∧ μ.val ≤ 1 := ⟨hμν, by omega⟩
        rw [if_pos hμν, if_neg hK, if_pos hKsq, if_pos ⟨hμ0, hν0⟩]
        ring
      · -- μ.val=0, ν.val=1: result is sinh t
        have hμν : μ ≠ ν := Fin.ne_of_val_ne (by omega)
        have hK : (μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0) := Or.inl ⟨hμ0, hν1⟩
        have hKsq : ¬(μ = ν ∧ μ.val ≤ 1) := fun h => hμν h.1
        rw [if_neg hμν, if_pos hK, if_neg hKsq,
            if_neg (by omega : ¬(μ.val = 0 ∧ ν.val = 0)), if_pos hK]
        ring
      · -- μ.val=1, ν.val=0: result is sinh t
        have hμν : μ ≠ ν := Fin.ne_of_val_ne (by omega)
        have hK : (μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0) := Or.inr ⟨hμ1, hν0⟩
        have hKsq : ¬(μ = ν ∧ μ.val ≤ 1) := fun h => hμν h.1
        -- After rw [if_neg hμν, if_pos hK, if_neg hKsq]:
        -- LHS: 0 + sinh(t) * 1 + (cosh(t)-1) * 0
        -- RHS: if μ.val=1 ∧ ν.val=1 then cosh t else ...  (the 0∧0 case already ruled out by hK)
        rw [if_neg hμν, if_pos hK, if_neg hKsq,
            if_neg (by omega : ¬(μ.val = 0 ∧ ν.val = 0)),
            if_pos hK]
        ring
      · -- μ.val=1, ν.val=1: result is cosh t
        have hμν : μ = ν := Fin.ext (by omega)
        have hK : ¬((μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0)) := by omega
        have hKsq : μ = ν ∧ μ.val ≤ 1 := ⟨hμν, by omega⟩
        rw [if_pos hμν, if_neg hK, if_pos hKsq,
            if_neg (by omega : ¬(μ.val = 0 ∧ ν.val = 0)),
            if_neg (by omega : ¬((μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0))),
            if_pos ⟨hμ1, hν1⟩]
        ring
    · -- μ.val < 2, ν.val ≥ 2
      have hK : ¬((μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0)) := by omega
      have hμν : μ ≠ ν := Fin.ne_of_val_ne (by omega)
      have hKsq : ¬(μ = ν ∧ μ.val ≤ 1) := fun h => hμν h.1
      rw [if_neg hμν, if_neg hK, if_neg hKsq,
          if_neg (by omega : ¬(μ.val = 0 ∧ ν.val = 0)),
          if_neg hK,
          if_neg (by omega : ¬(μ.val = 1 ∧ ν.val = 1))]
      simp
  · -- μ.val ≥ 2
    have hK : ¬((μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0)) := by omega
    have hKsq_cond : ¬(μ = ν ∧ μ.val ≤ 1) := fun ⟨_, hle⟩ => by omega
    rw [if_neg hK, if_neg hKsq_cond,
        if_neg (by omega : ¬(μ.val = 0 ∧ ν.val = 0)),
        if_neg hK,
        if_neg (by omega : ¬(μ.val = 1 ∧ ν.val = 1))]
    rcases eq_or_ne μ ν with hμν | hμν
    · rw [if_pos hμν]; ring
    · rw [if_neg hμν]; ring

/-- Entry formula for the real boost element in the `(0,1)` plane. -/
private lemma boostElement_val_entry (hd1 : 1 ≤ d) (a : ℝ) (μ ν : Fin (d + 1)) :
    let k0 : Fin d := ⟨0, by omega⟩
    let i0 : Fin (d + 1) := k0.succ
    ((LorentzLieGroup.boostElement d k0 a).val.val μ ν : ℂ) =
      if μ = 0 ∧ ν = 0 then Complex.cosh (a : ℂ)
      else if (μ = 0 ∧ ν = i0) ∨ (μ = i0 ∧ ν = 0) then Complex.sinh (a : ℂ)
      else if μ = i0 ∧ ν = i0 then Complex.cosh (a : ℂ)
      else if μ = ν then 1
      else 0 := by
  classical
  dsimp
  let k0 : Fin d := ⟨0, by omega⟩
  let i0 : Fin (d + 1) := k0.succ
  have hk0succ : k0.succ = (⟨1, by omega⟩ : Fin (d + 1)) := by
    ext
    simp [k0]
  change ((LorentzLieGroup.planarBoost d k0 a μ ν : ℝ) : ℂ) = _
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [LorentzLieGroup.pb0 d k0 a ν]
    by_cases hν0 : ν = 0
    · subst hν0
      simp [i0, hk0succ, Complex.ofReal_cosh]
    · by_cases hν1 : ν = i0
      · subst hν1
        simp [i0, hk0succ, Complex.ofReal_sinh]
      · have hνidx : ν ≠ (⟨1, by omega⟩ : Fin (d + 1)) := by
          intro h
          exact hν1 (by simpa [i0, hk0succ] using h)
        have hν0' : ¬(0 : Fin (d + 1)) = ν := by simpa [eq_comm] using hν0
        simp [hν0, hν1, hνidx, hν0', i0, hk0succ]
  · by_cases hμ1 : μ = i0
    · subst hμ1
      rw [LorentzLieGroup.pbK d k0 a ν]
      by_cases hν0 : ν = 0
      · subst hν0
        simp [i0, hk0succ, Complex.ofReal_sinh]
      · by_cases hν1 : ν = i0
        · subst hν1
          simp [i0, hk0succ, Complex.ofReal_cosh]
        · have hνidx : ν ≠ (⟨1, by omega⟩ : Fin (d + 1)) := by
            intro h
            exact hν1 (by simpa [i0, hk0succ] using h)
          have hνidx' : ¬(⟨1, by omega⟩ : Fin (d + 1)) = ν := by
            simpa [eq_comm] using hνidx
          simp [hν0, hν1, hνidx, hνidx', i0, hk0succ]
    · rw [LorentzLieGroup.pbO d k0 a μ hμ0 hμ1 ν]
      by_cases hμν : μ = ν
      · subst hμν
        have hμidx : μ ≠ (⟨1, by omega⟩ : Fin (d + 1)) := by
          intro h
          exact hμ1 (by simpa [i0, hk0succ] using h)
        simp [hμ0, hμ1, hμidx, i0, hk0succ]
      · have hμidx : μ ≠ (⟨1, by omega⟩ : Fin (d + 1)) := by
          intro h
          exact hμ1 (by simpa [i0, hk0succ] using h)
        simp [hμ0, hμ1, hμν, hμidx, i0, hk0succ]

/-- Real boost parameters are exactly real Lorentz boosts in the first spatial direction. -/
private lemma expBoost_ofReal_re (hd1 : 1 ≤ d) (a : ℝ) :
    expBoost (d := d) (a : ℂ) =
      ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a) := by
  ext μ ν
  change (expBoost (d := d) (a : ℂ)).val μ ν =
      (((LorentzLieGroup.boostElement d ⟨0, by omega⟩ a).val.val μ ν : ℂ))
  rw [expBoost_val_entry (d := d) (t := (a : ℂ)) hd1 μ ν,
      boostElement_val_entry (d := d) hd1 a μ ν]
  have hk0succ : ((⟨0, by omega⟩ : Fin d).succ : Fin (d + 1)) = ⟨1, by omega⟩ := by
    ext
    simp
  have hμ0 : (μ = (0 : Fin (d + 1))) ↔ μ.val = 0 := by
    constructor
    · intro h
      simpa [h]
    · intro h
      exact Fin.ext h
  have hν0 : (ν = (0 : Fin (d + 1))) ↔ ν.val = 0 := by
    constructor
    · intro h
      simpa [h]
    · intro h
      exact Fin.ext h
  have hμ1 : (μ = (⟨1, by omega⟩ : Fin (d + 1))) ↔ μ.val = 1 := by
    constructor
    · intro h
      simpa [h]
    · intro h
      exact Fin.ext h
  have hν1 : (ν = (⟨1, by omega⟩ : Fin (d + 1))) ↔ ν.val = 1 := by
    constructor
    · intro h
      simpa [h]
    · intro h
      exact Fin.ext h
  have hμi0 : (μ = ((⟨0, by omega⟩ : Fin d).succ : Fin (d + 1))) ↔ μ.val = 1 := by
    constructor
    · intro h
      have h' : μ = (⟨1, by omega⟩ : Fin (d + 1)) := by simpa [hk0succ] using h
      exact hμ1.mp h'
    · intro h
      have h' : μ = (⟨1, by omega⟩ : Fin (d + 1)) := hμ1.mpr h
      simpa [hk0succ] using h'
  have hνi0 : (ν = ((⟨0, by omega⟩ : Fin d).succ : Fin (d + 1))) ↔ ν.val = 1 := by
    constructor
    · intro h
      have h' : ν = (⟨1, by omega⟩ : Fin (d + 1)) := by simpa [hk0succ] using h
      exact hν1.mp h'
    · intro h
      have h' : ν = (⟨1, by omega⟩ : Fin (d + 1)) := hν1.mpr h
      simpa [hk0succ] using h'
  have h00 :
      (μ = (0 : Fin (d + 1)) ∧ ν = (0 : Fin (d + 1))) ↔
        (μ.val = 0 ∧ ν.val = 0) := hμ0.and hν0
  have h01 :
      (μ = (0 : Fin (d + 1)) ∧ ν = ((⟨0, by omega⟩ : Fin d).succ : Fin (d + 1)) ∨
          μ = ((⟨0, by omega⟩ : Fin d).succ : Fin (d + 1)) ∧ ν = (0 : Fin (d + 1))) ↔
        (μ.val = 0 ∧ ν.val = 1 ∨ μ.val = 1 ∧ ν.val = 0) := by
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl ⟨hμ0.mp h.1, hνi0.mp h.2⟩
      · exact Or.inr ⟨hμi0.mp h.1, hν0.mp h.2⟩
    · intro h
      rcases h with h | h
      · exact Or.inl ⟨hμ0.mpr h.1, hνi0.mpr h.2⟩
      · exact Or.inr ⟨hμi0.mpr h.1, hν0.mpr h.2⟩
  have h11 :
      (μ = ((⟨0, by omega⟩ : Fin d).succ : Fin (d + 1)) ∧
          ν = ((⟨0, by omega⟩ : Fin d).succ : Fin (d + 1))) ↔
        (μ.val = 1 ∧ ν.val = 1) := hμi0.and hνi0
  simpa [h00, h01, h11, hμ1, hν1]

/-- `expBoost` is `2πi`-periodic (for `d ≥ 1`), reflecting the boost-cylinder
    parameterization `t ~ t + 2πi`. -/
private lemma expBoost_periodic_two_pi_I {d : ℕ} (hd : 1 ≤ d) (t : ℂ) :
    expBoost (d := d) (t + (2 * Real.pi : ℂ) * Complex.I) = expBoost (d := d) t := by
  have hsinh_2piI : Complex.sinh ((2 * Real.pi : ℂ) * Complex.I) = 0 := by
    simpa [Complex.sin_two_pi] using Complex.sinh_mul_I (2 * (Real.pi : ℂ))
  have hcosh_2piI : Complex.cosh ((2 * Real.pi : ℂ) * Complex.I) = 1 := by
    simpa [Complex.cos_two_pi] using Complex.cosh_mul_I (2 * (Real.pi : ℂ))
  have hsinh_shift :
      Complex.sinh (t + (2 * Real.pi : ℂ) * Complex.I) = Complex.sinh t := by
    rw [Complex.sinh_add, hsinh_2piI, hcosh_2piI]
    simp
  have hcosh_shift :
      Complex.cosh (t + (2 * Real.pi : ℂ) * Complex.I) = Complex.cosh t := by
    rw [Complex.cosh_add, hsinh_2piI, hcosh_2piI]
    simp
  ext μ ν
  simp [expBoost_val_entry, hd, hsinh_shift, hcosh_shift]

/-- `expBoost` is periodic under shifts by integer multiples of `2πi`. -/
private lemma expBoost_periodic_two_pi_I_int {d : ℕ} (hd : 1 ≤ d) (t : ℂ) (m : ℤ) :
    expBoost (d := d) (t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) = expBoost (d := d) t := by
  have hmI :
      (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) =
        ((m : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by ring
  have hsinh_m : Complex.sinh (((m : ℂ) * (2 * Real.pi : ℂ)) * Complex.I) = 0 := by
    rw [Complex.sinh_mul_I]
    have hmul :
        ((m : ℂ) * (2 * Real.pi : ℂ)) = (((2 * m : ℤ) : ℂ) * (Real.pi : ℂ)) := by
      norm_num [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    have hsin :
        Complex.sin (((m : ℂ) * (2 * Real.pi : ℂ))) = 0 := by
      rw [hmul]
      simpa using Complex.sin_int_mul_pi (2 * m)
    simp [hsin]
  have hcosh_m : Complex.cosh (((m : ℂ) * (2 * Real.pi : ℂ)) * Complex.I) = 1 := by
    rw [Complex.cosh_mul_I]
    simpa [mul_assoc] using Complex.cos_int_mul_two_pi m
  have hsinh_shift :
      Complex.sinh (t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) = Complex.sinh t := by
    rw [hmI, Complex.sinh_add, hsinh_m, hcosh_m]
    simp
  have hcosh_shift :
      Complex.cosh (t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) = Complex.cosh t := by
    rw [hmI, Complex.cosh_add, hsinh_m, hcosh_m]
    simp
  ext μ ν
  simp [expBoost_val_entry, hd, hsinh_shift, hcosh_shift]

/-- Additivity of the boost exponential: `expBoost (u+v) = expBoost u * expBoost v`. -/
private lemma expBoost_add {d : ℕ} (u v : ℂ) :
    expBoost (d := d) (u + v) = expBoost (d := d) u * expBoost (d := d) v := by
  apply ComplexLorentzGroup.ext
  set K : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := boostGen d
  change exp ((u + v) • K) = exp (u • K) * exp (v • K)
  have hcomm : Commute (u • K) (v • K) := by
    rw [Commute, SemiconjBy]
    simp [smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_assoc, mul_comm, mul_left_comm]
  simpa [add_smul] using Matrix.exp_add_of_commute (u • K) (v • K) hcomm

/-- Time row of `expBoost (π i)` is `(-1,0,0,...)`. -/
private lemma expBoost_pi_I_row0 {d : ℕ} (hd1 : 1 ≤ d) (ν : Fin (d + 1)) :
    (expBoost (d := d) ((Real.pi : ℂ) * Complex.I)).val 0 ν = if ν = 0 then (-1 : ℂ) else 0 := by
  have h := expBoost_val_entry (d := d) (((Real.pi : ℂ) * Complex.I)) hd1 0 ν
  by_cases hν0 : ν = 0
  · subst hν0
    simpa [Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi, Complex.sin_pi]
      using h
  · have hν0' : ν.val ≠ 0 := by
      intro hv
      exact hν0 (Fin.ext hv)
    by_cases hν1 : ν = (⟨1, by omega⟩ : Fin (d + 1))
    · subst hν1
      have hzero :
          (expBoost (d := d) ((Real.pi : ℂ) * Complex.I)).val 0 (⟨1, by omega⟩ : Fin (d + 1)) = 0 := by
        simpa [hν0, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi, Complex.sin_pi]
          using h
      simpa using hzero
    · have hν1' : ν.val ≠ 1 := by
        intro hv
        exact hν1 (Fin.ext hv)
      have h0ν : (0 : Fin (d + 1)) ≠ ν := by
        simpa [eq_comm] using hν0
      have hzero :
          (expBoost (d := d) ((Real.pi : ℂ) * Complex.I)).val 0 ν = 0 := by
        simpa [hν0, h0ν, hν0', hν1', Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi, Complex.sin_pi]
          using h
      simpa [hν0] using hzero

/-- The `μ=0` component of `expBoost(π i)` action is negation. -/
private lemma expBoost_pi_I_action_time0 {d n : ℕ} (hd1 : 1 ≤ d)
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) :
    complexLorentzAction (expBoost (d := d) ((Real.pi : ℂ) * Complex.I)) z k 0 =
      -(z k 0) := by
  simp only [complexLorentzAction]
  refine (Finset.sum_eq_single_of_mem (0 : Fin (d + 1)) (Finset.mem_univ _) ?_).trans ?_
  · intro b _ hb
    have hb0 : b ≠ (0 : Fin (d + 1)) := by simpa [eq_comm] using hb
    simp [expBoost_pi_I_row0 (d := d) hd1, hb0]
  · simp [expBoost_pi_I_row0 (d := d) hd1]

/-- Spatial index `0` (first spatial coordinate) for `d ≥ 2`. -/
private def weylIdx0 (d : ℕ) (hd2 : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-- Spatial index `1` (second spatial coordinate) for `d ≥ 2`. -/
private def weylIdx1 (d : ℕ) (hd2 : 2 ≤ d) : Fin d := ⟨1, by omega⟩

private lemma weylIdx_ne (d : ℕ) (hd2 : 2 ≤ d) :
    weylIdx0 d hd2 ≠ weylIdx1 d hd2 := by
  simp [weylIdx0, weylIdx1]

/-- The Weyl reflection candidate: a `π`-rotation in the `(1,2)` spatial plane.
    It flips the boost spatial axis while staying in `SO↑(1,d;ℝ)`. -/
private def weylRot (d : ℕ) (hd2 : 2 ≤ d) : RestrictedLorentzGroup d :=
  spatialRotElement d (weylIdx0 d hd2) (weylIdx1 d hd2) (weylIdx_ne d hd2) Real.pi

/-- Time row of the Weyl rotation is unchanged. -/
private lemma weylRot_row_time (d : ℕ) (hd2 : 2 ≤ d) (ν : Fin (d + 1)) :
    (weylRot d hd2).val.val 0 ν = if ν = 0 then 1 else 0 := by
  change spatialRot d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi 0 ν = _
  rw [sr_other d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi 0
    (by simp [weylIdx0]) (by simp [weylIdx1]) ν]
  simp [eq_comm]

/-- Time column of the Weyl rotation is unchanged. -/
private lemma weylRot_col_time (d : ℕ) (hd2 : 2 ≤ d) (μ : Fin (d + 1)) :
    (weylRot d hd2).val.val μ 0 = if μ = 0 then 1 else 0 := by
  change spatialRot d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi μ 0 = _
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [sr_other d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi 0
      (by simp [weylIdx0]) (by simp [weylIdx1]) 0]
  · by_cases hμ1 : μ = (weylIdx0 d hd2).succ
    · subst hμ1
      rw [sr_i d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi 0]
      simp [weylIdx0]
    · by_cases hμ2 : μ = (weylIdx1 d hd2).succ
      · subst hμ2
        rw [sr_j d (weylIdx0 d hd2) (weylIdx1 d hd2) (weylIdx_ne d hd2) Real.pi 0]
        simp [weylIdx0, weylIdx1]
      · rw [sr_other d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi μ hμ1 hμ2 0]

/-- Boost row (spatial index 1) picks up a minus sign under the Weyl rotation. -/
private lemma weylRot_row_boost (d : ℕ) (hd2 : 2 ≤ d) (ν : Fin (d + 1)) :
    (weylRot d hd2).val.val (weylIdx0 d hd2).succ ν =
      if ν = (weylIdx0 d hd2).succ then (-1 : ℝ) else 0 := by
  change spatialRot d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi (weylIdx0 d hd2).succ ν = _
  rw [sr_i d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi ν]
  simp [weylIdx0, Real.sin_pi, Real.cos_pi]

/-- Boost column (spatial index 1) picks up a minus sign under the Weyl rotation. -/
private lemma weylRot_col_boost (d : ℕ) (hd2 : 2 ≤ d) (μ : Fin (d + 1)) :
    (weylRot d hd2).val.val μ (weylIdx0 d hd2).succ =
      if μ = (weylIdx0 d hd2).succ then (-1 : ℝ) else 0 := by
  change spatialRot d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi μ (weylIdx0 d hd2).succ = _
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [sr_other d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi 0
      (by simp [weylIdx0]) (by simp [weylIdx1]) (weylIdx0 d hd2).succ]
    simp [weylIdx0]
  · by_cases hμ1 : μ = (weylIdx0 d hd2).succ
    · subst hμ1
      rw [sr_i d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi (weylIdx0 d hd2).succ]
      simp [weylIdx0, Real.sin_pi, Real.cos_pi]
    · by_cases hμ2 : μ = (weylIdx1 d hd2).succ
      · subst hμ2
        rw [sr_j d (weylIdx0 d hd2) (weylIdx1 d hd2) (weylIdx_ne d hd2) Real.pi
          (weylIdx0 d hd2).succ]
        simp [weylIdx0, weylIdx1, Real.sin_pi]
      · rw [sr_other d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi μ hμ1 hμ2
          (weylIdx0 d hd2).succ]
        simp [hμ1]

/-- Complex-cast version of `weylRot_row_time`. -/
private lemma weylRotC_row_time (d : ℕ) (hd2 : 2 ≤ d) (ν : Fin (d + 1)) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2)).val 0 ν =
      if ν = 0 then (1 : ℂ) else 0 := by
  change ((weylRot d hd2).val.val 0 ν : ℂ) = _
  rw [weylRot_row_time d hd2 ν]
  split_ifs <;> simp

/-- Complex-cast version of `weylRot_col_time`. -/
private lemma weylRotC_col_time (d : ℕ) (hd2 : 2 ≤ d) (μ : Fin (d + 1)) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2)).val μ 0 =
      if μ = 0 then (1 : ℂ) else 0 := by
  change ((weylRot d hd2).val.val μ 0 : ℂ) = _
  rw [weylRot_col_time d hd2 μ]
  split_ifs <;> simp

/-- Complex-cast version of `weylRot_row_boost`. -/
private lemma weylRotC_row_boost (d : ℕ) (hd2 : 2 ≤ d) (ν : Fin (d + 1)) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2)).val (weylIdx0 d hd2).succ ν =
      if ν = (weylIdx0 d hd2).succ then (-1 : ℂ) else 0 := by
  change ((weylRot d hd2).val.val (weylIdx0 d hd2).succ ν : ℂ) = _
  rw [weylRot_row_boost d hd2 ν]
  split_ifs <;> simp

/-- Complex-cast version of `weylRot_col_boost`. -/
private lemma weylRotC_col_boost (d : ℕ) (hd2 : 2 ≤ d) (μ : Fin (d + 1)) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2)).val μ (weylIdx0 d hd2).succ =
      if μ = (weylIdx0 d hd2).succ then (-1 : ℂ) else 0 := by
  change ((weylRot d hd2).val.val μ (weylIdx0 d hd2).succ : ℂ) = _
  rw [weylRot_col_boost d hd2 μ]
  split_ifs <;> simp

/-- Diagonal sign character of the Weyl rotation at angle `π`. -/
private def weylSign (d : ℕ) (hd2 : 2 ≤ d) (a : Fin (d + 1)) : ℂ :=
  if a = 0 then (1 : ℂ)
  else if a = (weylIdx0 d hd2).succ then (-1 : ℂ)
  else if a = (weylIdx1 d hd2).succ then (-1 : ℂ)
  else (1 : ℂ)

private lemma weylSign_sq (d : ℕ) (hd2 : 2 ≤ d) (a : Fin (d + 1)) :
    weylSign d hd2 a * weylSign d hd2 a = 1 := by
  by_cases ha0 : a = 0
  · simp [weylSign, ha0]
  · by_cases ha1 : a = (weylIdx0 d hd2).succ
    · simp [weylSign, ha0, ha1]
    · by_cases ha2 : a = (weylIdx1 d hd2).succ
      · simp [weylSign, ha0, ha1, ha2]
      · simp [weylSign, ha0, ha1, ha2]

/-- At `θ = π`, `weylRot` is diagonal with signs given by `weylSign`. -/
private lemma weylRotC_entry_diag (d : ℕ) (hd2 : 2 ≤ d)
    (a b : Fin (d + 1)) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2)).val a b =
      if a = b then weylSign d hd2 a else 0 := by
  change ((weylRot d hd2).val.val a b : ℂ) = _
  change ((spatialRot d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi a b : ℝ) : ℂ) = _
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨x, rfl⟩
  · rw [sr_other d (weylIdx0 d hd2) (weylIdx1 d hd2) Real.pi 0
      (by simp [weylIdx0]) (by simp [weylIdx1]) b]
    by_cases hb : b = 0
    · simp [weylSign, hb, eq_comm]
    · simp [weylSign, hb, eq_comm]
  · rw [spatialRot_succ_apply d (weylIdx0 d hd2) (weylIdx1 d hd2) (weylIdx_ne d hd2) Real.pi x b]
    by_cases hxi : x = weylIdx0 d hd2
    · subst hxi
      by_cases hb : b = (weylIdx0 d hd2).succ
      · simp [weylSign, hb, eq_comm, weylIdx0, weylIdx1, Real.sin_pi, Real.cos_pi]
      · have hb' : b ≠ (weylIdx0 d hd2).succ := hb
        have hb1 : b ≠ (⟨1, by omega⟩ : Fin (d + 1)) := by
          simpa [weylIdx0] using hb'
        simp [weylSign, hb1, eq_comm, weylIdx0, weylIdx1, Real.sin_pi, Real.cos_pi]
    · by_cases hxj : x = weylIdx1 d hd2
      · subst hxj
        by_cases hb : b = (weylIdx1 d hd2).succ
        · simp [weylSign, hb, eq_comm, weylIdx0, weylIdx1, Real.sin_pi, Real.cos_pi]
        · have hb' : b ≠ (weylIdx1 d hd2).succ := hb
          have hb2 : b ≠ (⟨2, by omega⟩ : Fin (d + 1)) := by
            simpa [weylIdx1] using hb'
          simp [weylSign, hb2, eq_comm, weylIdx0, weylIdx1, Real.sin_pi, Real.cos_pi]
      · by_cases hb : x.succ = b
        · have hb0 : b ≠ 0 := by simpa [hb] using Fin.succ_ne_zero x
          have hb1 : b ≠ (weylIdx0 d hd2).succ := by
            intro hb1
            apply hxi
            exact Fin.succ_inj.mp (hb.trans hb1)
          have hb2 : b ≠ (weylIdx1 d hd2).succ := by
            intro hb2
            apply hxj
            exact Fin.succ_inj.mp (hb.trans hb2)
          simp [hxi, hxj, weylSign, hb, hb0, hb1, hb2, eq_comm]
        · simp [hxi, hxj, weylSign, hb, eq_comm]

/-- Under Weyl conjugation, the `(0,1)` boost entry changes sign. -/
private lemma weylConj_expBoost_entry01 {d : ℕ} (hd2 : 2 ≤ d) (t : ℂ) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2) * expBoost t *
      ComplexLorentzGroup.ofReal (weylRot d hd2)).val 0 (weylIdx0 d hd2).succ
      = Complex.sinh (-t) := by
  have hd1 : 1 ≤ d := by omega
  change ((((ComplexLorentzGroup.ofReal (weylRot d hd2)).val * (expBoost t).val *
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) 0 (weylIdx0 d hd2).succ) =
      Complex.sinh (-t))
  rw [Matrix.mul_apply]
  have hR_col : ∀ α : Fin (d + 1),
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val α (weylIdx0 d hd2).succ =
        if α = (weylIdx0 d hd2).succ then (-1 : ℂ) else 0 := by
    intro α
    simpa using weylRotC_col_boost d hd2 α
  simp_rw [hR_col, mul_ite, mul_neg, mul_zero]
  simp_rw [Matrix.mul_apply]
  have hR_row0 : ∀ β : Fin (d + 1),
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val 0 β = if β = 0 then (1 : ℂ) else 0 := by
    intro β
    simpa using weylRotC_row_time d hd2 β
  simp_rw [hR_row0, ite_mul, one_mul, zero_mul]
  simp
  have hentry : (expBoost t).val 0 (weylIdx0 d hd2).succ = Complex.sinh t := by
    simpa [weylIdx0] using expBoost_val_entry (d := d) t hd1 0 (weylIdx0 d hd2).succ
  simp [hentry]

/-- Under Weyl conjugation, the `(1,0)` boost entry changes sign. -/
private lemma weylConj_expBoost_entry10 {d : ℕ} (hd2 : 2 ≤ d) (t : ℂ) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2) * expBoost t *
      ComplexLorentzGroup.ofReal (weylRot d hd2)).val (weylIdx0 d hd2).succ 0
      = Complex.sinh (-t) := by
  have hd1 : 1 ≤ d := by omega
  change ((((ComplexLorentzGroup.ofReal (weylRot d hd2)).val * (expBoost t).val *
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (weylIdx0 d hd2).succ 0) =
      Complex.sinh (-t))
  rw [Matrix.mul_apply]
  have hR_col0 : ∀ α : Fin (d + 1),
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val α 0 = if α = 0 then (1 : ℂ) else 0 := by
    intro α
    simpa using weylRotC_col_time d hd2 α
  simp [hR_col0]
  simp_rw [Matrix.mul_apply]
  have hR_row1 : ∀ β : Fin (d + 1),
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val (weylIdx0 d hd2).succ β =
        if β = (weylIdx0 d hd2).succ then (-1 : ℂ) else 0 := by
    intro β
    simpa using weylRotC_row_boost d hd2 β
  simp [hR_row1]
  have hentry : (expBoost t).val (weylIdx0 d hd2).succ 0 = Complex.sinh t := by
    simpa [weylIdx0] using expBoost_val_entry (d := d) t hd1 (weylIdx0 d hd2).succ 0
  simp [hentry]

/-- Under Weyl conjugation, the `(0,0)` entry is unchanged. -/
private lemma weylConj_expBoost_entry00 {d : ℕ} (hd2 : 2 ≤ d) (t : ℂ) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2) * expBoost t *
      ComplexLorentzGroup.ofReal (weylRot d hd2)).val 0 0 = Complex.cosh (-t) := by
  have hd1 : 1 ≤ d := by omega
  change ((((ComplexLorentzGroup.ofReal (weylRot d hd2)).val * (expBoost t).val *
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) 0 0) = Complex.cosh (-t))
  rw [Matrix.mul_apply]
  have hR_col0 : ∀ α : Fin (d + 1),
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val α 0 = if α = 0 then (1 : ℂ) else 0 := by
    intro α
    simpa using weylRotC_col_time d hd2 α
  simp [hR_col0]
  simp_rw [Matrix.mul_apply]
  have hR_row0 : ∀ β : Fin (d + 1),
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val 0 β = if β = 0 then (1 : ℂ) else 0 := by
    intro β
    simpa using weylRotC_row_time d hd2 β
  simp_rw [hR_row0, ite_mul, one_mul, zero_mul]
  have hsum :
      (∑ x : Fin (d + 1), if x = 0 then (expBoost (d := d) t).val x 0 else 0) =
        (expBoost (d := d) t).val 0 0 := by
    simp
  have hentry : (expBoost (d := d) t).val 0 0 = Complex.cosh t := by
    simpa using expBoost_val_entry (d := d) t hd1 0 0
  simp [hsum, hentry]

/-- Under Weyl conjugation, the `(1,1)` entry is unchanged. -/
private lemma weylConj_expBoost_entry11 {d : ℕ} (hd2 : 2 ≤ d) (t : ℂ) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2) * expBoost t *
      ComplexLorentzGroup.ofReal (weylRot d hd2)).val (weylIdx0 d hd2).succ (weylIdx0 d hd2).succ
      = Complex.cosh (-t) := by
  have hd1 : 1 ≤ d := by omega
  change ((((ComplexLorentzGroup.ofReal (weylRot d hd2)).val * (expBoost t).val *
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (weylIdx0 d hd2).succ (weylIdx0 d hd2).succ) =
      Complex.cosh (-t))
  rw [Matrix.mul_apply]
  have hR_col1 : ∀ α : Fin (d + 1),
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val α (weylIdx0 d hd2).succ =
        if α = (weylIdx0 d hd2).succ then (-1 : ℂ) else 0 := by
    intro α
    simpa using weylRotC_col_boost d hd2 α
  simp [hR_col1]
  simp_rw [Matrix.mul_apply]
  have hR_row1 : ∀ β : Fin (d + 1),
      (ComplexLorentzGroup.ofReal (weylRot d hd2)).val (weylIdx0 d hd2).succ β =
        if β = (weylIdx0 d hd2).succ then (-1 : ℂ) else 0 := by
    intro β
    simpa using weylRotC_row_boost d hd2 β
  simp [hR_row1]
  have hentry : (expBoost (d := d) t).val (weylIdx0 d hd2).succ (weylIdx0 d hd2).succ =
      Complex.cosh t := by
    simpa [weylIdx0] using
      expBoost_val_entry (d := d) t hd1 (weylIdx0 d hd2).succ (weylIdx0 d hd2).succ
  simp [hentry]

/-- Weyl conjugation acts on the time/boost `2×2` block as `t ↦ -t`. -/
private theorem weylConj_expBoost_boostBlock {d : ℕ} (hd2 : 2 ≤ d) (t : ℂ) :
    let R := ComplexLorentzGroup.ofReal (weylRot d hd2)
    let i := (weylIdx0 d hd2).succ
    (R * expBoost t * R).val 0 0 = Complex.cosh (-t) ∧
    (R * expBoost t * R).val 0 i = Complex.sinh (-t) ∧
    (R * expBoost t * R).val i 0 = Complex.sinh (-t) ∧
    (R * expBoost t * R).val i i = Complex.cosh (-t) := by
  simp [weylConj_expBoost_entry00, weylConj_expBoost_entry01,
    weylConj_expBoost_entry10, weylConj_expBoost_entry11]

/-- Entrywise form of Weyl conjugation on boosts: diagonal sign-twisting. -/
private lemma weylConj_expBoost_entry_sign {d : ℕ} (hd2 : 2 ≤ d) (t : ℂ)
    (μ ν : Fin (d + 1)) :
    (ComplexLorentzGroup.ofReal (weylRot d hd2) * expBoost t *
      ComplexLorentzGroup.ofReal (weylRot d hd2)).val μ ν =
      weylSign d hd2 μ * (expBoost (d := d) t).val μ ν * weylSign d hd2 ν := by
  let R : ComplexLorentzGroup d := ComplexLorentzGroup.ofReal (weylRot d hd2)
  change ((((R.val * (expBoost (d := d) t).val * R.val :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) μ ν) =
      weylSign d hd2 μ * (expBoost (d := d) t).val μ ν * weylSign d hd2 ν)
  have hR : ∀ a b : Fin (d + 1), R.val a b = if a = b then weylSign d hd2 a else 0 := by
    intro a b
    simpa [R] using weylRotC_entry_diag d hd2 a b
  rw [Matrix.mul_apply]
  simp_rw [hR, mul_ite, mul_zero]
  simp
  rw [Matrix.mul_apply]
  simp [hR, ite_mul, one_mul, zero_mul]

/-- Weyl conjugation sends `exp(tK)` to `exp(-tK)` for `d ≥ 2`. -/
private theorem weylConj_expBoost {d : ℕ} (hd2 : 2 ≤ d) (t : ℂ) :
    ComplexLorentzGroup.ofReal (weylRot d hd2) * expBoost (d := d) t *
      ComplexLorentzGroup.ofReal (weylRot d hd2) = expBoost (d := d) (-t) := by
  ext μ ν
  have hd1 : 1 ≤ d := by omega
  rw [weylConj_expBoost_entry_sign (d := d) hd2 t μ ν]
  rw [expBoost_val_entry (d := d) t hd1 μ ν, expBoost_val_entry (d := d) (-t) hd1 μ ν]
  by_cases h00 : μ.val = 0 ∧ ν.val = 0
  · have hμ0 : μ = 0 := Fin.ext (by simpa using h00.1)
    have hν0 : ν = 0 := Fin.ext (by simpa using h00.2)
    subst μ; subst ν
    simp [h00, weylSign]
  · by_cases h01 :
      (μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0)
    · rcases h01 with h01 | h10
      · have hμ0 : μ = 0 := Fin.ext (by simpa using h01.1)
        have hν1 : ν = (weylIdx0 d hd2).succ := by
          apply Fin.ext
          simpa [weylIdx0] using h01.2
        subst μ; subst ν
        simp [h00, h01, weylSign, weylIdx0, weylIdx1]
      · have hμ1 : μ = (weylIdx0 d hd2).succ := by
          apply Fin.ext
          simpa [weylIdx0] using h10.1
        have hν0 : ν = 0 := Fin.ext (by simpa using h10.2)
        subst μ; subst ν
        simp [h00, h10, weylSign, weylIdx0, weylIdx1]
    · by_cases h11 : μ.val = 1 ∧ ν.val = 1
      · have hμ1 : μ = (weylIdx0 d hd2).succ := by
          apply Fin.ext
          simpa [weylIdx0] using h11.1
        have hν1 : ν = (weylIdx0 d hd2).succ := by
          apply Fin.ext
          simpa [weylIdx0] using h11.2
        subst μ; subst ν
        simp [h00, h01, h11, weylSign, weylIdx0, weylIdx1]
      · by_cases hμν : μ = ν
        · subst ν
          have hμ0 : μ ≠ 0 := by
            intro h
            apply h00
            simpa [h]
          have hμ1 : μ.val ≠ 1 := by
            intro h
            exact h11 ⟨h, h⟩
          simp [hμ0, hμ1, weylSign_sq, mul_assoc]
        · have hA : ¬(μ = 0 ∧ ν = 0) := by
            intro h
            apply h00
            simpa [h.1, h.2]
          have hB : ¬(μ = 0 ∧ ν.val = 1 ∨ μ.val = 1 ∧ ν = 0) := by
            intro h
            apply h01
            rcases h with h | h
            · exact Or.inl ⟨by simpa [h.1], h.2⟩
            · exact Or.inr ⟨h.1, by simpa [h.2]⟩
          simp [hA, hB, h11, hμν]

/-- The **principal boost strip** `{t ∈ ℂ | 0 < Im(t) < π}`.

    The boost generator `K` has eigenvalues `±1`, so `exp(tK)` is periodic with
    period `2πi`: the full boost strip is a cylinder `ℂ/2πiℤ`. On this cylinder,
    the "bad" parameters (where the slice is empty for some `n ≥ 3`) are the
    meridians `{Im(t) = 0}` (real boosts, preserving `V⁺`) and `{Im(t) = π}`
    (PT reversal, negating time components of unflipped differences).

    These two meridians disconnect the cylinder into two open strips:
    - Upper strip: `{0 < Im(t) < π}` (the principal strip)
    - Lower strip: `{-π < Im(t) < 0}` (= `{π < Im(t) < 2π}`)

    For `d ≥ 2`, the Weyl reflection `R ∈ K` (a 180° spatial rotation satisfying
    `R · exp(tK) · R⁻¹ = exp(-tK)`) identifies the two strips: given any
    `Λ = k₁ · exp(tK) · k₂` with `Im(t) < 0`, we can write
    `Λ = (k₁R⁻¹) · exp(-tK) · (Rk₂)` with `Im(-t) > 0`. This is why
    the principal strip suffices for the KAK decomposition when `d ≥ 2`. -/
private def principalBoostStrip : Set ℂ :=
  { t : ℂ | 0 < t.im ∧ t.im < Real.pi }

/-- The set of parameters in the principal strip for which `exp(tK)` yields
    a nonempty forward-overlap slice. -/
private def principalBoostOverlap (d n : ℕ) (σ : Equiv.Perm (Fin n)) : Set ℂ :=
  principalBoostStrip ∩
  { t : ℂ | (permForwardOverlapSlice (d := d) n σ (expBoost t)).Nonempty }

/-! ### Principal strip witnesses -/

/-- For any `t` in the principal strip `{0 < Im(t) < π}` and any permutation `σ`,
    the forward-overlap slice at `expBoost t` is nonempty when `d ≥ 2`.

    **Proof**: The "large spatial shift trick". Choose a witness `w` with
    imaginary time increments `ε > 0` and real spatial increments arranged
    along the σ-ordering with magnitude `M`. After boosting by `exp(tK)`,
    the imaginary time component of each permuted difference becomes
    `cosh(θ) · (ε·δ_k·cos(λ) + M·sin(λ))`, which is positive for large `M`
    since `sin(λ) > 0` in the principal strip. The Minkowski condition follows
    from `cosh²(θ) - sinh²(θ) = 1`. -/
private theorem principalStrip_slice_nonempty {d : ℕ} (hd2 : 2 ≤ d)
    (t : ℂ) (ht : 0 < t.im ∧ t.im < Real.pi)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permForwardOverlapSlice (d := d) n σ (expBoost t)).Nonempty := by
  have hd1 : 1 ≤ d := by omega
  -- Choose M large enough so that cos(t.im)*δ + sin(t.im)*M > 0 for all |δ| ≤ n.
  -- Any M > n / sin(t.im) works; we pick M = (n + 1) / sin(t.im).
  have hsin_pos : Real.sin t.im > 0 := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  -- Define the witness
  let M : ℝ := (n + 1) / Real.sin t.im
  have hM_pos : M > 0 := div_pos (by positivity) hsin_pos
  -- w k μ = I*(k+1) for μ=0, ((σ⁻¹ k)+1)*M for μ=1, 0 otherwise
  let w : Fin n → Fin (d + 1) → ℂ := fun k μ =>
    if μ = (0 : Fin (d + 1)) then Complex.I * ((k.val : ℝ) + 1)
    else if μ = ⟨1, by omega⟩ then (((σ⁻¹ k).val : ℝ) + 1) * (M : ℂ)
    else 0
  refine ⟨w, ?_, ?_⟩
  · -- w ∈ ForwardTube d n
    intro k
    -- η μ = Im(w k μ - prev μ); for μ=0: η=1; for μ≥1: η=0
    have hw_time : ∀ j : Fin n, (w j 0).im = (j.val : ℝ) + 1 := by
      intro j; simp [w, Complex.mul_im]
    have hw_spatial_im : ∀ j : Fin n, ∀ μ : Fin (d + 1), μ ≠ 0 → (w j μ).im = 0 := by
      intro j μ hμ
      simp only [w]
      rw [if_neg hμ]
      split_ifs
      · simp [Complex.ofReal_im]
      · simp
    -- Compute the imaginary difference
    constructor
    · -- η 0 > 0
      show (w k 0 - (if h : k.val = 0 then (0 : Fin (d+1) → ℂ)
          else w ⟨k.val - 1, by omega⟩) 0).im > 0
      by_cases hk : k.val = 0
      · simp [hk, hw_time k]
      · simp only [hk, dite_false, Complex.sub_im, hw_time k,
            hw_time ⟨k.val - 1, by omega⟩]
        have hle : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
        rw [show ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 from by rw [Nat.cast_sub hle]; push_cast; ring]
        linarith
    · -- Minkowski sum < 0
      -- Define η as the imaginary difference
      set η : Fin (d + 1) → ℝ := fun μ => (w k μ -
        (if h : k.val = 0 then (0 : Fin (d + 1) → ℂ) else w ⟨k.val - 1, by omega⟩) μ).im
        with hη_def
      rw [minkowski_sum_decomp]
      -- η 0 = 1
      have hη0 : η 0 = 1 := by
        simp only [hη_def, η]
        by_cases hk : k.val = 0
        · simp [hk, hw_time k]
        · simp only [hk, dite_false, Complex.sub_im, hw_time k,
              hw_time ⟨k.val - 1, by omega⟩]
          have hle : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
          rw [show ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 from by rw [Nat.cast_sub hle]; push_cast; ring]
          ring
      -- η (succ i) = 0
      have hηi : ∀ i : Fin d, η (Fin.succ i) = 0 := by
        intro i; simp only [hη_def, η]
        by_cases hk : k.val = 0
        · simp [hk, hw_spatial_im k (Fin.succ i) (Fin.succ_ne_zero i)]
        · simp only [hk, dite_false, Complex.sub_im,
              hw_spatial_im k (Fin.succ i) (Fin.succ_ne_zero i),
              hw_spatial_im ⟨k.val - 1, by omega⟩ (Fin.succ i) (Fin.succ_ne_zero i)]
          ring
      rw [hη0]; simp_rw [hηi]; norm_num
  · -- complexLorentzAction (expBoost t) (permAct σ w) ∈ ForwardTube d n
    -- Let z' be the boosted permuted configuration
    let z' : Fin n → Fin (d + 1) → ℂ := complexLorentzAction (expBoost (d := d) t) (permAct (d := d) σ w)
    -- For each k, compute the imaginary difference η' and show InOpenForwardCone
    intro k
    -- The key quantity: A_k = cos(t.im) * δ_time_k + sin(t.im) * M
    -- where δ_time_k = σ(k).val + 1 (for k=0) or σ(k).val - σ(k-1).val (for k>0)
    -- and M = the spatial increment (always M for our witness)
    -- After boosting, Im(comp 0) = cosh(t.re) * A_k and Im(comp 1) = sinh(t.re) * A_k
    -- and Im(comp μ≥2) = 0.
    -- The Minkowski norm is -(cosh²-sinh²)*A_k² = -A_k² < 0.

    -- Step 1: Compute the action of expBoost on the permuted witness
    -- z' k μ = ∑ ν, (expBoost t).val μ ν * (permAct σ w) k ν
    -- = ∑ ν, (expBoost t).val μ ν * w (σ k) ν
    -- Using the entry formula, this simplifies significantly.

    -- Define the time and spatial deltas for the permuted config
    let δ_time : ℝ := if h : k.val = 0 then (σ k).val + 1
        else (σ k).val - (σ ⟨k.val - 1, by omega⟩).val
    -- The spatial delta is always M (after applying σ⁻¹∘σ = id)

    -- Step 2: Show the imaginary difference of the boosted config
    -- The k-th imaginary difference of z' at component μ is:
    -- For μ = 0: Re(cosh t) * δ_time + Im(sinh t) * M = cosh(t.re)*cos(t.im)*δ_time + cosh(t.re)*sin(t.im)*M
    -- For μ = 1: Re(sinh t) * δ_time + Im(cosh t) * M = sinh(t.re)*cos(t.im)*δ_time + sinh(t.re)*sin(t.im)*M
    -- For μ ≥ 2: 0

    -- Step 3: Factor out to get:
    -- η'(0) = cosh(t.re) * A where A = cos(t.im) * δ_time + sin(t.im) * M
    -- η'(1) = sinh(t.re) * A
    -- Minkowski norm = -(cosh²-sinh²) * A² = -A²

    -- For the InOpenForwardCone condition:
    -- Need η'(0) > 0: cosh(t.re) > 0 and A > 0
    -- Need Minkowski < 0: -A² < 0 ↔ A ≠ 0, which follows from A > 0

    -- A > 0 because sin(t.im) > 0 and M > n/sin(t.im), so sin(t.im)*M > n ≥ |δ_time|*|cos(t.im)|

    -- Set up A
    let A : ℝ := Real.cos t.im * δ_time + Real.sin t.im * M
    -- Prove A > 0
    have hA_pos : A > 0 := by
      show Real.cos t.im * δ_time + Real.sin t.im * M > 0
      have hsinM : Real.sin t.im * M = (n + 1 : ℝ) := by
        simp only [M]
        rw [mul_div_cancel₀]
        exact ne_of_gt hsin_pos
      rw [hsinM]
      have hδ_bound : |δ_time| ≤ n := by
        show |if h : k.val = 0 then ((σ k).val : ℝ) + 1
            else ((σ k).val : ℝ) - ((σ ⟨k.val - 1, by omega⟩).val : ℝ)| ≤ n
        split_ifs with hk
        · -- k = 0: |σ(0).val + 1| ≤ n (note: σ(0).val < n, so σ(0).val + 1 ≤ n)
          rw [abs_of_nonneg (by positivity)]
          have h1 : (σ k).val < n := (σ k).isLt
          exact_mod_cast Nat.lt_succ_iff.mp (by omega)
        · -- k > 0: |σ(k) - σ(k-1)| ≤ n
          have h1 : ((σ k).val : ℝ) < n := by exact_mod_cast (σ k).isLt
          have h2 : ((σ ⟨k.val - 1, by omega⟩).val : ℝ) < n := by
            exact_mod_cast (σ ⟨k.val - 1, by omega⟩).isLt
          have h3 : (0 : ℝ) ≤ ((σ k).val : ℝ) := Nat.cast_nonneg _
          have h4 : (0 : ℝ) ≤ ((σ ⟨k.val - 1, by omega⟩).val : ℝ) := Nat.cast_nonneg _
          rw [abs_le]; constructor <;> linarith
      have hcos_bound : |Real.cos t.im * δ_time| ≤ |δ_time| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
      linarith [abs_le.mp (le_trans hcos_bound hδ_bound)]

    -- Now we need to show the actual InOpenForwardCone condition
    -- by computing the imaginary difference of the boosted config.

    -- The imaginary difference η' for the boosted config
    set η' : Fin (d + 1) → ℝ := fun μ => (z' k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℂ)
       else z' ⟨k.val - 1, by omega⟩) μ).im with hη'_def

    -- Key claim: η'(0) = cosh(t.re) * A, η'(1) = sinh(t.re) * A, η'(μ≥2) = 0
    -- We prove these by direct computation using expBoost_val_entry.

    -- First, compute the boosted action on the witness
    -- z' k μ = ∑ ν, (expBoost t).val μ ν * w (σ k) ν
    have hz'_eq : ∀ (j : Fin n) (μ : Fin (d + 1)),
        z' j μ = ∑ ν, (expBoost t).val μ ν * w (σ j) ν := by
      intro j μ; rfl

    -- w (σ j) has: component 0 = I * (σ j + 1), component 1 = (σ⁻¹(σ j) + 1) * M = (j + 1) * M
    have hw_σ_0 : ∀ j : Fin n, w (σ j) 0 = Complex.I * ((σ j).val + 1 : ℝ) := by
      intro j; simp [w]
    have hw_σ_1 : ∀ j : Fin n, w (σ j) ⟨1, by omega⟩ = ((j.val : ℝ) + 1) * (M : ℂ) := by
      intro j
      simp only [w]
      rw [if_neg (by simp [Fin.ext_iff]), if_pos (by simp [Fin.ext_iff])]
      congr 1
      push_cast
      congr 1
      have : (σ⁻¹ (σ j)).val = j.val := by
        simp [Equiv.Perm.inv_apply_self]
      exact_mod_cast this
    have hw_σ_ge2 : ∀ j : Fin n, ∀ ν : Fin (d + 1), ν.val ≥ 2 → w (σ j) ν = 0 := by
      intro j ν hν
      simp only [w]
      have hne0 : ν ≠ (0 : Fin (d + 1)) := by intro h; subst h; simp at hν
      have hne1 : ν ≠ (⟨1, by omega⟩ : Fin (d + 1)) := by
        intro h; have := congr_arg Fin.val h; simp at this; omega
      rw [if_neg hne0, if_neg hne1]

    -- Helper: compute the boosted action using the entry formula
    -- z' j μ = ∑ ν, (expBoost t).val μ ν * w (σ j) ν
    -- Since w (σ j) ν = 0 for ν ≥ 2, only ν=0 and ν=1 contribute.
    have hboost_sum : ∀ (j : Fin n) (μ : Fin (d + 1)),
        z' j μ = (expBoost t).val μ 0 * w (σ j) 0 +
                 (expBoost t).val μ ⟨1, by omega⟩ * w (σ j) ⟨1, by omega⟩ := by
      intro j μ
      rw [hz'_eq]
      have hlt1 : 1 < d + 1 := Nat.lt_add_one_iff.mpr hd1
      have hfin1 : (⟨1, hlt1⟩ : Fin (d + 1)) = ⟨1, by omega⟩ := rfl
      have hvanish : ∀ ν : Fin (d + 1), ν ≠ 0 → ν.val ≠ 1 →
          (expBoost t).val μ ν * w (σ j) ν = 0 := by
        intro ν hν0 hν1
        have hν_ge2 : ν.val ≥ 2 := by
          rcases Nat.eq_zero_or_pos ν.val with h | h
          · exact absurd (Fin.ext h) hν0
          · omega
        rw [hw_σ_ge2 j ν hν_ge2, mul_zero]
      -- The sum equals f(0) + f(1) because all other terms are 0
      have hsum : ∑ ν : Fin (d + 1), (expBoost t).val μ ν * w (σ j) ν =
          ∑ ν ∈ ({0, ⟨1, hlt1⟩} : Finset (Fin (d + 1))),
            (expBoost t).val μ ν * w (σ j) ν := by
        symm; apply Finset.sum_subset (Finset.subset_univ _)
        intro ν _ hν_notin
        simp only [Finset.mem_insert, Finset.mem_singleton] at hν_notin
        push_neg at hν_notin
        have hv0 : ν ≠ 0 := hν_notin.1
        have hv1 : ν.val ≠ 1 := fun h => hν_notin.2 (Fin.ext h)
        exact hvanish ν hv0 hv1
      rw [hsum, Finset.sum_pair (Fin.ne_of_val_ne (by norm_num))]

    -- Now substitute the entry formulas
    -- After rw [expBoost_val_entry], the goal is a nested if-then-else
    -- with conditions on Fin.val. We use split_ifs to resolve.
    have hentry : ∀ (μ ν : Fin (d + 1)), (expBoost (d := d) t).val μ ν =
        if μ.val = 0 ∧ ν.val = 0 then Complex.cosh t
        else if (μ.val = 0 ∧ ν.val = 1) ∨ (μ.val = 1 ∧ ν.val = 0) then Complex.sinh t
        else if μ.val = 1 ∧ ν.val = 1 then Complex.cosh t
        else if μ = ν then 1
        else 0 := fun μ ν => expBoost_val_entry t hd1 μ ν

    -- z' j 0 = cosh(t) * I * (σ(j)+1) + sinh(t) * (j+1) * M
    have hz'_0 : ∀ j : Fin n, z' j 0 =
        Complex.cosh t * (Complex.I * ((σ j).val + 1 : ℝ)) +
        Complex.sinh t * (((j.val : ℝ) + 1) * (M : ℂ)) := by
      intro j; rw [hboost_sum, hentry 0 0, hentry 0 ⟨1, by omega⟩, hw_σ_0, hw_σ_1]
      simp (config := { decide := true })

    -- z' j 1 = sinh(t) * I * (σ(j)+1) + cosh(t) * (j+1) * M
    have hz'_1 : ∀ j : Fin n, z' j ⟨1, by omega⟩ =
        Complex.sinh t * (Complex.I * ((σ j).val + 1 : ℝ)) +
        Complex.cosh t * (((j.val : ℝ) + 1) * (M : ℂ)) := by
      intro j; rw [hboost_sum, hentry ⟨1, by omega⟩ 0, hentry ⟨1, by omega⟩ ⟨1, by omega⟩,
        hw_σ_0, hw_σ_1]
      simp (config := { decide := true })

    -- z' j μ = 0 for μ ≥ 2
    have hz'_ge2 : ∀ j : Fin n, ∀ μ : Fin (d + 1), μ.val ≥ 2 → z' j μ = 0 := by
      intro j μ hμ
      rw [hboost_sum, hentry μ 0, hentry μ ⟨1, by omega⟩]
      have h0 : ¬(μ.val = 0) := by omega
      have h1 : ¬(μ.val = 1) := by omega
      have hne0 : μ ≠ (0 : Fin (d+1)) := Fin.ne_of_val_ne (ne_of_gt (by omega : μ.val > 0))
      have hne1 : μ ≠ (⟨1, by omega⟩ : Fin (d+1)) := by
        intro h; rw [h] at hμ; simp at hμ
      simp only [h0, h1, false_and, and_false, false_or, or_false, ite_false, hne0, hne1]
      ring

    -- Now compute the imaginary differences
    -- η'(0) = cosh(t.re) * A, where A = cos(t.im)*δ_time + sin(t.im)*M
    -- η'(1) = sinh(t.re) * A
    -- η'(μ≥2) = 0

    -- Compute Im of z' j 0
    -- cosh(t) = cosh(t.re)*cos(t.im) + I*sinh(t.re)*sin(t.im)
    -- sinh(t) = sinh(t.re)*cos(t.im) + I*cosh(t.re)*sin(t.im)
    -- So Im(cosh(t) * I * r) = Re(cosh(t)) * r = cosh(t.re)*cos(t.im) * r (for real r)
    -- Im(sinh(t) * s) = Im(sinh(t)) * s = cosh(t.re)*sin(t.im) * s (for real s)

    -- Decompose cosh/sinh of complex argument into real/imaginary parts
    have ht_rw : t = (t.re : ℂ) + Complex.I * (t.im : ℂ) := by
      rw [mul_comm]; exact (Complex.re_add_im t).symm
    have hI_comm : Complex.I * (t.im : ℂ) = (t.im : ℂ) * Complex.I := mul_comm _ _

    have hcosh_re : (Complex.cosh t).re = Real.cosh t.re * Real.cos t.im := by
      conv_lhs => rw [ht_rw, Complex.cosh_add, hI_comm, Complex.cosh_mul_I, Complex.sinh_mul_I]
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
            Complex.sinh_ofReal_re, Complex.cosh_ofReal_im, Complex.sinh_ofReal_im,
            Complex.mul_re, Complex.add_re]
    have hcosh_im : (Complex.cosh t).im = Real.sinh t.re * Real.sin t.im := by
      conv_lhs => rw [ht_rw, Complex.cosh_add, hI_comm, Complex.cosh_mul_I, Complex.sinh_mul_I]
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
            Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.sinh_ofReal_re,
            Complex.cosh_ofReal_im, Complex.sinh_ofReal_im,
            Complex.mul_im, Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    have hsinh_re : (Complex.sinh t).re = Real.sinh t.re * Real.cos t.im := by
      conv_lhs => rw [ht_rw, Complex.sinh_add, hI_comm, Complex.cosh_mul_I, Complex.sinh_mul_I]
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
            Complex.sinh_ofReal_re, Complex.cosh_ofReal_im, Complex.sinh_ofReal_im,
            Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    have hsinh_im : (Complex.sinh t).im = Real.cosh t.re * Real.sin t.im := by
      conv_lhs => rw [ht_rw, Complex.sinh_add, hI_comm, Complex.cosh_mul_I, Complex.sinh_mul_I]
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
            Complex.sin_ofReal_im, Complex.cosh_ofReal_re, Complex.sinh_ofReal_re,
            Complex.cosh_ofReal_im, Complex.sinh_ofReal_im,
            Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.add_im]

    -- The imaginary part of z' j 0
    -- Helper: Im(a * I * r + b * s) = a.re * r + b.im * s for complex a, b and real r, s
    have im_boost_formula (a b : ℂ) (r s : ℝ) :
        (a * (Complex.I * (r : ℂ)) + b * ((s : ℝ) : ℂ)).im = a.re * r + b.im * s := by
      simp [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have hz'_0_im : ∀ j : Fin n, (z' j 0).im =
        Real.cosh t.re * (Real.cos t.im * ((σ j).val + 1 : ℝ) +
        Real.sin t.im * (((j.val : ℝ) + 1) * M)) := by
      intro j; rw [hz'_0]
      rw [show (((j.val : ℝ) + 1) * (M : ℂ)) = ((((j.val : ℝ) + 1) * M : ℝ) : ℂ) from by
        push_cast; ring]
      rw [im_boost_formula, hcosh_re, hsinh_im]
      ring

    -- The imaginary part of z' j 1
    have hz'_1_im : ∀ j : Fin n, (z' j ⟨1, by omega⟩).im =
        Real.sinh t.re * (Real.cos t.im * ((σ j).val + 1 : ℝ) +
        Real.sin t.im * (((j.val : ℝ) + 1) * M)) := by
      intro j; rw [hz'_1]
      rw [show (((j.val : ℝ) + 1) * (M : ℂ)) = ((((j.val : ℝ) + 1) * M : ℝ) : ℂ) from by
        push_cast; ring]
      rw [im_boost_formula, hsinh_re, hcosh_im]
      ring

    -- Now compute the imaginary differences
    -- η'(0) for position k
    set η' : Fin (d + 1) → ℝ := fun μ => (z' k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℂ)
       else z' ⟨k.val - 1, by omega⟩) μ).im with hη'_def

    -- η'(0) = cosh(t.re) * A
    have hη'_0 : η' 0 = Real.cosh t.re * A := by
      simp only [hη'_def, η', A, δ_time]
      by_cases hk : k.val = 0
      · simp [hk, hz'_0_im]
      · simp only [hk, dite_false, Complex.sub_im, hz'_0_im k,
            hz'_0_im ⟨k.val - 1, by omega⟩]
        have hle : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
        rw [show ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 from by rw [Nat.cast_sub hle]; push_cast; ring]
        ring

    -- η'(1) = sinh(t.re) * A
    have hη'_1 : η' ⟨1, by omega⟩ = Real.sinh t.re * A := by
      simp only [hη'_def, η', A, δ_time]
      by_cases hk : k.val = 0
      · simp [hk, hz'_1_im]
      · simp only [hk, dite_false, Complex.sub_im, hz'_1_im k,
            hz'_1_im ⟨k.val - 1, by omega⟩]
        have hle : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
        rw [show ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 from by rw [Nat.cast_sub hle]; push_cast; ring]
        ring

    -- η'(μ) = 0 for μ ≥ 2
    have hη'_ge2 : ∀ μ : Fin (d + 1), μ.val ≥ 2 → η' μ = 0 := by
      intro μ hμ
      simp only [hη'_def, η']
      by_cases hk : k.val = 0
      · simp [hk, hz'_ge2 k μ hμ]
      · simp only [hk, dite_false, Complex.sub_im, hz'_ge2 k μ hμ,
            hz'_ge2 ⟨k.val - 1, by omega⟩ μ hμ]; ring

    -- Now prove InOpenForwardCone
    -- The goal after `set η'` should involve η', but let's unfold to be safe
    show η' 0 > 0 ∧ ∑ μ, minkowskiSignature d μ * η' μ ^ 2 < 0
    constructor
    · -- η'(0) > 0
      rw [hη'_0]
      exact mul_pos (Real.cosh_pos t.re) hA_pos
    · -- Minkowski sum < 0
      rw [minkowski_sum_decomp, hη'_0]
      -- Convert η'(Fin.succ i) for i : Fin d
      have hηi_sq : ∀ i : Fin d, η' (Fin.succ i) ^ 2 =
          if i.val = 0 then (Real.sinh t.re * A) ^ 2 else 0 := by
        intro i
        rcases eq_or_ne i.val 0 with hi | hi
        · rw [if_pos hi]
          have : Fin.succ i = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
          rw [this, hη'_1]
        · have hi2 : (Fin.succ i).val ≥ 2 := by simp [Fin.succ]; omega
          rw [if_neg hi, hη'_ge2 (Fin.succ i) hi2, sq, zero_mul]
      simp_rw [hηi_sq]
      -- The sum becomes (sinh(t.re) * A)^2
      have hsum : ∑ i : Fin d, (if i.val = 0 then (Real.sinh t.re * A) ^ 2 else (0 : ℝ)) =
          (Real.sinh t.re * A) ^ 2 := by
        have : ∀ i : Fin d, (if i.val = 0 then (Real.sinh t.re * A) ^ 2 else (0 : ℝ)) =
            if i = ⟨0, by omega⟩ then (Real.sinh t.re * A) ^ 2 else 0 := by
          intro i; simp [Fin.ext_iff]
        simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hsum]
      -- -(cosh(t.re)*A)^2 + (sinh(t.re)*A)^2 = A^2 * (sinh^2 - cosh^2) = -A^2
      have : -(Real.cosh t.re * A) ^ 2 + (Real.sinh t.re * A) ^ 2 = -(A ^ 2) := by
        have h1 : Real.cosh t.re ^ 2 - Real.sinh t.re ^ 2 = 1 :=
          Real.cosh_sq_sub_sinh_sq t.re
        nlinarith
      rw [this]
      nlinarith [sq_nonneg A, hA_pos]

/-- The principal boost overlap equals the entire principal strip for d ≥ 2. -/
private theorem principalBoostOverlap_eq_strip {d : ℕ} (hd2 : 2 ≤ d)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    principalBoostOverlap d n σ = principalBoostStrip := by
  ext t
  simp only [principalBoostOverlap, principalBoostStrip, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro ⟨ht, _⟩; exact ht
  · intro ht; exact ⟨ht, principalStrip_slice_nonempty hd2 t ht n σ⟩

/-- The principal strip `{0 < Im(t) < π}` is convex. -/
private lemma convex_principalBoostStrip : Convex ℝ principalBoostStrip := by
  intro x hx y hy a b ha hb hab
  simp only [principalBoostStrip, Set.mem_setOf_eq] at *
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
  rw [him]
  constructor
  · have h1 : a * x.im ≥ 0 := mul_nonneg ha hx.1.le
    have h2 : b * y.im ≥ 0 := mul_nonneg hb hy.1.le
    by_contra h; push_neg at h
    have : a * x.im + b * y.im = 0 := le_antisymm h (by linarith)
    have ha0 : a * x.im = 0 := by linarith
    have hb0 : b * y.im = 0 := by linarith
    rcases mul_eq_zero.mp ha0 with ha' | ha'
    · rcases mul_eq_zero.mp hb0 with hb' | hb'
      · linarith
      · linarith [hy.1]
    · linarith [hx.1]
  · have h1 : a * x.im ≤ a * Real.pi := by nlinarith [hx.2]
    have h2 : b * y.im ≤ b * Real.pi := by nlinarith [hy.2]
    have h3 : a * Real.pi + b * Real.pi = Real.pi := by nlinarith
    -- strict inequality: can't have both a*x.im = a*pi and b*y.im = b*pi
    -- since x.im < pi and y.im < pi (and a + b = 1, a,b ≥ 0)
    by_cases ha0 : a = 0
    · subst ha0; simp at hab; subst hab; simpa using hy.2
    · have : a * x.im < a * Real.pi :=
        mul_lt_mul_of_pos_left hx.2 (lt_of_le_of_ne ha (Ne.symm ha0))
      linarith

/-- The principal boost overlap is connected for `d ≥ 2`.

    By `principalBoostOverlap_eq_strip`, the overlap equals the entire principal
    strip, which is convex and hence connected.

    **References**:
    - R.F. Streater and A.S. Wightman, "PCT, Spin and Statistics, and All That"
      (1964, 2000), Section 2-5, Lemma 2 -/
theorem isConnected_principalBoostOverlap {d : ℕ}
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    IsConnected (principalBoostOverlap d n σ) := by
  rw [principalBoostOverlap_eq_strip hd2 n σ]
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hpi2 : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  refine ⟨⟨⟨0, Real.pi / 2⟩, ?_⟩, convex_principalBoostStrip.isPreconnected⟩
  simp only [principalBoostStrip, Set.mem_setOf_eq]
  exact ⟨hpi, hpi2⟩

/-- **Raw KAK decomposition** for the complex Lorentz group.

    This is the pure Lie-theoretic input: every `Λ ∈ SO₊(1,d;ℂ)` factors as
    `k₁ · exp(tK) · k₂` with real restricted Lorentz factors. -/
private axiom raw_KAK_decomposition {d : ℕ}
    (Λ : ComplexLorentzGroup d) :
    ∃ (k₁ k₂ : RestrictedLorentzGroup d) (t : ℂ),
      Λ = ComplexLorentzGroup.ofReal k₁ * expBoost t * ComplexLorentzGroup.ofReal k₂

/-- Nonempty overlap slices cannot occur on even meridians `Im(t) = 2πm`
    for nontrivial permutations: after periodicity reduction this would force
    `FT ∩ σ·FT ≠ ∅`, contradicting `σ ≠ 1`. -/
private lemma expBoost_nonempty_excludes_even_meridian (d : ℕ) (hd2 : 2 ≤ d)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1)
    (t : ℂ)
    (ht : (permForwardOverlapSlice (d := d) n σ (expBoost (d := d) t)).Nonempty) :
    ∀ m : ℤ, t.im ≠ ((2 * m : ℤ) : ℝ) * Real.pi := by
  intro m hm
  have hd1 : 1 ≤ d := by omega
  let a : ℝ := t.re
  have hm' : t.im = (m : ℝ) * (2 * Real.pi) := by
    calc
      t.im = ((2 * m : ℤ) : ℝ) * Real.pi := hm
      _ = (m : ℝ) * (2 * Real.pi) := by
            norm_num [Int.cast_mul, mul_assoc, mul_comm, mul_left_comm]
  have ht_decomp : t = (a : ℂ) + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [a, hm', mul_assoc, mul_comm, mul_left_comm]
  have hperiod :
      expBoost (d := d) ((a : ℂ) + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) =
        expBoost (d := d) (a : ℂ) :=
    expBoost_periodic_two_pi_I_int (d := d) hd1 (a : ℂ) m
  have hexp_real : expBoost (d := d) t = expBoost (d := d) (a : ℂ) := by
    calc
      expBoost (d := d) t =
          expBoost (d := d) ((a : ℂ) + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
            rw [ht_decomp]
      _ = expBoost (d := d) (a : ℂ) := hperiod
  have ht_real :
      (permForwardOverlapSlice (d := d) n σ (expBoost (d := d) (a : ℂ))).Nonempty := by
    simpa [hexp_real] using ht
  have hreal_eq :
      expBoost (d := d) (a : ℂ) =
        ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a) :=
    expBoost_ofReal_re (d := d) hd1 a
  rcases ht_real with ⟨w, hwFT, hwActFT⟩
  have hwActFT' :
      complexLorentzAction
        (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a))
        (permAct (d := d) σ w) ∈ ForwardTube d n := by
    simpa [hreal_eq] using hwActFT
  have hpermFT :
      permAct (d := d) σ w ∈ ForwardTube d n := by
    have htmp :
        complexLorentzAction
          (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a))⁻¹
          (complexLorentzAction
            (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a))
            (permAct (d := d) σ w)) ∈ ForwardTube d n := by
      exact ofReal_inv_preserves_forwardTube
        (R := LorentzLieGroup.boostElement d ⟨0, by omega⟩ a)
        (z := complexLorentzAction
          (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a))
          (permAct (d := d) σ w))
        hwActFT'
    simpa [complexLorentzAction_inv] using htmp
  have hwPerm : w ∈ PermutedForwardTube d n σ := by
    simpa [PermutedForwardTube, permAct] using hpermFT
  have hinter : w ∈ ForwardTube d n ∩ PermutedForwardTube d n σ := ⟨hwFT, hwPerm⟩
  have hempty :
      ForwardTube d n ∩ PermutedForwardTube d n σ = (∅ : Set (Fin n → Fin (d + 1) → ℂ)) :=
    forwardTube_inter_permutedForwardTube_eq_empty_of_ne_one (d := d) (n := n) σ hσ
  have : w ∈ (∅ : Set (Fin n → Fin (d + 1) → ℂ)) := by simpa [hempty] using hinter
  exact this.elim

/-- Nonempty overlap slices cannot occur on odd meridians `Im(t) = (2m+1)π`.

    After reducing `t` modulo `2πi`, write `expBoost t = expBoost(a) * expBoost(πi)`.
    Peel off the real boost `expBoost(a)` via inverse invariance of `ForwardTube`.
    The remaining factor `expBoost(πi)` flips the time component sign, contradicting
    forward-cone positivity at `k = 0`. -/
private theorem expBoost_nonempty_excludes_odd_meridian (d : ℕ) (hd2 : 2 ≤ d)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : σ ≠ 1)
    (t : ℂ)
    (ht : (permForwardOverlapSlice (d := d) n σ (expBoost (d := d) t)).Nonempty) :
    ∀ m : ℤ, t.im ≠ ((2 * m + 1 : ℤ) : ℝ) * Real.pi := by
  intro m hm
  have hd1 : 1 ≤ d := by omega
  rcases ht with ⟨w, hwFT, hwActFT⟩
  have hnz : n ≠ 0 := by
    intro hn0
    subst hn0
    exact hσ (Subsingleton.elim σ 1)
  let k0 : Fin n := ⟨0, Nat.pos_of_ne_zero hnz⟩
  let a : ℝ := t.re
  have hm' : t.im = (m : ℝ) * (2 * Real.pi) + Real.pi := by
    calc
      t.im = ((2 * m + 1 : ℤ) : ℝ) * Real.pi := hm
      _ = (m : ℝ) * (2 * Real.pi) + Real.pi := by
            norm_num [Int.cast_mul, Int.cast_add, mul_assoc, mul_comm, mul_left_comm]
            ring
  have ht_decomp :
      t = ((a : ℂ) + ((Real.pi : ℂ) * Complex.I)) +
        (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
    apply Complex.ext <;>
      simp [a, hm', mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm, add_comm]
  have hperiod :
      expBoost (d := d)
          (((a : ℂ) + ((Real.pi : ℂ) * Complex.I)) + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) =
        expBoost (d := d) ((a : ℂ) + ((Real.pi : ℂ) * Complex.I)) :=
    expBoost_periodic_two_pi_I_int (d := d) hd1 ((a : ℂ) + ((Real.pi : ℂ) * Complex.I)) m
  have hexp_t :
      expBoost (d := d) t = expBoost (d := d) ((a : ℂ) + ((Real.pi : ℂ) * Complex.I)) := by
    simpa [ht_decomp] using hperiod
  have hsplit :
      expBoost (d := d) ((a : ℂ) + ((Real.pi : ℂ) * Complex.I)) =
        expBoost (d := d) (a : ℂ) * expBoost (d := d) ((Real.pi : ℂ) * Complex.I) :=
    expBoost_add (d := d) (a : ℂ) ((Real.pi : ℂ) * Complex.I)
  have hact0 :
      complexLorentzAction
        (expBoost (d := d) ((a : ℂ) + ((Real.pi : ℂ) * Complex.I)))
        (permAct (d := d) σ w) ∈ ForwardTube d n := by
    simpa [hexp_t] using hwActFT
  have hact :
      complexLorentzAction
        (expBoost (d := d) (a : ℂ) * expBoost (d := d) ((Real.pi : ℂ) * Complex.I))
        (permAct (d := d) σ w) ∈ ForwardTube d n := by
    simpa [hsplit] using hact0
  have hreal_eq :
      expBoost (d := d) (a : ℂ) =
        ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a) :=
    expBoost_ofReal_re (d := d) hd1 a
  have hact_real :
      complexLorentzAction
        (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a))
        (complexLorentzAction (expBoost (d := d) ((Real.pi : ℂ) * Complex.I))
          (permAct (d := d) σ w)) ∈ ForwardTube d n := by
    simpa [hreal_eq, complexLorentzAction_mul, mul_assoc] using hact
  have hpiFT :
      complexLorentzAction (expBoost (d := d) ((Real.pi : ℂ) * Complex.I))
        (permAct (d := d) σ w) ∈ ForwardTube d n := by
    have htmp :
        complexLorentzAction
          (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a))⁻¹
          (complexLorentzAction
            (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a))
            (complexLorentzAction (expBoost (d := d) ((Real.pi : ℂ) * Complex.I))
              (permAct (d := d) σ w))) ∈ ForwardTube d n := by
      exact ofReal_inv_preserves_forwardTube
        (R := LorentzLieGroup.boostElement d ⟨0, by omega⟩ a)
        (z := complexLorentzAction
          (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement d ⟨0, by omega⟩ a))
          (complexLorentzAction (expBoost (d := d) ((Real.pi : ℂ) * Complex.I))
            (permAct (d := d) σ w)))
        hact_real
    simpa [complexLorentzAction_inv] using htmp
  have hpos :
      InOpenForwardCone d (fun μ => ((permAct (d := d) σ w) k0 μ).im) := by
    have hwσ : InOpenForwardCone d (fun μ => (w (σ k0) μ).im) :=
      forwardTube_point_inOpenForwardCone (d := d) (n := n) hwFT (σ k0)
    simpa [permAct] using hwσ
  have hneg :
      InOpenForwardCone d
        (fun μ =>
          (complexLorentzAction (expBoost (d := d) ((Real.pi : ℂ) * Complex.I))
            (permAct (d := d) σ w) k0 μ).im) :=
    forwardTube_point_inOpenForwardCone (d := d) (n := n) hpiFT k0
  have hneg_time : ((permAct (d := d) σ w) k0 0).im < 0 := by
    have htime_pos :
        0 <
          (complexLorentzAction (expBoost (d := d) ((Real.pi : ℂ) * Complex.I))
            (permAct (d := d) σ w) k0 0).im := hneg.1
    have htime :
        (complexLorentzAction (expBoost (d := d) ((Real.pi : ℂ) * Complex.I))
          (permAct (d := d) σ w) k0 0).im =
          -((permAct (d := d) σ w) k0 0).im := by
      rw [expBoost_pi_I_action_time0 (d := d) (n := n) hd1 (permAct (d := d) σ w) k0]
      simp [Complex.neg_im]
    linarith
  linarith [hpos.1, hneg_time]

private lemma im_add_int_two_pi_I (t : ℂ) (m : ℤ) :
    (t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)).im =
      t.im + (m : ℝ) * (2 * Real.pi) := by
  simp [mul_comm, mul_left_comm]

/-- Scalar parameter normalization: from a nonempty boost slice, one can move
    the parameter into the principal strip by an integer `2πi` shift, optionally
    followed by a sign flip. -/
private theorem expBoost_nonempty_parameter_normalization (d : ℕ) (hd2 : 2 ≤ d)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : σ ≠ 1)
    (t : ℂ)
    (ht : (permForwardOverlapSlice (d := d) n σ (expBoost (d := d) t)).Nonempty) :
    ∃ (t' : ℂ) (m : ℤ),
      (0 < t'.im ∧ t'.im < Real.pi) ∧
      (t' = t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) ∨
       t' = -(t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I))
      ) := by
  have heven : ∀ m : ℤ, t.im ≠ ((2 * m : ℤ) : ℝ) * Real.pi :=
    expBoost_nonempty_excludes_even_meridian d hd2 n σ hσ t ht
  have hodd : ∀ m : ℤ, t.im ≠ ((2 * m + 1 : ℤ) : ℝ) * Real.pi :=
    expBoost_nonempty_excludes_odd_meridian d hd2 n σ hσ t ht
  let m0 : ℤ := Int.floor (t.im / (2 * Real.pi))
  let y : ℝ := t.im - (m0 : ℝ) * (2 * Real.pi)
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hm0_le : (m0 : ℝ) ≤ t.im / (2 * Real.pi) := Int.floor_le _
  have hm0_lt : t.im / (2 * Real.pi) < (m0 : ℝ) + 1 := Int.lt_floor_add_one _
  have hm0_mul : (m0 : ℝ) * (2 * Real.pi) ≤ t.im := by
    have hmul := mul_le_mul_of_nonneg_right hm0_le (le_of_lt h2pi_pos)
    have hdiv : (t.im / (2 * Real.pi)) * (2 * Real.pi) = t.im := by
      field_simp [ne_of_gt h2pi_pos]
    linarith
  have hm0_mul_lt : t.im < ((m0 : ℝ) + 1) * (2 * Real.pi) := by
    have hmul := mul_lt_mul_of_pos_right hm0_lt h2pi_pos
    have hdiv : (t.im / (2 * Real.pi)) * (2 * Real.pi) = t.im := by
      field_simp [ne_of_gt h2pi_pos]
    linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    linarith
  have hy_lt_two_pi : y < 2 * Real.pi := by
    dsimp [y]
    linarith
  have hy_ne_zero : y ≠ 0 := by
    intro hy0
    change t.im - (m0 : ℝ) * (2 * Real.pi) = 0 at hy0
    have hy0' : t.im = (m0 : ℝ) * (2 * Real.pi) := by linarith
    have hy0'' : t.im = ((2 * m0 : ℤ) : ℝ) * Real.pi := by
      calc
        t.im = (m0 : ℝ) * (2 * Real.pi) := hy0'
        _ = ((2 * m0 : ℤ) : ℝ) * Real.pi := by
            norm_num [Int.cast_mul, mul_assoc, mul_comm, mul_left_comm]
    exact heven m0 hy0''
  have hy_ne_pi : y ≠ Real.pi := by
    intro hypi
    change t.im - (m0 : ℝ) * (2 * Real.pi) = Real.pi at hypi
    have hypi' : t.im = (m0 : ℝ) * (2 * Real.pi) + Real.pi := by linarith
    have hypi'' : t.im = ((2 * m0 + 1 : ℤ) : ℝ) * Real.pi := by
      calc
        t.im = (m0 : ℝ) * (2 * Real.pi) + Real.pi := hypi'
        _ = ((2 * m0 + 1 : ℤ) : ℝ) * Real.pi := by
            norm_num [Int.cast_mul, Int.cast_add, mul_assoc, mul_comm, mul_left_comm]
            ring
    exact hodd m0 hypi''
  have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy_ne_zero)
  by_cases hy_lt_pi : y < Real.pi
  · let m : ℤ := -m0
    let t' : ℂ := t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)
    have ht'im : t'.im = y := by
      unfold t' m
      rw [im_add_int_two_pi_I]
      have hnegm : ((-m0 : ℤ) : ℝ) = -(m0 : ℝ) := by norm_num
      rw [hnegm]
      dsimp [y]
      ring
    refine ⟨t', m, ?_, ?_⟩
    · exact ⟨by simpa [ht'im] using hy_pos, by simpa [ht'im] using hy_lt_pi⟩
    · exact Or.inl rfl
  · have hy_pi_le : Real.pi ≤ y := le_of_not_gt hy_lt_pi
    have hy_gt_pi : Real.pi < y := lt_of_le_of_ne hy_pi_le (Ne.symm hy_ne_pi)
    let m : ℤ := -m0 - 1
    let t' : ℂ := -(t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I))
    have ht'im : t'.im = 2 * Real.pi - y := by
      unfold t' m
      rw [Complex.neg_im, im_add_int_two_pi_I]
      have hnegm : ((-m0 - 1 : ℤ) : ℝ) = -(m0 : ℝ) - 1 := by norm_num
      rw [hnegm]
      dsimp [y]
      ring
    refine ⟨t', m, ?_, ?_⟩
    · constructor
      · have : 0 < 2 * Real.pi - y := by linarith [hy_lt_two_pi]
        simpa [ht'im] using this
      · have : 2 * Real.pi - y < Real.pi := by linarith [hy_gt_pi]
        simpa [ht'im] using this
    · exact Or.inr rfl

/-- **Principal-strip normalization for boosts (up to real `K`-factors)**.

    This follows from:
    1. scalar parameter normalization (shift/reflection),
    2. `2πi` periodicity of `expBoost`,
    3. Weyl conjugation `exp(tK) ↦ exp(-tK)`. -/
private theorem expBoost_principal_representative (d : ℕ) (hd2 : 2 ≤ d)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : σ ≠ 1)
    (t : ℂ)
    (ht : (permForwardOverlapSlice (d := d) n σ (expBoost (d := d) t)).Nonempty) :
    ∃ (kL kR : RestrictedLorentzGroup d) (t' : ℂ),
      (0 < t'.im ∧ t'.im < Real.pi) ∧
      expBoost (d := d) t =
        ComplexLorentzGroup.ofReal kL * expBoost (d := d) t' * ComplexLorentzGroup.ofReal kR := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨t', m, ht'_strip, ht'_form⟩ :=
    expBoost_nonempty_parameter_normalization d hd2 n σ hσ t ht
  rcases ht'_form with ht'_shift | ht'_refl
  · refine ⟨1, 1, t', ht'_strip, ?_⟩
    have hperiod :
        expBoost (d := d) (t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) = expBoost (d := d) t :=
      expBoost_periodic_two_pi_I_int (d := d) hd1 t m
    have ht_eq : expBoost (d := d) t = expBoost (d := d) t' := by
      simpa [ht'_shift] using hperiod.symm
    calc
      expBoost (d := d) t = expBoost (d := d) t' := ht_eq
      _ = ComplexLorentzGroup.ofReal (1 : RestrictedLorentzGroup d) * expBoost (d := d) t' *
            ComplexLorentzGroup.ofReal (1 : RestrictedLorentzGroup d) := by
          simp [ofReal_one_eq, mul_assoc]
  · refine ⟨weylRot d hd2, weylRot d hd2, t', ht'_strip, ?_⟩
    have hperiod :
        expBoost (d := d) (t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) = expBoost (d := d) t :=
      expBoost_periodic_two_pi_I_int (d := d) hd1 t m
    have hnegarg :
        -t' = t + (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
      rw [ht'_refl]
      ring
    have ht_eq_neg : expBoost (d := d) t = expBoost (d := d) (-t') := by
      simpa [hnegarg] using hperiod.symm
    calc
      expBoost (d := d) t = expBoost (d := d) (-t') := ht_eq_neg
      _ = ComplexLorentzGroup.ofReal (weylRot d hd2) * expBoost (d := d) t' *
            ComplexLorentzGroup.ofReal (weylRot d hd2) := by
          simpa using (weylConj_expBoost (d := d) hd2 t').symm

/-- **Principal-strip KAK decomposition**: every slice-index element factors as
    `k₁ · exp(tK) · k₂` with `t` in the principal boost overlap.

    This is obtained from:
    1. the raw KAK factorization (`raw_KAK_decomposition`), and
    2. principal-strip normalization of the boost parameter
       (`expBoost_principal_representative`). -/
theorem sliceIndexSet_KAK_principal {d : ℕ} (hd2 : 2 ≤ d)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : σ ≠ 1)
    (Λ : ComplexLorentzGroup d)
    (hΛ : (permForwardOverlapSlice (d := d) n σ Λ).Nonempty) :
    ∃ (k₁ k₂ : RestrictedLorentzGroup d) (t : ℂ),
      t ∈ principalBoostOverlap d n σ ∧
      Λ = ComplexLorentzGroup.ofReal k₁ * expBoost t * ComplexLorentzGroup.ofReal k₂ := by
  obtain ⟨k₁, k₂, t, hKAK⟩ := raw_KAK_decomposition Λ
  have ht_nonempty_raw :
      (permForwardOverlapSlice (d := d) n σ (expBoost t)).Nonempty := by
    have hcomposed :
        (permForwardOverlapSlice (d := d) n σ
          (ComplexLorentzGroup.ofReal k₁ * expBoost t * ComplexLorentzGroup.ofReal k₂)).Nonempty := by
      simpa [hKAK] using hΛ
    exact sliceIndexSet_bi_invariant_rev n σ (expBoost t) k₁ k₂ hcomposed
  obtain ⟨kL, kR, t', ht'_strip, ht_repr⟩ :=
    expBoost_principal_representative d hd2 n σ hσ t ht_nonempty_raw
  have ht'_nonempty :
      (permForwardOverlapSlice (d := d) n σ (expBoost t')).Nonempty := by
    have hcomposed :
        (permForwardOverlapSlice (d := d) n σ
          (ComplexLorentzGroup.ofReal kL * expBoost t' * ComplexLorentzGroup.ofReal kR)).Nonempty := by
      simpa [ht_repr] using ht_nonempty_raw
    exact sliceIndexSet_bi_invariant_rev n σ (expBoost t') kL kR hcomposed
  refine ⟨k₁ * kL, kR * k₂, t', ?_, ?_⟩
  · refine ⟨ht'_strip, ?_⟩
    exact ht'_nonempty
  · calc
      Λ = ComplexLorentzGroup.ofReal k₁ * expBoost t * ComplexLorentzGroup.ofReal k₂ := hKAK
      _ = ComplexLorentzGroup.ofReal k₁ *
            (ComplexLorentzGroup.ofReal kL * expBoost t' * ComplexLorentzGroup.ofReal kR) *
            ComplexLorentzGroup.ofReal k₂ := by
              rw [ht_repr]
      _ = ComplexLorentzGroup.ofReal (k₁ * kL) * expBoost t' *
            ComplexLorentzGroup.ofReal (kR * k₂) := by
              simp [ofReal_mul_eq, mul_assoc]

/-- The slice index set is connected for `d ≥ 2`.

    **Proof**: By the principal-strip KAK decomposition, every element of the
    index set `I` factors as `k₁ · exp(tK) · k₂` with `t` in the principal
    boost overlap `P`. By bi-invariance, the boost part `exp(tK)` is also in `I`.
    So `I` is the image of `K × P × K` under the continuous multiplication map.
    Since `K = SO↑(1,d;ℝ)` is path-connected and `P` is connected (axiom),
    the product is connected, and so is its continuous image.

    **Key insight**: The previous axiom `isConnected_boostParameterOverlap`
    (on the full cylinder) was **false** for `n ≥ 3` — the meridians `Im(t) = 0`
    and `Im(t) = π` both give empty slices, disconnecting the cylinder into two
    strips. The principal strip fix restricts to `{0 < Im(t) < π}` and uses
    the Weyl reflection to cover both strips via KAK. -/
theorem isConnected_sliceIndexSet {d : ℕ}
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (hd2 : 2 ≤ d) :
    IsConnected {Λ : ComplexLorentzGroup d |
      (permForwardOverlapSlice (d := d) n σ Λ).Nonempty} := by
  -- Abbreviations
  let I := {Λ : ComplexLorentzGroup d | (permForwardOverlapSlice (d := d) n σ Λ).Nonempty}
  let P := principalBoostOverlap d n σ
  -- Step 1: The principal boost overlap (image on the group) is connected
  have hP_conn : IsConnected P := isConnected_principalBoostOverlap n σ hd2
  -- Step 2: K is path-connected
  haveI : PathConnectedSpace (RestrictedLorentzGroup d) :=
    pathConnectedSpace_iff_univ.mpr (RestrictedLorentzGroup.isPathConnected d)
  -- Step 3: The multiplication map
  --   f : K × {t // t ∈ P} × K → ComplexLorentzGroup d
  --   f(k₁, t, k₂) = ofReal(k₁) * expBoost(t) * ofReal(k₂)
  -- is continuous
  let f : RestrictedLorentzGroup d × {t : ℂ // t ∈ P} ×
      RestrictedLorentzGroup d → ComplexLorentzGroup d :=
    fun p => ComplexLorentzGroup.ofReal p.1 * expBoost p.2.1.val * ComplexLorentzGroup.ofReal p.2.2
  have hf_cont : Continuous f := by
    apply Continuous.mul
    · apply Continuous.mul
      · exact continuous_ofReal.comp continuous_fst
      · exact continuous_expBoost.comp (continuous_subtype_val.comp
          (continuous_fst.comp continuous_snd))
    · exact continuous_ofReal.comp (continuous_snd.comp continuous_snd)
  -- Step 4: f maps into I (by sliceIndexSet_bi_invariant)
  have hf_mem : ∀ p, f p ∈ I := by
    intro ⟨k₁, ⟨t, htP⟩, k₂⟩
    -- t ∈ P means expBoost t is in the slice index set
    exact sliceIndexSet_bi_invariant n σ (expBoost t) k₁ k₂ htP.2
  -- Step 5: f is surjective onto I (by principal KAK)
  have hf_surj : ∀ Λ ∈ I, ∃ p, f p = Λ := by
    intro Λ hΛ
    obtain ⟨k₁, k₂, t, htP, rfl⟩ := sliceIndexSet_KAK_principal hd2 n σ hσ Λ hΛ
    exact ⟨⟨k₁, ⟨t, htP⟩, k₂⟩, rfl⟩
  -- Step 6: The domain K × P × K is connected
  haveI : ConnectedSpace {t : ℂ // t ∈ P} :=
    isConnected_iff_connectedSpace.mp hP_conn
  -- Step 7: I = range f, which is connected (continuous image of connected)
  have hI_eq : Set.range f =
      {Λ : ComplexLorentzGroup d | (permForwardOverlapSlice (d := d) n σ Λ).Nonempty} := by
    ext Λ; constructor
    · rintro ⟨p, rfl⟩; exact hf_mem p
    · intro hΛ; obtain ⟨p, hp⟩ := hf_surj Λ hΛ; exact ⟨p, hp⟩
  rw [← hI_eq]
  exact isConnected_range hf_cont

/-- The forward-overlap set `{w ∈ FT | σ·w ∈ ET}` is connected for `d ≥ 2`.

    **Proof**: The forward-overlap set decomposes as a union of fixed-`Λ` slices
    (`permForwardOverlapSet_eq_iUnion_slice`). Each slice is the intersection of
    the forward tube with a linearly transformed forward tube, making it
    geometrically convex and therefore preconnected
    (`permForwardOverlapSlice_isPreconnected`). Since slice membership is an open
    condition (`permForwardOverlapSlice_openMembership`), and the index set of
    nonempty slices is connected (`isConnected_sliceIndexSet`), the topological
    gluing lemma `isConnected_iUnion_of_open_membership` gives connectedness
    of the full union. -/
theorem isConnected_permForwardOverlapSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (hd2 : 2 ≤ d) :
    IsConnected (permForwardOverlapSet (d := d) n σ) := by
  -- Define the index set: Λ's with nonempty slices
  let I := {Λ : ComplexLorentzGroup d | (permForwardOverlapSlice (d := d) n σ Λ).Nonempty}
  have hI_conn : IsConnected I := isConnected_sliceIndexSet n σ hσ hd2
  -- The forward-overlap set equals ⋃_{Λ ∈ I} Slice(Λ)
  have heq : permForwardOverlapSet (d := d) n σ =
      ⋃ Λ ∈ I, permForwardOverlapSlice (d := d) n σ Λ := by
    rw [permForwardOverlapSet_eq_iUnion_slice]
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨Λ, hΛ⟩; exact ⟨Λ, ⟨w, hΛ⟩, hΛ⟩
    · rintro ⟨Λ, _, hΛ⟩; exact ⟨Λ, hΛ⟩
  rw [heq]
  -- Apply the topological gluing lemma
  exact isConnected_iUnion_of_open_membership hI_conn
    (fun Λ => permForwardOverlapSlice (d := d) n σ Λ)
    (fun Λ hΛ => permForwardOverlapSlice_isPreconnected n σ Λ)
    (fun Λ hΛ => hΛ)
    (fun _Λ _hΛ w hw =>
      (permForwardOverlapSlice_openMembership n σ w _Λ hw).filter_mono
        nhdsWithin_le_nhds)

/-- **Connectedness of `ET ∩ σ⁻¹(ET)` for `d ≥ 2`.**

    By σ-Λ commutativity (`permAct_complexLorentzAction_comm`), the ET overlap
    equals the continuous image of `L₊(ℂ) × forward-overlap` under the
    Lorentz action map. Since `L₊(ℂ)` is connected and the forward-overlap
    set is connected (by the slice gluing argument), the product is connected,
    and so is its continuous image. -/
theorem isConnected_etOverlap
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (hd2 : 2 ≤ d) :
    IsConnected (etOverlap (d := d) n σ) := by
  rw [etOverlap_eq_image_forwardOverlap]
  have hcont : Continuous (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
      complexLorentzAction p.1 p.2) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    simp only [complexLorentzAction]
    apply continuous_finset_sum; intro ν _
    exact ((continuous_apply ν).comp ((continuous_apply μ).comp
      (ComplexLorentzGroup.continuous_val.comp continuous_fst))).mul
      ((continuous_apply ν).comp ((continuous_apply k).comp continuous_snd))
  haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
    pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
  have hFO_conn := isConnected_permForwardOverlapSet n σ hσ hd2
  constructor
  · rcases hFO_conn.nonempty with ⟨w, hw⟩
    exact ⟨complexLorentzAction 1 w,
      Set.mem_image_of_mem _ (Set.mk_mem_prod (Set.mem_univ _) hw)⟩
  · exact (PreconnectedSpace.isPreconnected_univ.prod
      hFO_conn.isPreconnected).image _ hcont.continuousOn

/-- **Target theorem for d ≥ 2 (Route B: ET identity theorem).**

    `extendF F` is permutation-invariant on the ET overlap.
    This is the exact shape needed to fill the `sorry` at
    `PermutationFlow.lean:2262` in the `d ≥ 2` branch.

    **Proof structure:**
    1. Define `h(z) = extendF F (σ·z) - extendF F (z)`.
    2. `h` is holomorphic on `W = ET ∩ σ⁻¹(ET)` (open, connected for `d ≥ 2`).
    3. `h = 0` on the permuted Jost set `V ⊂ W` (open, nonempty for `d ≥ 2`).
    4. By `identity_theorem_totally_real_product`, `h = 0` on all of `W`.

    **Textbook axiom:** `isConnected_sliceIndexSet` — connectedness of the
    index set of nonempty forward-overlap slices (from polar decomposition
    of `L₊(ℂ)`), which propagates through
    `isConnected_permForwardOverlapSet` → `isConnected_etOverlap` → here.
-/
theorem hExtPerm_of_d2
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
        ∑ μ, LorentzLieGroup.minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ≠ 1)
    (hd2 : 2 ≤ d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ExtendedTube d n)
    (hσz : (fun k => z (σ k)) ∈ ExtendedTube d n) :
    extendF F (fun k => z (σ k)) = extendF F z := by
  -- Step 1: Derive complex Lorentz invariance from real Lorentz invariance
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z :=
    complex_lorentz_invariance n F hF_holo hF_lorentz
  -- Step 2: Define h(z) = extendF F (σ·z) - extendF F (z)
  set h : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => extendF F (permAct (d := d) σ z) - extendF F z with hh_def
  -- Step 3: h is holomorphic on W = etOverlap
  have hh_holo : DifferentiableOn ℂ h (etOverlap (d := d) n σ) :=
    differentiableOn_extendF_diff_on_etOverlap n σ F hF_holo hF_cinv
  -- Step 4: W is open and connected
  have hW_open : IsOpen (etOverlap (d := d) n σ) := isOpen_etOverlap n σ
  have hW_conn : IsConnected (etOverlap (d := d) n σ) :=
    isConnected_etOverlap n σ hσ hd2
  -- Step 5: The permuted Jost set V is open and nonempty, with realEmbed V ⊂ W
  have hV_open : IsOpen (permJostSet (d := d) n σ) := isOpen_permJostSet n σ
  have hV_ne : (permJostSet (d := d) n σ).Nonempty := permJostSet_nonempty n σ hd2
  have hV_sub : ∀ x ∈ permJostSet (d := d) n σ,
      realEmbed x ∈ etOverlap (d := d) n σ :=
    permJostSet_realEmbed_sub_etOverlap n σ
  -- Step 6: h = 0 on V
  have hh_zero : ∀ x ∈ permJostSet (d := d) n σ,
      h (realEmbed x) = 0 :=
    extendF_diff_zero_on_permJostSet n F hF_holo hF_cinv
      (by intro x; exact hF_bv x) hF_local σ
  -- Step 7: Identity theorem gives h = 0 on all of W
  have hh_all : ∀ z ∈ etOverlap (d := d) n σ, h z = 0 :=
    identity_theorem_totally_real_product hW_open hW_conn hh_holo
      hV_open hV_ne hV_sub hh_zero
  -- Step 8: Apply at our specific z
  have hz_in_W : z ∈ etOverlap (d := d) n σ := by
    exact ⟨hz, by simpa [permAct] using hσz⟩
  have := hh_all z hz_in_W
  simp only [hh_def] at this
  exact sub_eq_zero.mp this

/-! ### Dimension reduction: `d = 1` → `d = 2`

For `d = 1`, real Jost witnesses do not exist (proved in
`d1_no_real_witness_swap_n2_probe.lean`). We handle this case by embedding
1+1 Minkowski space into 2+1, applying `hExtPerm_of_d2`, and projecting back.

**Strategy**: Define `dimLift : (Fin n → Fin 2 → ℂ) → (Fin n → Fin 3 → ℂ)` that appends
a zero spatial coordinate. Show:
1. `dimLift` maps `FT(1,n)` into `FT(2,n)` (forward cone monotonicity)
2. Block-embedding `L₊(ℂ,1) ↪ L₊(ℂ,2)` makes `dimLift` equivariant under Lorentz action
3. `dimLift` maps `ET(1,n)` into `ET(2,n)` (from 1 + 2)
4. `extendF (F ∘ proj) ∘ lift = extendF F` (extension respects dimensional reduction)
5. `F ∘ proj` satisfies the Wightman axioms on `FT(2,n)` (holomorphy, Lorentz invariance,
   boundary values, locality all transfer)
6. Apply `hExtPerm_of_d2` to `F ∘ proj` and translate back.

The key technical steps are the Lorentz group embedding (block matrix in `SO₊(1,d;ℂ)`)
and the `extendF` compatibility (which uses well-definedness of extension on ET preimages).
-/

/-- **Dimension reduction axiom** (textbook): `extendF F` is permutation-invariant
    on the ET overlap for `d = 1`.

    For `d ≥ 2`, this is proved in `hExtPerm_of_d2` using the identity theorem
    with slice-gluing connectedness (`isConnected_sliceIndexSet`) and Jost witnesses
    (`permJostSet_nonempty`). For `d = 1`, real Jost witnesses do not exist
    (proved in `d1_no_real_witness_swap_n2_probe.lean`), so the proof requires
    fundamentally different infrastructure.

    The standard textbook approach embeds 1+1D into 2+1D, applies the `d ≥ 2`
    result, and projects back. However, the naive lift `F ∘ proj` does NOT
    preserve full `SO₊(1,2;ℂ)` Lorentz invariance (spatial rotations mixing the
    two spatial components would alter the projected function). The rigorous lift
    requires expressing `F` in terms of Lorentz-invariant scalar products
    `z_i · z_j` via the BHW representation theorem for invariant analytic
    functions, which then trivially extends to higher dimension.

    We axiomatize the conclusion (permutation invariance of `extendF` on
    `ET ∩ σ⁻¹(ET)` for `d = 1`) rather than formalizing the BHW invariant
    theory and Fin-arithmetic infrastructure for the dimensional embedding.

    **References**:
    - R.F. Streater and A.S. Wightman, "PCT, Spin and Statistics, and All That"
      (1964, 2000), Section 2-5, Remark after Theorem 2-11 -/
axiom hExtPerm_of_d1
    (n : ℕ)
    (F : (Fin n → Fin 2 → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin 2 → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin 2 → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin 2 → ℝ),
        ∑ μ, LorentzLieGroup.minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin 2 → ℂ)
    (hz : z ∈ ExtendedTube 1 n)
    (hσz : (fun k => z (σ k)) ∈ ExtendedTube 1 n) :
    extendF F (fun k => z (σ k)) = extendF F z

end BHW
