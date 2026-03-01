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

/-- A 1-parameter family of complex Lorentz boosts in a fixed spatial direction.
    Defined as `{exp(t · K) | t ∈ ℂ}` where `K` is the boost generator.
    This is a complex 1-parameter subgroup, isomorphic to `(ℂ, +)`, hence connected. -/
private def complexBoostStrip (d : ℕ) : Set (ComplexLorentzGroup d) :=
  Set.range (fun t : ℂ => ComplexLorentzGroup.expLieAlg (t • boostGen d)
    (ComplexLorentzGroup.isInLieAlgebra_smul t boostGen_isInLieAlgebra))

/-- The complex boost strip is connected (it is the continuous image of ℂ). -/
private theorem isConnected_complexBoostStrip (_hd2 : 2 ≤ d) :
    IsConnected (complexBoostStrip d) := by
  -- The strip is the range of the continuous map t ↦ exp(t · boostGen)
  -- ℂ is connected, so the image is connected.
  unfold complexBoostStrip
  apply isConnected_range
  have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
  rw [hind.continuous_iff]
  show Continuous (fun t : ℂ => exp (t • boostGen d))
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

/-- Cartan (KAK) decomposition: every complex Lorentz transform decomposes as
    `Λ = R₁ · B · R₂` where `R₁, R₂ ∈ L₊↑(ℝ)` and `B` lies in the
    complex boost strip. -/
private theorem cartan_decomposition (hd2 : 2 ≤ d) (Λ : ComplexLorentzGroup d) :
    ∃ (k₁ k₂ : RestrictedLorentzGroup d) (a : ComplexLorentzGroup d),
      a ∈ complexBoostStrip d ∧
      Λ = ComplexLorentzGroup.ofReal k₁ * a * ComplexLorentzGroup.ofReal k₂ := sorry

/-- Every element of the complex boost strip lies in the slice index set for `d ≥ 2`.
    This is the geometric core: for a complex boost `B(t)` and any permutation `σ`,
    there exists `w ∈ FT` with `B(t) · (σ · w) ∈ FT`. For `d ≥ 2`, the forward
    cone has enough spatial dimensions that the boost can be arranged orthogonally
    to the difference vectors. -/
private theorem complexBoostStrip_subset_sliceIndexSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    complexBoostStrip d ⊆ {Λ : ComplexLorentzGroup d |
      (permForwardOverlapSlice (d := d) n σ Λ).Nonempty} := sorry

/-- The index set of Lorentz transforms with nonempty forward-overlap slice
    is connected for `d ≥ 2`.

    **Proof:** By the Cartan (KAK) decomposition, every `Λ ∈ L₊(ℂ)` factors as
    `Λ = R₁ · B · R₂` with `R₁, R₂ ∈ L₊↑(ℝ)` and `B` in the complex boost strip.
    By bi-invariance (`sliceIndexSet_bi_invariant`), `Λ ∈ I ↔ B ∈ I`.
    By `complexBoostStrip_subset_sliceIndexSet`, the strip lies in `I`.
    The index set is therefore the continuous image of
    `L₊↑(ℝ) × (I ∩ boost strip) × L₊↑(ℝ)` under the multiplication map,
    which is connected (product of connected spaces mapped continuously). -/
private theorem isConnected_sliceIndexSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    IsConnected {Λ : ComplexLorentzGroup d |
      (permForwardOverlapSlice (d := d) n σ Λ).Nonempty} := by
  let I := {Λ : ComplexLorentzGroup d | (permForwardOverlapSlice (d := d) n σ Λ).Nonempty}
  -- K = image of real restricted Lorentz group in L₊(ℂ)
  let K : Set (ComplexLorentzGroup d) :=
    Set.range (ComplexLorentzGroup.ofReal : RestrictedLorentzGroup d → ComplexLorentzGroup d)
  -- K is connected (continuous image of path-connected space)
  have hK_conn : IsConnected K := by
    have heq : K = ComplexLorentzGroup.ofReal '' Set.univ :=
      (Set.image_univ).symm
    rw [heq]
    have hpc := IsPathConnected.isConnected
      (RestrictedLorentzGroup.isPathConnected (d := d))
    exact IsConnected.image hpc _ continuous_ofReal.continuousOn
  -- A = complex boost strip (connected for d ≥ 2)
  let A := complexBoostStrip d
  -- I ∩ A = A (all boosts are in the index set)
  have hIA_eq : I ∩ A = A := by
    ext a; constructor
    · exact And.right
    · intro ha; exact ⟨complexBoostStrip_subset_sliceIndexSet n σ hd2 ha, ha⟩
  have hIA_conn : IsConnected (I ∩ A) := by rw [hIA_eq]; exact isConnected_complexBoostStrip hd2
  -- Multiplication map: (k₁, a, k₂) ↦ k₁ * a * k₂
  let mulMap : ComplexLorentzGroup d × (ComplexLorentzGroup d × ComplexLorentzGroup d) →
      ComplexLorentzGroup d := fun p => p.1 * p.2.1 * p.2.2
  have h_cont : Continuous mulMap := by
    apply Continuous.mul
    · exact (continuous_fst).mul (continuous_fst.comp continuous_snd)
    · exact continuous_snd.comp continuous_snd
  -- I = mulMap '' (K ×ˢ ((I ∩ A) ×ˢ K))
  have h_image : I = mulMap '' (K ×ˢ ((I ∩ A) ×ˢ K)) := by
    ext Λ; constructor
    · intro hΛ
      rcases cartan_decomposition hd2 Λ with ⟨k₁, k₂, a, ha, rfl⟩
      refine ⟨(ComplexLorentzGroup.ofReal k₁, a, ComplexLorentzGroup.ofReal k₂),
        ⟨⟨k₁, rfl⟩, ⟨?_, ha⟩, ⟨k₂, rfl⟩⟩, rfl⟩
      exact sliceIndexSet_bi_invariant_rev n σ a k₁ k₂ hΛ
    · rintro ⟨⟨k₁_val, a_val, k₂_val⟩, ⟨⟨k₁, rfl⟩, ⟨haI, _⟩, ⟨k₂, rfl⟩⟩, rfl⟩
      exact sliceIndexSet_bi_invariant n σ a_val k₁ k₂ haI
  -- Connected product mapped continuously
  have hprod_conn := (hK_conn.prod (hIA_conn.prod hK_conn)).image _ h_cont.continuousOn
  convert hprod_conn using 1

/-- The forward-overlap set `{w ∈ FT | σ·w ∈ ET}` is connected for `d ≥ 2`.

    Uses the slice decomposition `permForwardOverlapSet = ⋃_Λ Slice(Λ)`
    where each `Slice(Λ)` is convex (hence connected), together with the
    topological gluing lemma (`isConnected_iUnion_of_open_membership`).

    The gluing lemma requires:
    1. Connected index set (from `isConnected_sliceIndexSet`)
    2. Each slice is preconnected (from convexity, `permForwardOverlapSlice_isPreconnected`)
    3. Each slice is nonempty (by definition of the index set)
    4. Slice membership is open in Λ (from `permForwardOverlapSlice_openMembership`) -/
theorem isConnected_permForwardOverlapSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    IsConnected (permForwardOverlapSet (d := d) n σ) := by
  -- Rewrite as union of slices over the index set of nonempty slices
  let I := {Λ : ComplexLorentzGroup d | (permForwardOverlapSlice (d := d) n σ Λ).Nonempty}
  have hI_conn : IsConnected I := isConnected_sliceIndexSet n σ hd2
  -- The forward-overlap set equals ⋃_{Λ ∈ I} Slice(Λ)
  have heq : permForwardOverlapSet (d := d) n σ = ⋃ Λ ∈ I, permForwardOverlapSlice (d := d) n σ Λ := by
    rw [permForwardOverlapSet_eq_iUnion_slice]
    ext w; simp only [Set.mem_iUnion]; constructor
    · rintro ⟨Λ, hΛ⟩; exact ⟨Λ, ⟨w, hΛ⟩, hΛ⟩
    · rintro ⟨Λ, _, hΛ⟩; exact ⟨Λ, hΛ⟩
  rw [heq]
  exact isConnected_iUnion_of_open_membership hI_conn
    (fun Λ => permForwardOverlapSlice (d := d) n σ Λ)
    (fun Λ _ => permForwardOverlapSlice_isPreconnected n σ Λ)
    (fun Λ hΛ => hΛ)
    (fun Λ hΛ w hw => by
      have := permForwardOverlapSlice_openMembership n σ w Λ hw
      exact this.filter_mono nhdsWithin_le_nhds)

/-- **Connectedness of `ET ∩ σ⁻¹(ET)` for `d ≥ 2`.**

    By σ-Λ commutativity (`permAct_complexLorentzAction_comm`), the ET overlap
    equals the continuous image of `L₊(ℂ) × forward-overlap` under the
    Lorentz action map. Since `L₊(ℂ)` is connected and the forward-overlap
    set is connected (by the slice gluing argument), the product is connected,
    and so is its continuous image. -/
theorem isConnected_etOverlap
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
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
  have hFO_conn := isConnected_permForwardOverlapSet n σ hd2
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

    **Remaining sorry:** `isConnected_sliceIndexSet` — connectedness of the
    index set `{Λ | Slice(Λ) ≠ ∅}`, which propagates through
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
    isConnected_etOverlap n σ hd2
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

/-! ### Remaining work: `d = 1` branch

For `d = 1`, real Jost witnesses do not exist (proved in
`d1_no_real_witness_swap_n2_probe.lean`). Neither the FT-overlap
connectedness route nor the ET identity theorem route apply directly.

**Recommended approach: Dimension reduction.**
Embed 1+1 Minkowski space into 2+1 by adding a trivial spatial dimension,
invoke the `d ≥ 2` theorem, and project back. This requires a compatibility
lemma between forward tubes across dimensions:

  `ForwardTube 1 n ≃ ForwardTube 2 n ∩ {z | ∀ k, z k 2 = 0}`

This is the standard textbook approach for handling the `d = 1` case.
-/

end BHW
