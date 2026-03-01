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

/-- Every transposition `swap a b` in `Fin n` can be written as a product of
    adjacent transpositions. Stated as a property that propagates through
    the product: if P holds for the identity and is preserved by left-multiplication
    by any adjacent swap, then P holds for `swap a b`. -/
lemma swap_adj_induction {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    {P : Equiv.Perm (Fin n) → Prop}
    (hid : P 1)
    (hadj : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
      P σ → P (Equiv.swap i ⟨i.val + 1, hi⟩ * σ)) :
    P (Equiv.swap a b) := by
  sorry

/-- F is invariant under any swap on JostSet.

    Reduces arbitrary swaps to adjacent swaps via `swap_adj_induction`,
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
    (a b : Fin n) (hab : a ≠ b)
    (x : Fin n → Fin (d + 1) → ℝ) (hxJ : x ∈ JostSet d n) :
    F (fun k μ => (x (Equiv.swap a b k) μ : ℂ)) =
    F (fun k μ => (x k μ : ℂ)) := by
  -- Use swap_adj_induction with:
  -- P(σ) = ∀ y ∈ JostSet, F(y ∘ σ) = F(y)
  suffices h : ∀ y : Fin n → Fin (d + 1) → ℝ, y ∈ JostSet d n →
      F (fun k μ => (y (Equiv.swap a b k) μ : ℂ)) = F (fun k μ => (y k μ : ℂ)) from
    h x hxJ
  apply swap_adj_induction a b hab (P := fun σ =>
    ∀ y : Fin n → Fin (d + 1) → ℝ, y ∈ JostSet d n →
      F (fun k μ => (y (σ k) μ : ℂ)) = F (fun k μ => (y k μ : ℂ)))
  · -- P(1): trivial
    intro y _; simp
  · -- P(σ) → P(swap(i, i+1) * σ)
    intro σ i hi ih y hyJ
    have hwJ : (fun k => y (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ JostSet d n :=
      jostSet_permutation_invariant _ hyJ
    have hrewrite : (fun k μ => (y ((Equiv.swap i ⟨i.val + 1, hi⟩ * σ) k) μ : ℂ)) =
        (fun k μ => ((fun k' => y (Equiv.swap i ⟨i.val + 1, hi⟩ k')) (σ k) μ : ℂ)) := by
      ext k μ; simp [Equiv.Perm.mul_apply]
    rw [hrewrite, ih _ hwJ]
    exact F_adj_swap_invariant F hF_local y hyJ i hi

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

/-- **Key lemma: Connectedness of the ET overlap `W = ET ∩ σ⁻¹(ET)`.**

    This is the remaining geometric obligation for Route B. The standard
    proof uses the fact that ET is a "domain of holomorphy" with a specific
    geometric structure (union of Lorentz orbits of FT), which makes the
    intersection `ET ∩ σ⁻¹(ET)` connected.

    **Proof sketch (Streater–Wightman, §2-5):**
    The extended tube `T'_n = L₊(ℂ) · T_n` is connected (continuous image
    of connected `L₊(ℂ) × T_n`). Both `T'_n` and `σ(T'_n) = T'_n`
    (since `T'_n` is invariant under permutations — every permutation is
    a complex Lorentz transformation composed with a relabeling). Therefore
    `W = T'_n ∩ σ⁻¹(T'_n) = T'_n` and W is connected.

    **Wait — is `T'_n` permutation-invariant?**
    If `z ∈ ET`, does `σ·z ∈ ET`? This would make `W = ET` and the
    connectedness would be immediate. However, this is exactly what we are
    *trying to prove* (it would follow from `extendF` permutation invariance
    by the identity theorem, creating a circular argument).

    In general, `T'_n` is NOT permutation-invariant — its permutation
    invariance is the *consequence* of the BHW theorem, not a prerequisite.
    So `W = ET ∩ σ⁻¹(ET)` is a proper open subset of ET, and its
    connectedness is a genuine geometric obligation.

    The standard textbook approach proves this via the Jost–Lehmann–Dyson
    representation or by direct geometric analysis of the tube structure. -/
theorem isConnected_etOverlap
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    IsConnected (etOverlap (d := d) n σ) := by
  sorry

/-- **Target theorem for d ≥ 2 (Route B: ET identity theorem).**

    `extendF F` is permutation-invariant on the ET overlap.
    This is the exact shape needed to fill the `sorry` at
    `PermutationFlow.lean:2262` in the `d ≥ 2` branch.

    **Proof structure:**
    1. Define `h(z) = extendF F (σ·z) - extendF F (z)`.
    2. `h` is holomorphic on `W = ET ∩ σ⁻¹(ET)` (open, connected for `d ≥ 2`).
    3. `h = 0` on the permuted Jost set `V ⊂ W` (open, nonempty for `d ≥ 2`).
    4. By `identity_theorem_totally_real_product`, `h = 0` on all of `W`.

    **Remaining sorrys:**
    - `F_perm_invariant_on_jostSet`: locality for general σ on JostSet
      (induction on adjacent transposition decomposition).
    - `isConnected_etOverlap`: connectedness of `ET ∩ σ⁻¹(ET)`.
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
