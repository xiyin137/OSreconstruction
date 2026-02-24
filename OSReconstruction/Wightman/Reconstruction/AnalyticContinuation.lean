/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.Spacetime.MinkowskiGeometry
import OSReconstruction.Wightman.Reconstruction.Helpers.SeparatelyAnalytic
import OSReconstruction.Wightman.Reconstruction.Helpers.EdgeOfWedge
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.ComplexLieGroups.Connectedness
import OSReconstruction.Bridge.AxiomBridge
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Analytic Continuation Infrastructure for OS Reconstruction

This file develops the analytic continuation machinery needed for the
Osterwalder-Schrader reconstruction theorems, including:

1. **Permuted extended tube** — the domain obtained by applying all permutations
   to the extended forward tube, then taking the envelope of holomorphy
2. **Euclidean points** — the subset corresponding to purely imaginary time
3. **Bargmann-Hall-Wightman (BHW) theorem** — extension of Wightman functions
   from the forward tube to the permuted extended tube
4. **Edge-of-the-wedge theorem** — the key complex analysis result enabling BHW
5. **Jost points** — real points in the permuted extended tube (spacelike configurations)

## Mathematical Background

### Forward Tube → Extended Tube → Permuted Extended Tube

The **forward tube** T_n ⊂ ℂ^{n(d+1)} consists of complex n-point configurations
where successive imaginary-part differences lie in the open forward light cone V₊:
  T_n = {z : Im(z_k - z_{k-1}) ∈ V₊ for k = 1,...,n}

The **extended tube** T'_n is the orbit of T_n under the complex Lorentz group L₊(ℂ):
  T'_n = ⋃_{Λ ∈ L₊(ℂ)} Λ(T_n)

The **permuted extended tube** is:
  T''_n = ⋃_{π ∈ S_n} π(T'_n)

### BHW Theorem

The Bargmann-Hall-Wightman theorem states that a holomorphic function on T_n that is
invariant under the real Lorentz group L₊↑ extends uniquely to a holomorphic function
on the **envelope of holomorphy** of T''_n, which is invariant under complex Lorentz
transformations and permutations.

Key ingredients:
1. **Complex Lorentz invariance**: Real Lorentz covariance + holomorphy on T_n implies
   complex Lorentz invariance on T'_n (by analytic continuation of the group action)
2. **Local commutativity** at **Jost points**: Spacelike-separated real points lie in
   multiple permuted extended tubes. Locality ensures the values agree.
3. **Edge-of-the-wedge theorem**: Stitches holomorphic functions on adjacent "wedges"
   (permuted tubes sharing a real boundary) into a single holomorphic function.

### Euclidean Points

A configuration z ∈ ℂ^{n(d+1)} is **Euclidean** if z_k = (iτ_k, x⃗_k) with
τ_k ∈ ℝ and x⃗_k ∈ ℝ^d. For distinct Euclidean points, some permutation π makes
the imaginary times ordered: τ_{π(1)} > τ_{π(2)} > ... > τ_{π(n)}, placing
the permuted configuration in T_n.

**Theorem**: All distinct Euclidean points lie in the permuted extended tube.
This is what allows defining Schwinger functions by restricting the analytically
continued Wightman functions to Euclidean points.

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 2
* Jost, "The General Theory of Quantized Fields", Chapter IV
* Osterwalder-Schrader I (1973), Section 5
* Osterwalder-Schrader II (1975), Sections IV-V
-/

noncomputable section

open Complex

variable {d : ℕ} [NeZero d]

/-! ### Complex Lorentz Group

The `ComplexLorentzGroup d` structure and its `ofReal`/`ofEuclidean` constructors are imported
from `OSReconstruction.ComplexLieGroups.Complexification` (via `Connectedness`). That definition
uses `LorentzLieGroup.minkowskiSignature`, which equals `MinkowskiSpace.metricSignature` by `rfl`
(see `minkowskiSignature_eq_metricSignature` in `AxiomBridge.lean`).

The imported `ComplexLorentzGroup.ofReal` takes `RestrictedLorentzGroup d` (from LorentzLieGroup).
To construct from `LorentzGroup.Restricted`, use `wightmanToRestrictedLorentzGroup` from
`AxiomBridge.lean`.
-/

/-! ### Extended Tube via Complex Lorentz Group -/

/-- The extended forward tube using the full complex Lorentz group.

    T'_n = ⋃_{Λ ∈ L₊(ℂ)} Λ(T_n)

    Note: WightmanAxioms.lean defined `ExtendedForwardTube` using only the real
    restricted Lorentz group. Here we use the full complex Lorentz group, which
    gives a strictly larger domain. The two are related by:
      ExtendedForwardTube ⊂ ComplexExtendedForwardTube ⊂ PermutedExtendedTube -/
def ComplexExtendedForwardTube (d n : ℕ) [NeZero d] :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
    w ∈ ForwardTube d n ∧
    z = fun k μ => ∑ ν, Λ.val μ ν * w k ν }

/-- The permuted forward tube for permutation π.

    π(T_n) = {z ∈ ℂ^{n(d+1)} : (z_{π(1)}, ..., z_{π(n)}) ∈ T_n}

    Different permutations impose different orderings on the imaginary parts. -/
def PermutedForwardTube (d n : ℕ) [NeZero d] (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k => z (π k)) ∈ ForwardTube d n }

/-- The permuted extended tube T''_n = ⋃_{π ∈ S_n} π(T'_n)

    This is the union over all permutations of the complex-extended forward tubes.
    The BHW theorem says Wightman functions extend holomorphically to (the envelope
    of holomorphy of) this domain. -/
def PermutedExtendedTube (d n : ℕ) [NeZero d] :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ π : Equiv.Perm (Fin n),
    { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧
      z = fun k μ => ∑ ν, Λ.val μ ν * w k ν }

/-- The forward tube is contained in the complex extended forward tube
    (take Λ = identity). -/
theorem ForwardTube_subset_ComplexExtended (d n : ℕ) [NeZero d] :
    ForwardTube d n ⊆ ComplexExtendedForwardTube d n := by
  intro z hz
  refine ⟨⟨1, ?_, ?_⟩, z, hz, ?_⟩
  · -- Identity preserves metric: Σ_α η(α) · δ_{αμ} · δ_{αν} = η(μ) · δ_{μν}
    intro μ ν
    simp only [Matrix.one_apply]
    by_cases h : μ = ν
    · subst h; simp [Finset.sum_ite_eq', Finset.mem_univ]
    · simp only [h, ite_false]
      apply Finset.sum_eq_zero
      intro α _
      split_ifs <;> simp_all
  · simp [Matrix.det_one]
  · ext k μ; simp [Matrix.one_apply, Finset.mem_univ]

/-- The complex extended forward tube is contained in the permuted extended tube
    (take π = identity). -/
theorem ComplexExtended_subset_Permuted (d n : ℕ) [NeZero d] :
    ComplexExtendedForwardTube d n ⊆ PermutedExtendedTube d n := by
  intro z ⟨Λ, w, hw, hz⟩
  simp only [PermutedExtendedTube, Set.mem_iUnion]
  exact ⟨Equiv.refl _, Λ, w, by simpa [PermutedForwardTube] using hw, hz⟩

/-! ### Euclidean Points -/

/-- A point z ∈ ℂ^{n(d+1)} is Euclidean if z_k = (iτ_k, x⃗_k) where τ_k ∈ ℝ
    and x⃗_k ∈ ℝ^d. That is, the time components are purely imaginary and the
    spatial components are real. -/
def IsEuclidean (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  (∀ k : Fin n, (z k 0).re = 0) ∧  -- time component is purely imaginary
  (∀ k : Fin n, ∀ μ : Fin (d + 1), μ ≠ 0 → (z k μ).im = 0)  -- spatial components are real

omit [NeZero d] in
/-- Wick-rotated points are Euclidean. -/
theorem wickRotatePoint_isEuclidean (xs : Fin n → Fin (d + 1) → ℝ) :
    IsEuclidean (fun k => wickRotatePoint (xs k)) := by
  constructor
  · intro k
    simp [wickRotatePoint, Complex.mul_re, Complex.I_re, Complex.I_im]
  · intro k μ hμ
    simp [wickRotatePoint, hμ, Complex.ofReal_im]

/-- Euclidean points with increasing times are in the forward tube.

    If 0 < τ₀ < τ₁ < ... < τₙ₋₁ (strictly increasing positive Euclidean times),
    then the Wick-rotated points (iτ₀, x⃗₀), ..., (iτₙ₋₁, x⃗ₙ₋₁) lie in the forward tube.

    The imaginary part differences are:
      Im(z_k - z_{k-1})₀ = τ_k - τ_{k-1} > 0   (time component)
      Im(z_k - z_{k-1})_μ = 0                     (spatial, μ ≥ 1)
    so η = (τ_k - τ_{k-1}, 0,...,0) has positive time and zero spatial part.
    The Minkowski norm η² = -(τ_k - τ_{k-1})² < 0, so η ∈ V₊. -/
theorem euclidean_ordered_in_forwardTube
    (xs : Fin n → Fin (d + 1) → ℝ)
    (hord : ∀ k j : Fin n, k < j → xs k 0 < xs j 0)
    (hpos : ∀ k : Fin n, xs k 0 > 0) :
    (fun k => wickRotatePoint (xs k)) ∈ ForwardTube d n := by
  intro k
  -- η_μ = Im(z_k μ - prev μ) where prev = 0 if k=0, z_{k-1} if k≥1
  -- For Wick-rotated points: η = (τ_k - τ_{k-1}, 0, ..., 0)
  -- which has positive time and negative Minkowski norm
  constructor
  · -- η 0 > 0 (positive time component)
    dsimp
    split_ifs with hk
    · -- k = 0: Im(wickRotatePoint(xs k) 0 - 0) = xs k 0 > 0
      simp only [wickRotatePoint, ite_true, Pi.zero_apply,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
        Complex.zero_im, sub_zero, zero_add]
      exact hpos k
    · -- k ≥ 1: Im(i*τ_k - i*τ_{k-1}) = τ_k - τ_{k-1} > 0
      simp only [wickRotatePoint, ite_true,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
      have hlt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
        simp only [Fin.lt_def]; omega
      linarith [hord ⟨k.val - 1, by omega⟩ k hlt]
  · -- minkowskiNormSq η < 0 (purely timelike, so η² = -η₀² < 0)
    dsimp
    simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature]
    -- Split sum: i=0 term + sum of spatial terms
    rw [Fin.sum_univ_succ]
    simp only [Fin.succ_ne_zero, ite_false, ite_true, one_mul]
    -- Spatial imaginary parts vanish: Im(wickRotatePoint x μ) = 0 for μ ≠ 0
    have hspatial : ∀ i : Fin d,
        (wickRotatePoint (xs k) i.succ).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) i.succ).im = 0 := by
      intro i
      simp only [wickRotatePoint, Fin.succ_ne_zero, ite_false, Complex.ofReal_im]
      split_ifs with hk
      · simp [Complex.zero_im]
      · simp [wickRotatePoint, Fin.succ_ne_zero, Complex.ofReal_im]
    simp only [hspatial, mul_zero, Finset.sum_const_zero, add_zero]
    -- Goal: -1 * η₀ * η₀ < 0, where η₀ = time difference > 0
    have heta_pos : (wickRotatePoint (xs k) 0).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) 0).im > 0 := by
      simp only [wickRotatePoint, ite_true, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
      split_ifs with hk
      · simp only [Pi.zero_apply, Complex.zero_im, sub_zero]; exact hpos k
      · simp only [wickRotatePoint, ite_true, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        have hlt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
          simp only [Fin.lt_def]; omega
        linarith [hord ⟨k.val - 1, by omega⟩ k hlt]
    nlinarith [sq_nonneg ((wickRotatePoint (xs k) 0).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) 0).im)]

/-- For any configuration of distinct Euclidean points with positive times,
    there exists a permutation that orders the times, placing the permuted
    configuration in the forward tube.

    This is the key geometric fact: **all** distinct positive-time Euclidean
    points lie in the permuted extended tube, not just the time-ordered ones.

    The positive time condition is natural for Osterwalder-Schrader reconstruction,
    where Schwinger functions are defined for positive Euclidean times. -/
theorem euclidean_distinct_in_permutedTube {n : ℕ}
    (xs : Fin n → Fin (d + 1) → ℝ)
    (hdistinct : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0)
    (hpos : ∀ i : Fin n, xs i 0 > 0) :
    (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n := by
  -- Step 1: Find a sorting permutation π such that times are strictly increasing
  let π := Tuple.sort (fun k => xs k 0)
  have hmono := Tuple.monotone_sort (fun k => xs k 0)
  -- Times are distinct, hence injective
  have hinj : Function.Injective (fun k => xs k 0) := by
    intro i j h; by_contra hij; exact hdistinct i j hij h
  -- Monotone + injective = strictly monotone
  have hstrict : StrictMono ((fun k => xs k 0) ∘ π) :=
    hmono.strictMono_of_injective (hinj.comp π.injective)
  -- Step 2: The permuted configuration is time-ordered with positive times
  have hord : ∀ k j : Fin n, k < j → xs (π k) 0 < xs (π j) 0 :=
    fun k j hkj => hstrict hkj
  have hpos' : ∀ k : Fin n, xs (π k) 0 > 0 := fun k => hpos (π k)
  -- Step 3: Apply euclidean_ordered_in_forwardTube to get forward tube membership
  have hfwd : (fun k => wickRotatePoint (xs (π k))) ∈ ForwardTube d n :=
    euclidean_ordered_in_forwardTube (fun k => xs (π k)) hord hpos'
  -- Step 4: This gives PermutedForwardTube membership (by definition)
  -- PermutedForwardTube d n π = { z | (fun k => z (π k)) ∈ ForwardTube d n }
  -- So z = (fun k => wickRotatePoint (xs k)) is in PermutedForwardTube d n π
  -- Step 5: Use the identity complex Lorentz to get PermutedExtendedTube membership
  simp only [PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨π, ?_⟩
  -- Construct the identity complex Lorentz transformation
  refine ⟨⟨1, ?_, by simp [Matrix.det_one]⟩, fun k => wickRotatePoint (xs k), hfwd, ?_⟩
  · -- Identity preserves metric
    intro μ ν
    simp only [Matrix.one_apply]
    by_cases h : μ = ν
    · subst h; simp [Finset.sum_ite_eq', Finset.mem_univ]
    · simp only [h, ite_false]
      apply Finset.sum_eq_zero; intro α _; split_ifs <;> simp_all
  · -- z = 1 · w = w
    ext k μ; simp [Matrix.one_apply, Finset.mem_univ]

/-! ### Edge-of-the-Wedge Theorem -/

/- The edge-of-the-wedge theorem (Bogoliubov).

    This is a deep result in several complex variables. The simplest version states:

    Let C ⊂ ℝⁿ be an open convex cone, and let T₊ = ℝⁿ + iC, T₋ = ℝⁿ - iC be
    the corresponding tube domains. If f₊ : T₊ → ℂ and f₋ : T₋ → ℂ are holomorphic,
    and their boundary values (as distributions) agree on an open set E ⊂ ℝⁿ:
      lim_{ε→0⁺} f₊(x + iεη) = lim_{ε→0⁺} f₋(x - iεη) for x ∈ E
    then there exists a holomorphic function F on a complex neighborhood of E that
    agrees with f₊ on T₊ ∩ U and f₋ on T₋ ∩ U for some open U.

    This is the mathematical backbone of the BHW theorem: it allows "gluing"
    analytic continuations from overlapping tube domains. -/

/-- A tube domain: the set of points whose imaginary parts lie in an open cone. -/
def TubeDomain {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  { z | (fun i => (z i).im) ∈ C }

/-! ### Slice Maps for Multi-dimensional Edge-of-the-Wedge

The key technique for the multi-dimensional edge-of-the-wedge theorem is slicing:
given a direction η in the cone C, the affine map w ↦ x_ℂ + w · η_ℂ embeds ℂ into ℂᵐ.
The imaginary part of the slice is Im(w) · η, so:
- Upper half-plane (Im w > 0) maps to TubeDomain(C) when η ∈ C
- Lower half-plane (Im w < 0) maps to TubeDomain(-C) when η ∈ C

This reduces the multi-dimensional problem to the 1D edge-of-the-wedge theorem
applied to each slice. -/

/-- The affine slice map w ↦ x_ℂ + w · η_ℂ embedding ℂ into ℂᵐ along direction η.
    Im(sliceMap x η w) = Im(w) · η, so:
    - Upper half-plane (Im w > 0) maps to TubeDomain(C) when η ∈ C
    - Lower half-plane (Im w < 0) maps to TubeDomain(-C) when η ∈ C -/
def sliceMap {m : ℕ} (x η : Fin m → ℝ) : ℂ → (Fin m → ℂ) :=
  fun w i => (x i : ℂ) + w * (η i : ℂ)

theorem sliceMap_im_eq_smul {m : ℕ} (x η : Fin m → ℝ) (w : ℂ) :
    (fun i => (sliceMap x η w i).im) = w.im • η := by
  ext i
  simp only [sliceMap, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, mul_zero, zero_add, Pi.smul_apply, smul_eq_mul]

theorem sliceMap_at_zero {m : ℕ} (x η : Fin m → ℝ) :
    sliceMap x η 0 = fun i => (x i : ℂ) := by
  ext i; simp [sliceMap]

theorem sliceMap_upper_mem_tubeDomain {m : ℕ} {C : Set (Fin m → ℝ)} {x : Fin m → ℝ}
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    {η : Fin m → ℝ} (hη : η ∈ C) {w : ℂ} (hw : w.im > 0) :
    sliceMap x η w ∈ TubeDomain C := by
  show (fun i => (sliceMap x η w i).im) ∈ C
  rw [sliceMap_im_eq_smul]; exact hcone w.im η hw hη

theorem sliceMap_lower_mem_neg_tubeDomain {m : ℕ} {C : Set (Fin m → ℝ)} {x : Fin m → ℝ}
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    {η : Fin m → ℝ} (hη : η ∈ C) {w : ℂ} (hw : w.im < 0) :
    sliceMap x η w ∈ TubeDomain (Neg.neg '' C) := by
  show (fun i => (sliceMap x η w i).im) ∈ Neg.neg '' C
  rw [sliceMap_im_eq_smul]
  exact ⟨(-w.im) • η, hcone (-w.im) η (by linarith) hη,
    by ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]⟩

theorem differentiable_sliceMap {m : ℕ} (x η : Fin m → ℝ) :
    Differentiable ℂ (sliceMap x η) := by
  intro w; unfold sliceMap; rw [differentiableAt_pi]; intro i
  fun_prop

theorem continuous_sliceMap {m : ℕ} (x η : Fin m → ℝ) :
    Continuous (sliceMap x η) :=
  (differentiable_sliceMap x η).continuous

theorem sliceMap_real {m : ℕ} (x η : Fin m → ℝ) (t : ℝ) :
    sliceMap x η (t : ℂ) = fun i => ((x i + t * η i : ℝ) : ℂ) := by
  ext i; simp [sliceMap, Complex.ofReal_add, Complex.ofReal_mul]

/-! ### Tube Domain Infrastructure -/

/-- A tube domain over an open cone is open. -/
theorem tubeDomain_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (TubeDomain C) := by
  have : TubeDomain C = (fun z : Fin m → ℂ => fun i => (z i).im) ⁻¹' C := rfl
  rw [this]
  exact hC.preimage (continuous_pi fun i => Complex.continuous_im.comp (continuous_apply i))

/-- The negation image of an open set in `Fin m → ℝ` is open. -/
theorem neg_image_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (Neg.neg '' C) := by
  have heq : Neg.neg '' C = Neg.neg ⁻¹' C := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨-x, hx, neg_neg x⟩
  rw [heq]
  exact hC.preimage (continuous_pi fun i => continuous_neg.comp (continuous_apply i))

/-- Tube domains over C and -C are disjoint when C is convex and 0 ∉ C. -/
theorem tubeDomain_disjoint_neg {m : ℕ} {C : Set (Fin m → ℝ)}
    (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C) :
    Disjoint (TubeDomain C) (TubeDomain (Neg.neg '' C)) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  apply h0
  -- hz1: Im(z) ∈ C, hz2: Im(z) ∈ Neg.neg '' C (so -Im(z) ∈ C)
  obtain ⟨y, hy, hy_eq⟩ := hz2
  -- y ∈ C and -y = Im(z), so Im(z) = -y and -Im(z) = y ∈ C
  have h_neg_im : -(fun i => (z i).im) ∈ C := by
    have : -(fun i => (z i).im) = y := by
      ext i; have h := congr_fun hy_eq i
      simp only [Pi.neg_apply] at h ⊢; linarith
    rw [this]; exact hy
  -- 0 = (1/2) • Im(z) + (1/2) • (-Im(z)) ∈ C by convexity
  have h_zero : (0 : Fin m → ℝ) = (1/2 : ℝ) • (fun i => (z i).im) + (1/2 : ℝ) • (-(fun i => (z i).im)) := by
    ext i; simp [Pi.smul_apply, Pi.add_apply, Pi.neg_apply]
  rw [h_zero]
  exact hconv hz1 h_neg_im (by positivity) (by positivity) (by norm_num)

/-- Holomorphic extension along a 1D slice through a cone direction.

    For each `x₀ ∈ E` and `η ∈ C`, composing `f_±` with `sliceMap x₀ η` gives
    1D holomorphic functions on UHP/LHP with matching boundary values. The 1D
    edge-of-the-wedge theorem provides holomorphic extension in the η-direction.

    This is the key dimensional reduction step: it shows that f₊ and f₋ have a
    common holomorphic extension along each cone direction through each boundary point. -/
theorem edge_of_the_wedge_slice {m : ℕ}
    (C : Set (Fin m → ℝ)) (_hC : IsOpen C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (hE : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus (nhdsWithin (fun i => (x i : ℂ)) (TubeDomain C)) (nhds (bv x)))
    (hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus (nhdsWithin (fun i => (x i : ℂ)) (TubeDomain (Neg.neg '' C))) (nhds (bv x)))
    (x₀ : Fin m → ℝ) (hx₀ : x₀ ∈ E) (η : Fin m → ℝ) (hη : η ∈ C) :
    ∃ (V : Set ℂ) (G : ℂ → ℂ),
      IsOpen V ∧ (0 : ℂ) ∈ V ∧
      DifferentiableOn ℂ G V ∧
      (∀ w ∈ V, w.im > 0 → G w = f_plus (sliceMap x₀ η w)) ∧
      (∀ w ∈ V, w.im < 0 → G w = f_minus (sliceMap x₀ η w)) := by
  -- Step 1: Find δ > 0 such that x₀ + t • η ∈ E for all |t| < δ
  -- Use continuity of t ↦ x₀ + t • η at 0
  have hcont_affine : Continuous (fun t : ℝ => x₀ + t • η) := by continuity
  have haffine_zero : (fun t : ℝ => x₀ + t • η) 0 = x₀ := by simp
  have hmem_preimage : (0 : ℝ) ∈ (fun t : ℝ => x₀ + t • η) ⁻¹' E := by
    simp [Set.mem_preimage, hx₀]
  obtain ⟨δ, hδ_pos, hδ_sub'⟩ := Metric.isOpen_iff.mp
    (hE.preimage hcont_affine) 0 hmem_preimage
  have hδ_sub : ∀ t : ℝ, |t| < δ → x₀ + t • η ∈ E := by
    intro t ht; exact hδ_sub' (by rwa [Metric.mem_ball, Real.dist_eq, sub_zero])
  -- Step 2: Define the 1D functions for the slice
  let g_plus : ℂ → ℂ := fun w =>
    if 0 < w.im then f_plus (sliceMap x₀ η w)
    else bv (fun i => x₀ i + w.re * η i)
  let g_minus : ℂ → ℂ := fun w =>
    if w.im < 0 then f_minus (sliceMap x₀ η w)
    else bv (fun i => x₀ i + w.re * η i)
  -- Step 3: Apply edge_of_the_wedge_1d with interval (-δ, δ)
  have hab : -δ < δ := by linarith
  -- g_plus is holomorphic on UHP (agrees with f_plus ∘ sliceMap there)
  have hg_plus_holo : DifferentiableOn ℂ g_plus EOW.UpperHalfPlane := by
    have h_comp : DifferentiableOn ℂ (fun w => f_plus (sliceMap x₀ η w)) EOW.UpperHalfPlane :=
      hf_plus.comp (differentiable_sliceMap x₀ η).differentiableOn
        (fun w hw => sliceMap_upper_mem_tubeDomain hcone hη hw)
    exact h_comp.congr (fun w hw => if_pos hw)
  -- g_minus is holomorphic on LHP
  have hg_minus_holo : DifferentiableOn ℂ g_minus EOW.LowerHalfPlane := by
    have h_comp : DifferentiableOn ℂ (fun w => f_minus (sliceMap x₀ η w)) EOW.LowerHalfPlane :=
      hf_minus.comp (differentiable_sliceMap x₀ η).differentiableOn
        (fun w hw => sliceMap_lower_mem_neg_tubeDomain hcone hη hw)
    exact h_comp.congr (fun w hw => if_pos hw)
  -- Boundary values match: g_plus(t) = g_minus(t) for t ∈ (-δ, δ)
  have hmatch' : ∀ x : ℝ, -δ < x → x < δ → g_plus x = g_minus x := by
    intro t _ _
    simp only [g_plus, g_minus, Complex.ofReal_im, lt_irrefl, ite_false]
  -- Boundary value from above: g_plus approaches g_plus(t) from UHP
  -- This requires translating the multi-D boundary value (hf_plus_bv) to 1D via sliceMap
  have hcont_plus : ∀ x : ℝ, -δ < x → x < δ →
      Filter.Tendsto g_plus (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (g_plus x)) := by
    intro t ht_lo ht_hi
    have ht_abs : |t| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    have ht_E : x₀ + t • η ∈ E := hδ_sub t ht_abs
    have hslice_eq : sliceMap x₀ η (↑t) = fun i => ↑((x₀ + t • η) i) := by
      rw [sliceMap_real]; ext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    -- sliceMap maps nhdsWithin t UHP into nhdsWithin (x₀+t•η)_ℂ (TubeDomain C)
    have hslice_tends : Filter.Tendsto (sliceMap x₀ η)
        (nhdsWithin (↑t) EOW.UpperHalfPlane)
        (nhdsWithin (fun i => ↑((x₀ + t • η) i)) (TubeDomain C)) := by
      have hcw : ContinuousWithinAt (sliceMap x₀ η) EOW.UpperHalfPlane (↑t) :=
        (continuous_sliceMap x₀ η).continuousWithinAt
      have h := hcw.tendsto_nhdsWithin
        (fun w hw => sliceMap_upper_mem_tubeDomain hcone hη hw)
      rwa [hslice_eq] at h
    -- Compose: f_plus ∘ sliceMap → bv(x₀+t•η) from nhdsWithin t UHP
    have h_comp := (hf_plus_bv (x₀ + t • η) ht_E).comp hslice_tends
    -- g_plus ↑t = bv(x₀+t•η)
    have hg_t_eq : g_plus (↑t) = bv (x₀ + t • η) := if_neg (by simp [Complex.ofReal_im])
    rw [hg_t_eq]
    have key : Filter.map g_plus (nhdsWithin (↑t) EOW.UpperHalfPlane) =
               Filter.map (f_plus ∘ sliceMap x₀ η) (nhdsWithin (↑t) EOW.UpperHalfPlane) :=
      Filter.map_congr (eventually_nhdsWithin_of_forall fun w hw => if_pos hw)
    change Filter.map g_plus _ ≤ _
    rw [key]
    exact h_comp
  -- Boundary value from below (symmetric argument)
  have hcont_minus : ∀ x : ℝ, -δ < x → x < δ →
      Filter.Tendsto g_minus (nhdsWithin (x : ℂ) EOW.LowerHalfPlane) (nhds (g_minus x)) := by
    intro t ht_lo ht_hi
    have ht_abs : |t| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    have ht_E : x₀ + t • η ∈ E := hδ_sub t ht_abs
    have hslice_eq : sliceMap x₀ η (↑t) = fun i => ↑((x₀ + t • η) i) := by
      rw [sliceMap_real]; ext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hslice_tends : Filter.Tendsto (sliceMap x₀ η)
        (nhdsWithin (↑t) EOW.LowerHalfPlane)
        (nhdsWithin (fun i => ↑((x₀ + t • η) i)) (TubeDomain (Neg.neg '' C))) := by
      have hcw : ContinuousWithinAt (sliceMap x₀ η) EOW.LowerHalfPlane (↑t) :=
        (continuous_sliceMap x₀ η).continuousWithinAt
      have h := hcw.tendsto_nhdsWithin
        (fun w hw => sliceMap_lower_mem_neg_tubeDomain hcone hη hw)
      rwa [hslice_eq] at h
    have h_comp := (hf_minus_bv (x₀ + t • η) ht_E).comp hslice_tends
    have hg_t_eq : g_minus (↑t) = bv (x₀ + t • η) := if_neg (by simp [Complex.ofReal_im])
    rw [hg_t_eq]
    have key : Filter.map g_minus (nhdsWithin (↑t) EOW.LowerHalfPlane) =
               Filter.map (f_minus ∘ sliceMap x₀ η) (nhdsWithin (↑t) EOW.LowerHalfPlane) :=
      Filter.map_congr (eventually_nhdsWithin_of_forall fun w hw => if_pos hw)
    change Filter.map g_minus _ ≤ _
    rw [key]
    exact h_comp
  -- Continuity of boundary value along real line:
  -- g_plus restricted to {Im = 0} is t ↦ bv(x₀ + t•η), continuous by hbv_cont
  have hbv_cont_1d : ∀ x₀' : ℝ, -δ < x₀' → x₀' < δ →
      Filter.Tendsto g_plus (nhdsWithin (x₀' : ℂ) {c : ℂ | c.im = 0})
        (nhds (g_plus x₀')) := by
    intro t ht_lo ht_hi
    have ht_abs : |t| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    have ht_E : x₀ + t • η ∈ E := hδ_sub t ht_abs
    have hg_t_eq : g_plus (↑t) = bv (x₀ + t • η) := if_neg (by simp [Complex.ofReal_im])
    rw [hg_t_eq]
    -- g_plus = bv ∘ affine on {Im = 0}
    have heq : ∀ᶠ (c : ℂ) in nhdsWithin (↑t) {c : ℂ | c.im = 0},
        g_plus c = bv (fun i => x₀ i + c.re * η i) :=
      eventually_nhdsWithin_of_forall fun c (hc : c.im = 0) =>
        if_neg (by simp [hc])
    have hcont_bv : Filter.Tendsto (fun c : ℂ => bv (fun i => x₀ i + c.re * η i))
        (nhdsWithin (↑t) {c : ℂ | c.im = 0}) (nhds (bv (x₀ + t • η))) := by
      have h_at_t : bv (fun i => x₀ i + (↑t : ℂ).re * η i) = bv (x₀ + t • η) := by
        congr 1
      rw [← h_at_t]
      have hmem : (fun i : Fin m => x₀ i + (↑t : ℂ).re * η i) ∈ E := by
        convert ht_E using 1
      exact ((hbv_cont.continuousAt (hE.mem_nhds hmem)).comp
        (continuous_pi fun i => continuous_const.add
          (Complex.continuous_re.mul continuous_const)).continuousAt).continuousWithinAt
    change Filter.map g_plus _ ≤ _
    rw [Filter.map_congr heq]
    exact hcont_bv
  -- Apply 1D EOW
  obtain ⟨V, G, hV_open, _, _, hV_int, hG_holo, hG_plus, hG_minus, _⟩ :=
    edge_of_the_wedge_1d (-δ) δ hab g_plus g_minus hg_plus_holo hg_minus_holo
      hcont_plus hcont_minus hmatch' hbv_cont_1d
  -- Step 4: Translate back to multi-D
  refine ⟨V, G, hV_open, hV_int 0 (by linarith) (by linarith), hG_holo, ?_, ?_⟩
  · -- G agrees with f_plus ∘ sliceMap on V ∩ UHP
    intro w hw_V hw_im
    have h := hG_plus w (Set.mem_inter hw_V hw_im)
    simp only [g_plus, if_pos hw_im] at h; exact h
  · -- G agrees with f_minus ∘ sliceMap on V ∩ LHP
    intro w hw_V hw_im
    have h := hG_minus w (Set.mem_inter hw_V hw_im)
    simp only [g_minus, if_pos hw_im] at h; exact h

/-- **The Edge-of-the-Wedge Theorem** (Bogoliubov, 1956).

    Two holomorphic functions on opposite tube domains with matching continuous
    boundary values on a real open set extend to a unique holomorphic function
    on a complex neighborhood.

    Proved via `SCV.edge_of_the_wedge_theorem` in `SCV/TubeDomainExtension.lean`,
    using iterated Cauchy integrals on polydiscs.

    **References:**
    - Bogoliubov, N.N. (1956). *On the theory of quantized fields*. ICM report.
    - Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-16.
    - Rudin, W. (1971). *Lectures on the edge-of-the-wedge theorem*. CBMS 6.

    **Hypotheses:**
    - `C` is an open convex cone (not containing the origin) in `ℝᵐ`,
      closed under positive scalar multiplication (`hcone`)
    - `f_plus`, `f_minus` are holomorphic on the tube domains `ℝᵐ + iC` and `ℝᵐ - iC`
    - `bv` is a continuous function on the open set `E ⊂ ℝᵐ` giving the common
      boundary value, with `f_±` approaching `bv` in the `nhdsWithin` sense -/
theorem edge_of_the_wedge {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C)
    (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
    (hCne : C.Nonempty)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (hE : IsOpen E)
    (bv : (Fin m → ℝ) → ℂ) (hbv_cont : ContinuousOn bv E)
    (hf_plus_bv : ∀ x ∈ E,
      Filter.Tendsto f_plus
        (nhdsWithin (fun i => (x i : ℂ)) (TubeDomain C)) (nhds (bv x)))
    (hf_minus_bv : ∀ x ∈ E,
      Filter.Tendsto f_minus
        (nhdsWithin (fun i => (x i : ℂ)) (TubeDomain (Neg.neg '' C))) (nhds (bv x))) :
    ∃ (U : Set (Fin m → ℂ)) (F : (Fin m → ℂ) → ℂ),
      IsOpen U ∧
      (∀ x ∈ E, (fun i => (x i : ℂ)) ∈ U) ∧
      DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ TubeDomain C, F z = f_plus z) ∧
      (∀ z ∈ U ∩ TubeDomain (Neg.neg '' C), F z = f_minus z) ∧
      -- Uniqueness: any holomorphic function on U agreeing with f_plus on the
      -- positive tube must agree with F everywhere on U (by the identity theorem,
      -- since U ∩ TubeDomain C is open and nonempty).
      (∀ (G : (Fin m → ℂ) → ℂ), DifferentiableOn ℂ G U →
        (∀ z ∈ U ∩ TubeDomain C, G z = f_plus z) → ∀ z ∈ U, G z = F z) :=
  -- Proved in SCV/TubeDomainExtension.lean. The local TubeDomain and SCV.TubeDomain
  -- are definitionally equal, as is `fun i => (x i : ℂ)` and `SCV.realEmbed x`.
  SCV.edge_of_the_wedge_theorem C hC hconv h0 hcone hCne f_plus f_minus
    hf_plus hf_minus E hE bv hbv_cont hf_plus_bv hf_minus_bv

/-! ### Bargmann-Hall-Wightman Theorem -/

/-! ### Bridge lemmas: ForwardTube and PermutedExtendedTube equivalence

These lemmas connect the BHW infrastructure (from `Connectedness.lean`, which uses
`LorentzLieGroup.minkowskiSignature` and no `[NeZero d]`) with the Wightman definitions
(from `WightmanAxioms.lean`, which uses `MinkowskiSpace.metricSignature` and `[NeZero d]`). -/

/-- The BHW forward tube equals the Wightman forward tube. -/
theorem BHW_forwardTube_eq : BHW.ForwardTube d n = ForwardTube d n := by
  ext z; simp only [BHW.ForwardTube, ForwardTube, Set.mem_setOf_eq]
  exact forall_congr' fun k => inOpenForwardCone_iff _

/-- The BHW permuted forward tube equals the Wightman permuted forward tube. -/
theorem BHW_permutedForwardTube_eq (π : Equiv.Perm (Fin n)) :
    BHW.PermutedForwardTube d n π = PermutedForwardTube d n π := by
  ext z; simp only [BHW.PermutedForwardTube, PermutedForwardTube, Set.mem_setOf_eq]
  rw [← BHW_forwardTube_eq]

/-- The BHW permuted extended tube equals the Wightman permuted extended tube. -/
theorem BHW_permutedExtendedTube_eq :
    BHW.PermutedExtendedTube d n = PermutedExtendedTube d n := by
  have hft := BHW_forwardTube_eq (d := d) (n := n)
  ext z
  simp only [BHW.PermutedExtendedTube, PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq,
    BHW.PermutedForwardTube, PermutedForwardTube]
  constructor
  · rintro ⟨π, Λ, w, hw, hz⟩
    refine ⟨π, Λ, w, hft ▸ hw, ?_⟩
    rw [hz]; rfl
  · rintro ⟨π, Λ, w, hw, hz⟩
    refine ⟨π, Λ, w, hft ▸ hw, ?_⟩
    rw [hz]; rfl

/-- **The Bargmann-Hall-Wightman (BHW) theorem.**

    Given a holomorphic function F on the forward tube T_n that is:
    1. Invariant under the real Lorentz group L₊↑
    2. Continuously extends to the real boundary (`hF_bv`)
    3. Has boundary values satisfying local commutativity at spacelike pairs (`hF_local`)

    Then F extends uniquely to a holomorphic function F_ext on the permuted extended
    tube T''_n, and the extension is:
    1. Invariant under the complex Lorentz group L₊(ℂ)
    2. Invariant under all permutations of the arguments
    3. Unique (any other holomorphic extension agreeing with F on the forward tube
       must equal F_ext on the permuted extended tube)

    **Note on `hF_bv`:** Real points lie outside the forward tube (Im = 0 ∉ V₊),
    so F is not a priori meaningful at real points. The `hF_bv` hypothesis ensures
    that F(x_ℂ) equals the distributional boundary value lim_{ε→0⁺} F(x + iεη),
    making `hF_local` well-defined.

    **Proof:** Delegates to `BHW.bargmann_hall_wightman_theorem` from
    `Connectedness.lean` via the `AxiomBridge` type conversions.

    References:
    - Bargmann, Hall, Wightman (1957), Nuovo Cimento 5, 1-14
    - Streater & Wightman, PCT Spin and Statistics, Theorem 2-11
    - Jost (1965), The General Theory of Quantized Fields, Ch. IV -/
theorem bargmann_hall_wightman (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : LorentzGroup.Restricted (d := d))
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        MinkowskiSpace.minkowskiNormSq d
          (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = F_ext z) ∧
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) ∧
      (∀ (G : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ G (PermutedExtendedTube d n) →
        (∀ z ∈ ForwardTube d n, G z = F z) →
        ∀ z ∈ PermutedExtendedTube d n, G z = F_ext z) := by
  -- Convert hypotheses from Wightman types to BHW types
  have hft_eq := BHW_forwardTube_eq (d := d) (n := n)
  have hpet_eq := BHW_permutedExtendedTube_eq (d := d) (n := n)
  have hF_holo' : DifferentiableOn ℂ F (BHW.ForwardTube d n) :=
    hft_eq ▸ hF_holo
  have hF_lorentz' : ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z := by
    intro Λ z hz
    have hz' : z ∈ ForwardTube d n := hft_eq ▸ hz
    exact hF_lorentz (restrictedLorentzGroupToWightman Λ) z hz'
  have hF_bv' : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (BHW.ForwardTube d n) (fun k μ => (x k μ : ℂ)) :=
    fun x => hft_eq ▸ hF_bv x
  have hF_local' : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, LorentzLieGroup.minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)) := by
    intro i hi x hsp
    exact hF_local i hi x ((spacelike_condition_iff _).mp hsp)
  -- Apply BHW theorem from Connectedness.lean
  obtain ⟨F_ext, h1, h2, h3, h4, h5⟩ :=
    BHW.bargmann_hall_wightman_theorem n F hF_holo' hF_lorentz' hF_bv' hF_local'
  -- Convert the result back from BHW types to Wightman types
  refine ⟨F_ext, ?_, ?_, ?_, ?_, ?_⟩
  · -- DifferentiableOn on PermutedExtendedTube
    rwa [← hpet_eq]
  · -- Restriction to ForwardTube
    intro z hz
    exact h2 z (hft_eq ▸ hz)
  · -- Complex Lorentz invariance
    intro Λ z hz
    have hz' : z ∈ BHW.PermutedExtendedTube d n := hpet_eq ▸ hz
    have := h3 Λ z hz'
    rwa [show BHW.complexLorentzAction Λ z = fun k μ => ∑ ν, Λ.val μ ν * z k ν from rfl] at this
  · -- Permutation invariance
    intro π z hz
    exact h4 π z (hpet_eq ▸ hz)
  · -- Uniqueness
    intro G hG_holo hG_eq z hz
    have hz' : z ∈ BHW.PermutedExtendedTube d n := hpet_eq ▸ hz
    exact h5 G (hpet_eq ▸ hG_holo)
      (fun w hw => hG_eq w (hft_eq ▸ hw)) z hz'

/-! ### Jost Points -/

/-- A Jost point is a real point in the extended forward tube.
    These exist when all (z_k - z_{k-1}) are spacelike.
    At Jost points, the Wightman function takes real (distributional) values,
    and local commutativity can be directly applied. -/
def IsJostPoint (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  z ∈ ComplexExtendedForwardTube d n ∧
  ∀ k : Fin n, ∀ μ : Fin (d + 1), (z k μ).im = 0

/-- At Jost points, all difference vectors are spacelike.
    This is Jost's lemma: if (x₁,...,xₙ) ∈ T'_n ∩ ℝ^{n(d+1)}, then
    (x_k - x_{k-1})² > 0 for all k. -/
theorem jost_lemma (z : Fin n → Fin (d + 1) → ℂ) (hz : IsJostPoint z) :
    ∀ k : Fin n, (k.val ≠ 0) →
    let prev := z ⟨k.val - 1, by omega⟩
    let diff : Fin (d + 1) → ℝ := fun μ => (z k μ).re - (prev μ).re
    MinkowskiSpace.minkowskiNormSq d diff > 0 := by
  intro k hk
  -- Extract Λ, w from the extended forward tube membership
  obtain ⟨Λ, w, hw, hz_eq⟩ := hz.1
  -- z is real (all imaginary parts vanish)
  have hz_real := hz.2
  -- Define the complex difference in w-coordinates
  set prev_w : Fin (d + 1) → ℂ := w ⟨k.val - 1, by omega⟩
  set diff_w : Fin (d + 1) → ℂ := fun μ => w k μ - prev_w μ
  -- The imaginary part of diff_w is in the forward cone (from ForwardTube)
  set η : Fin (d + 1) → ℝ := fun μ => (diff_w μ).im
  set ξ : Fin (d + 1) → ℝ := fun μ => (diff_w μ).re
  have hη_cone : InOpenForwardCone d η := by
    have h := hw k; simp only [dif_neg hk] at h; exact h
  -- η is timelike (normSq < 0) and future-directed (η₀ > 0)
  have hη_timelike : MinkowskiSpace.IsTimelike d η := hη_cone.2
  have hη_future : MinkowskiSpace.IsFutureDirected d η := hη_cone.1
  -- z_k - z_{k-1} = Λ · diff_w (linearity of matrix multiplication)
  have hz_diff : ∀ μ, z k μ - z ⟨k.val - 1, by omega⟩ μ =
      ∑ ν, Λ.val μ ν * diff_w ν := by
    intro μ
    simp only [hz_eq, diff_w, prev_w]
    rw [← Finset.sum_sub_distrib
      (f := fun ν => Λ.val μ ν * w k ν)
      (g := fun ν => Λ.val μ ν * w ⟨k.val - 1, by omega⟩ ν)]
    congr 1; ext ν; ring
  -- The image Λ · diff_w is real (since z is real)
  set z_diff : Fin (d + 1) → ℂ := fun μ => ∑ ν, Λ.val μ ν * diff_w ν
  have hz_diff_real : ∀ μ, (z_diff μ).im = 0 := by
    intro μ
    have h := congr_arg Complex.im (hz_diff μ)
    simp only [Complex.sub_im] at h
    rw [hz_real k μ, hz_real ⟨k.val - 1, by omega⟩ μ] at h
    linarith
  -- KEY STEP 1: Q(Λ · diff_w) = Q(diff_w) by metric preservation
  have hQ_inv : MinkowskiSpace.complexMinkowskiQuadratic d z_diff =
      MinkowskiSpace.complexMinkowskiQuadratic d diff_w :=
    MinkowskiSpace.complexQuadratic_lorentz_invariant d Λ.val Λ.metric_preserving diff_w
  -- KEY STEP 2: Q(z_diff) is real since z_diff is a real vector
  have hQ_real : MinkowskiSpace.complexMinkowskiQuadratic d z_diff =
      (MinkowskiSpace.minkowskiNormSq d (fun μ => (z_diff μ).re) : ℂ) :=
    MinkowskiSpace.complexMinkowskiQuadratic_real_vector d z_diff hz_diff_real
  -- KEY STEP 3: diff_w = ξ + iη, so Q(diff_w) has known Re and Im
  have hdiff_decomp : diff_w = fun μ => (ξ μ : ℂ) + (η μ : ℂ) * I := by
    ext μ; exact (Complex.re_add_im (diff_w μ)).symm
  -- The imaginary part of Q(diff_w)
  have hQ_im : (MinkowskiSpace.complexMinkowskiQuadratic d diff_w).im =
      2 * MinkowskiSpace.minkowskiInner d ξ η := by
    conv_lhs => rw [hdiff_decomp]
    exact MinkowskiSpace.complexQuadratic_im d ξ η
  -- The real part of Q(diff_w)
  have hQ_re : (MinkowskiSpace.complexMinkowskiQuadratic d diff_w).re =
      MinkowskiSpace.minkowskiNormSq d ξ - MinkowskiSpace.minkowskiNormSq d η := by
    conv_lhs => rw [hdiff_decomp]
    exact MinkowskiSpace.complexQuadratic_re d ξ η
  -- KEY STEP 4: Since Q(z_diff) is real, Q(diff_w) must also be real,
  -- which gives ⟨ξ, η⟩_M = 0 (Minkowski orthogonality)
  have hQ_is_real : (MinkowskiSpace.complexMinkowskiQuadratic d diff_w).im = 0 := by
    rw [← hQ_inv] at hQ_re hQ_im ⊢
    rw [hQ_real]; simp [Complex.ofReal_im]
  have horth : MinkowskiSpace.minkowskiInner d ξ η = 0 := by
    linarith [hQ_im, hQ_is_real]
  -- KEY STEP 5: η timelike future-directed + ξ ⊥ η → normSq(ξ) ≥ 0
  have hξ_nonneg : MinkowskiSpace.minkowskiNormSq d ξ ≥ 0 :=
    MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg d ξ η
      hη_timelike hη_future horth
  -- KEY STEP 6: normSq(η) < 0 (timelike), so normSq(ξ) - normSq(η) > 0
  have hη_neg : MinkowskiSpace.minkowskiNormSq d η < 0 := hη_timelike
  have hQ_diff_pos : MinkowskiSpace.minkowskiNormSq d ξ -
      MinkowskiSpace.minkowskiNormSq d η > 0 := by linarith
  -- KEY STEP 7: Connect to the goal
  show MinkowskiSpace.minkowskiNormSq d (fun μ => (z k μ).re -
    (z ⟨k.val - 1, by omega⟩ μ).re) > 0
  -- The real diff = Re(z_diff) since z_k - z_{k-1} = z_diff
  have hdiff_eq : (fun μ => (z k μ).re - (z ⟨k.val - 1, by omega⟩ μ).re) =
      fun μ => (z_diff μ).re := by
    ext μ; exact congr_arg Complex.re (hz_diff μ)
  rw [hdiff_eq]
  -- Chain: normSq(Re(z_diff)) = Re(Q(z_diff)) = Re(Q(diff_w)) = normSq(ξ) - normSq(η)
  have key : MinkowskiSpace.minkowskiNormSq d (fun μ => (z_diff μ).re) =
      MinkowskiSpace.minkowskiNormSq d ξ - MinkowskiSpace.minkowskiNormSq d η := by
    -- From hQ_real: Q(z_diff) = ↑(normSq(Re(z_diff)))
    -- From hQ_inv: Q(z_diff) = Q(diff_w)
    -- So normSq(Re(z_diff)) = Re(Q(z_diff)) = Re(Q(diff_w)) = normSq(ξ) - normSq(η)
    have h1 : (MinkowskiSpace.complexMinkowskiQuadratic d z_diff).re =
        MinkowskiSpace.minkowskiNormSq d (fun μ => (z_diff μ).re) := by
      rw [hQ_real]; simp [Complex.ofReal_re]
    have h2 : (MinkowskiSpace.complexMinkowskiQuadratic d z_diff).re =
        MinkowskiSpace.minkowskiNormSq d ξ - MinkowskiSpace.minkowskiNormSq d η := by
      rw [hQ_inv]; exact hQ_re
    linarith [h1, h2]
  linarith [key]

/-! ### Schwinger Functions from Wightman Functions -/

/-- Define Schwinger functions from Wightman functions using analytic continuation.

    Given Wightman functions W_n with analytic continuation W_analytic to the forward tube,
    the Schwinger functions are defined by evaluating W_analytic at Euclidean points:

      S_n(τ₁, x⃗₁, ..., τₙ, x⃗ₙ) = W_analytic_n(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ)

    for τ₁ > τ₂ > ... > τₙ > 0 (time-ordered Euclidean points lie in the forward tube).

    By the BHW theorem, the analytic continuation extends to the permuted extended tube,
    making S_n well-defined and symmetric for all distinct Euclidean points. -/
def SchwingerFromWightman (d : ℕ) [NeZero d]
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (n : ℕ) → (Fin n → Fin (d + 1) → ℝ) → ℂ :=
  fun n xs => W_analytic n (fun k => wickRotatePoint (xs k))

/-- The ℂ-linear Wick rotation: maps complex coordinates to Wick-rotated coordinates.
    This is the holomorphic version of `wickRotatePoint`: instead of requiring real inputs,
    it acts on complex inputs by (z₀, z₁, ..., z_d) ↦ (I·z₀, z₁, ..., z_d).

    This is a ℂ-linear map, hence holomorphic (entire). On real inputs it agrees
    with `wickRotatePoint`. -/
def complexWickRotate (z : Fin n → Fin (d + 1) → ℂ) : Fin n → Fin (d + 1) → ℂ :=
  fun k μ => if μ = 0 then I * z k 0 else z k μ

omit [NeZero d] in
/-- The ℂ-linear Wick rotation agrees with `wickRotatePoint` on real inputs. -/
theorem complexWickRotate_eq_wickRotatePoint (xs : Fin n → Fin (d + 1) → ℝ) :
    complexWickRotate (fun k μ => (xs k μ : ℂ)) =
    fun k => wickRotatePoint (xs k) := by
  ext k μ
  simp [complexWickRotate, wickRotatePoint]

omit [NeZero d] in
/-- The ℂ-linear Wick rotation is differentiable everywhere. -/
theorem differentiable_complexWickRotate :
    Differentiable ℂ (complexWickRotate (d := d) (n := n)) := by
  intro xs
  unfold complexWickRotate
  rw [differentiableAt_pi]
  intro k
  rw [differentiableAt_pi]
  intro μ
  by_cases hμ : μ = 0
  · simp only [hμ, ite_true]
    exact DifferentiableAt.const_mul (by fun_prop) I
  · simp only [hμ, ite_false]
    fun_prop

/-- The Schwinger functions defined from Wightman's analytic continuation are
    differentiable on the set of Euclidean configurations whose Wick-rotated
    images lie in the permuted extended tube.

    This follows from the chain rule: SchwingerFromWightman is the composition
    of the holomorphic W_analytic with the ℂ-linear Wick rotation map
    z ↦ (I·z₀, z₁, ..., z_d), which is holomorphic (entire). -/
theorem schwingerFromWightman_analytic
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW : ∀ n, DifferentiableOn ℂ (W_analytic n) (PermutedExtendedTube d n))
    (n : ℕ) :
    -- The composition W_analytic ∘ complexWickRotate is ℂ-differentiable
    -- on the preimage of the permuted extended tube
    DifferentiableOn ℂ
      (fun xs : Fin n → Fin (d + 1) → ℂ =>
        W_analytic n (complexWickRotate xs))
      { xs | complexWickRotate xs ∈ PermutedExtendedTube d n } := by
  show DifferentiableOn ℂ (W_analytic n ∘ complexWickRotate) _
  exact (hW n).comp differentiable_complexWickRotate.differentiableOn (fun _ hxs => hxs)

/-! ### Temperedness of Schwinger Functions

The temperedness of Schwinger functions (OS axiom E0) requires bounding
|S_n(f)| for Schwartz test functions f. This follows from the temperedness
of Wightman functions (R0) together with the geometry of the Wick rotation.

OS I, Proposition 5.1 provides the key geometric estimate. -/

/-- The geometric domain Ω_n from OS I, Proposition 5.1.
    This is the set of Euclidean n-point configurations where the Wick-rotated
    points are "sufficiently inside" the forward tube for temperedness estimates. -/
def OmegaRegion (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℝ) :=
  { x | ∀ i j : Fin n, i ≠ j → x i ≠ x j }

/-! ### Key Properties for OS Axiom Verification -/

omit [NeZero d] in
/-- The Wick rotation intertwines Euclidean rotations with complex Lorentz transformations:
    wickRotatePoint(R · x) = (ofEuclidean R) · wickRotatePoint(x)

    For R ∈ SO(d+1), the diagram commutes:
      ℝ^{d+1} --R--> ℝ^{d+1}
        |                |
    wick             wick
        |                |
      ℂ^{d+1} --Λ_R-> ℂ^{d+1}  -/
theorem wickRotatePoint_ofEuclidean
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (x : Fin (d + 1) → ℝ) :
    ∀ μ : Fin (d + 1),
      wickRotatePoint (R.mulVec x) μ =
      ∑ ν, (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val μ ν *
        wickRotatePoint x ν := by
  intro μ
  simp only [wickRotatePoint, ComplexLorentzGroup.ofEuclidean, Matrix.mulVec, dotProduct]
  -- Each summand on RHS: (wμ * R(μ,ν) * wν⁻¹) * wickRotatePoint(x)(ν)
  -- For ν=0: wμ * R(μ,0) * (-I) * (I * x(0)) = wμ * R(μ,0) * x(0)  [since -I*I = 1]
  -- For ν≠0: wμ * R(μ,ν) * 1 * x(ν) = wμ * R(μ,ν) * x(ν)
  -- So RHS = wμ * Σ_ν R(μ,ν) * x(ν) = LHS
  -- First, simplify each summand via -I*I = 1
  have simplify_summand : ∀ ν : Fin (d + 1),
      (if μ = 0 then I else (1 : ℂ)) * ↑(R μ ν) * (if ν = 0 then -I else 1) *
      (if ν = 0 then I * ↑(x 0) else ↑(x ν)) =
      (if μ = 0 then I else (1 : ℂ)) * ↑(R μ ν) * ↑(x ν) := by
    intro ν
    by_cases hν : ν = (0 : Fin (d + 1))
    · subst hν; simp only [ite_true]
      rw [show (if μ = 0 then I else (1 : ℂ)) * ↑(R μ 0) * -I * (I * ↑(x 0)) =
        (if μ = 0 then I else (1 : ℂ)) * ↑(R μ 0) * ↑(x 0) * (-I * I) from by ring]
      rw [show (-I : ℂ) * I = -(I * I) from by ring, ← sq, Complex.I_sq]; ring
    · simp only [hν, ite_false]; ring
  simp_rw [simplify_summand]
  -- Now RHS = Σ_ν wμ * ↑(R(μ,ν)) * ↑(x(ν)) = wμ * Σ_ν ↑(R(μ,ν) * x(ν))
  by_cases hμ : μ = (0 : Fin (d + 1))
  · subst hμ; simp only [ite_true]
    rw [Complex.ofReal_sum, Finset.mul_sum]
    congr 1; ext ν; push_cast; ring
  · simp only [hμ, ite_false]
    rw [Complex.ofReal_sum]
    congr 1; ext ν; push_cast; ring

omit [NeZero d] in
/-- The transpose of an orthogonal matrix with det 1 also has det 1. -/
private lemma det_transpose_of_SO {R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hR_det : R.det = 1) : R.transpose.det = 1 := by
  rw [Matrix.det_transpose]; exact hR_det

omit [NeZero d] in
/-- The transpose of an orthogonal matrix R (with RᵀR = I) satisfies (Rᵀ)ᵀRᵀ = I. -/
private lemma transpose_orth_of_SO {R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hR_orth : R.transpose * R = 1) : R.transpose.transpose * R.transpose = 1 := by
  rw [Matrix.transpose_transpose]
  have : R * R.transpose = 1 := mul_eq_one_comm.mpr hR_orth
  exact this

omit [NeZero d] in
/-- The matrix product of ofEuclidean(Rᵀ) and ofEuclidean(R) is the identity.

    This follows from the fact that ofEuclidean is a group homomorphism:
    W·Rᵀ·W⁻¹ · W·R·W⁻¹ = W·(RᵀR)·W⁻¹ = W·I·W⁻¹ = I -/
private lemma ofEuclidean_transpose_mul_self
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1) :
    ∀ μ α : Fin (d + 1),
      ∑ ν, (ComplexLorentzGroup.ofEuclidean R.transpose
              (det_transpose_of_SO hR_det) (transpose_orth_of_SO hR_orth)).val μ ν *
           (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val ν α =
      if μ = α then 1 else 0 := by
  intro μ α
  simp only [ComplexLorentzGroup.ofEuclidean, Matrix.transpose_apply]
  -- Each summand: (wμ * Rᵀ(μ,ν) * wν⁻¹) * (wν * R(ν,α) * wα⁻¹)
  -- = wμ * Rᵀ(μ,ν) * R(ν,α) * wα⁻¹  [since wν⁻¹ * wν = 1]
  have simplify : ∀ ν : Fin (d + 1),
      (if μ = 0 then I else (1 : ℂ)) * ↑(R ν μ) * (if ν = 0 then -I else 1) *
      ((if ν = 0 then I else (1 : ℂ)) * ↑(R ν α) * (if α = 0 then -I else 1)) =
      (if μ = 0 then I else (1 : ℂ)) * (if α = 0 then -I else (1 : ℂ)) *
      (↑(R ν μ) * ↑(R ν α)) := by
    intro ν
    by_cases hν : ν = (0 : Fin (d + 1))
    · subst hν; simp only [ite_true]
      rw [show (if μ = 0 then I else (1 : ℂ)) * ↑(R 0 μ) * -I * (I * ↑(R 0 α) *
        (if α = 0 then -I else 1)) =
        (if μ = 0 then I else (1 : ℂ)) * (if α = 0 then -I else (1 : ℂ)) *
        (↑(R 0 μ) * ↑(R 0 α)) * (-I * I) from by ring]
      rw [show (-I : ℂ) * I = -(I * I) from by ring, ← sq, Complex.I_sq, neg_neg, mul_one]
    · simp only [hν, ite_false]; ring
  simp_rw [simplify, ← Finset.mul_sum]
  -- Now need: Σ_ν R(ν,μ) * R(ν,α) = δ_{μα}  (from RᵀR = I)
  have hRtR : ∑ ν : Fin (d + 1), (R ν μ : ℂ) * (R ν α : ℂ) =
      if μ = α then 1 else 0 := by
    have h := congr_fun (congr_fun hR_orth μ) α
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    have : ∑ ν, (R ν μ : ℂ) * (R ν α : ℂ) = (∑ ν, R ν μ * R ν α : ℝ) := by
      push_cast; rfl
    rw [this, h]; split_ifs <;> simp
  rw [hRtR]
  by_cases hμ : μ = (0 : Fin (d + 1)) <;> by_cases hα : α = (0 : Fin (d + 1))
  · -- μ = 0, α = 0
    subst hμ; subst hα; simp
  · -- μ = 0, α ≠ 0
    subst hμ; simp only [ite_true, hα, ite_false]
    have : ¬(0 : Fin (d + 1)) = α := fun h => hα h.symm
    simp only [this, ite_false]; ring
  · -- μ ≠ 0, α = 0
    subst hα; simp only [hμ, ite_false, ite_true]; ring
  · -- μ ≠ 0, α ≠ 0
    simp only [hμ, hα, ite_false]
    split_ifs <;> ring

/-- If a Wick-rotated configuration lies in PET, then applying the inverse
    Euclidean rotation's complex Lorentz embedding recovers the original
    (un-rotated) configuration in PET.

    More precisely: if (fun k => wickRotatePoint (R · x_k)) ∈ PET, then
    (fun k => wickRotatePoint (x_k)) ∈ PET, witnessed by applying
    ofEuclidean(Rᵀ) as the complex Lorentz transformation. -/
theorem PermutedExtendedTube_euclidean_preimage
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (x : Fin n → Fin (d + 1) → ℝ)
    (h : (fun k => wickRotatePoint (R.mulVec (x k))) ∈ PermutedExtendedTube d n) :
    (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n := by
  -- Unpack PET membership: there exist π, Λ, w with w ∈ PermutedForwardTube π
  simp only [PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq] at h ⊢
  obtain ⟨π, Λ, w, hw, hzw⟩ := h
  -- Use the same permutation and forward tube witness
  refine ⟨π, ?_⟩
  -- Build the new complex Lorentz transformation: ofEuclidean(Rᵀ) * Λ
  -- But we don't have a Group instance, so we compose manually
  -- First, build ofEuclidean(Rᵀ)
  let Λ_inv := ComplexLorentzGroup.ofEuclidean R.transpose
    (det_transpose_of_SO hR_det) (transpose_orth_of_SO hR_orth)
  -- We need to show wickRotatePoint(x_k) = Λ_new · w where Λ_new = Λ_inv composed with Λ
  -- Strategy: wickRotatePoint(x_k) = Λ_inv · wickRotatePoint(R · x_k) = Λ_inv · (Λ · w)
  -- By wickRotatePoint_ofEuclidean: wickRotatePoint(R · x_k) = ofEuclidean(R) · wickRotatePoint(x_k)
  -- So: wickRotatePoint(x_k) = ofEuclidean(Rᵀ) · ofEuclidean(R) · wickRotatePoint(x_k)
  --   = ofEuclidean(Rᵀ) · (Λ · w)
  -- But we want wickRotatePoint(x_k) = Λ_new · w, i.e., we need Λ_new such that
  -- Σ_ν Λ_new μ ν * w k ν = wickRotatePoint(x_k) μ
  -- From hzw: wickRotatePoint(R · x_k) = Λ · w, i.e.,
  --   Σ_ν Λ.val μ ν * w k ν = wickRotatePoint(R · x_k) μ
  --   = Σ_ν (ofEuclidean R).val μ ν * wickRotatePoint(x_k) ν
  -- So: wickRotatePoint(x_k) μ = Σ_ν (ofEuclidean Rᵀ · ofEuclidean R)_{μν} * wickRotatePoint(x_k) ν
  --   = Σ_α (ofEuclidean Rᵀ)_{μα} * Σ_ν (ofEuclidean R)_{αν} * wickRotatePoint(x_k) ν
  --   = Σ_α (ofEuclidean Rᵀ)_{μα} * wickRotatePoint(R · x_k) α
  --   = Σ_α (ofEuclidean Rᵀ)_{μα} * Σ_ν Λ_{αν} * w_k ν
  --   = Σ_ν (Σ_α (ofEuclidean Rᵀ)_{μα} * Λ_{αν}) * w_k ν
  -- Build Λ_new with val μ ν = Σ_α Λ_inv.val μ α * Λ.val α ν
  let Λ_new : ComplexLorentzGroup d := {
    val := Λ_inv.val * Λ.val
    metric_preserving := by
      intro μ ν
      have hΛ_inv := Λ_inv.metric_preserving
      have hΛ := Λ.metric_preserving
      simp only [Matrix.mul_apply]
      -- Prove: Σ_α η(α) * (Σ_j ..) * (Σ_j ..) = η(μ)*δ_{μν}
      -- = Σ_β Σ_γ (Σ_α η(α)*Λ_inv(α,β)*Λ_inv(α,γ)) * Λ(β,μ)*Λ(γ,ν)
      -- = Σ_β η(β)*Λ(β,μ)*Λ(β,ν) = η(μ)*δ_{μν}
      trans (∑ β : Fin (d + 1), ∑ γ : Fin (d + 1),
            (∑ α : Fin (d + 1), (LorentzLieGroup.minkowskiSignature d α : ℂ) *
              Λ_inv.val α β * Λ_inv.val α γ) * (Λ.val β μ * Λ.val γ ν))
      · -- Expand product of sums and swap sum order
        trans (∑ α, ∑ β, ∑ γ, (LorentzLieGroup.minkowskiSignature d α : ℂ) *
              Λ_inv.val α β * Λ_inv.val α γ * (Λ.val β μ * Λ.val γ ν))
        · -- Expand the product of sums
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [show (LorentzLieGroup.minkowskiSignature d α : ℂ) *
              (∑ j, Λ_inv.val α j * Λ.val j μ) *
              (∑ j, Λ_inv.val α j * Λ.val j ν) =
            (LorentzLieGroup.minkowskiSignature d α : ℂ) *
              ((∑ j, Λ_inv.val α j * Λ.val j μ) *
              (∑ j, Λ_inv.val α j * Λ.val j ν)) from mul_assoc _ _ _,
            Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun γ _ => ?_
          ring
        · -- Swap sums and factor out constant
          rw [Finset.sum_comm (f := fun α β => _)]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.sum_comm (f := fun α γ => _)]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [← Finset.sum_mul]
      · -- Use Λ_inv.metric_preserving and Λ.metric_preserving
        simp_rw [hΛ_inv]
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        convert hΛ μ ν using 1
        refine Finset.sum_congr rfl fun β _ => ?_; ring
    proper := by
      show (Λ_inv.val * Λ.val).det = 1
      rw [Matrix.det_mul, Λ_inv.proper, Λ.proper, mul_one]
  }
  refine ⟨Λ_new, w, hw, ?_⟩
  -- Show: wickRotatePoint(x_k) = Λ_new · w
  funext k μ
  show wickRotatePoint (x k) μ = ∑ ν, (Λ_inv.val * Λ.val) μ ν * w k ν
  simp only [Matrix.mul_apply]
  -- Goal: wick(x_k)(μ) = Σ_ν (Σ_j Λ_inv(μ,j)*Λ(j,ν)) * w(k,ν)
  -- From hzw: wickRotatePoint(R · x_k)(α) = Σ_ν Λ(α,ν) * w(k,ν)
  have hzw_k : ∀ α, wickRotatePoint (R.mulVec (x k)) α =
      ∑ ν, Λ.val α ν * w k ν :=
    fun α => congr_fun (congr_fun hzw k) α
  -- Step 1: wick(x_k)(μ) = Σ_α δ_{μα} * wick(x_k)(α)
  --       = Σ_α (Σ_j Λ_inv(μ,j)*ofEuc(R)(j,α)) * wick(x_k)(α)
  --       = Σ_j Λ_inv(μ,j) * Σ_α ofEuc(R)(j,α) * wick(x_k)(α)
  --       = Σ_j Λ_inv(μ,j) * wick(R·x_k)(j)    [by wickRotatePoint_ofEuclidean]
  --       = Σ_j Λ_inv(μ,j) * Σ_ν Λ(j,ν) * w(k,ν)   [by hzw_k]
  --       = Σ_ν (Σ_j Λ_inv(μ,j) * Λ(j,ν)) * w(k,ν)  [swap sums]
  -- Build the chain step by step
  -- First, wick(x_k)(μ) = Σ_j Λ_inv(μ,j) * wick(R·x_k)(j)
  have step1 : wickRotatePoint (x k) μ =
      ∑ j, Λ_inv.val μ j * wickRotatePoint (R.mulVec (x k)) j := by
    -- Use ofEuclidean_transpose_mul_self: Σ_ν Λ_inv(μ,ν)*ofEuc(R)(ν,α) = δ_{μα}
    symm
    calc ∑ j, Λ_inv.val μ j * wickRotatePoint (R.mulVec (x k)) j
        = ∑ j, Λ_inv.val μ j * ∑ α, (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val j α *
            wickRotatePoint (x k) α := by
          congr 1; funext j
          congr 1
          exact wickRotatePoint_ofEuclidean R hR_det hR_orth (x k) j
      _ = ∑ j, ∑ α, Λ_inv.val μ j *
            (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val j α *
            wickRotatePoint (x k) α := by
          congr 1; funext j; rw [Finset.mul_sum]
          congr 1; funext α; ring
      _ = ∑ α, (∑ j, Λ_inv.val μ j *
            (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val j α) *
            wickRotatePoint (x k) α := by
          rw [Finset.sum_comm]; congr 1; funext α; rw [Finset.sum_mul]
      _ = ∑ α, (if μ = α then (1 : ℂ) else 0) * wickRotatePoint (x k) α := by
          congr 1; funext α
          congr 1
          exact ofEuclidean_transpose_mul_self R hR_det hR_orth μ α
      _ = wickRotatePoint (x k) μ := by
          simp only [boole_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 2: substitute hzw_k and swap sums
  rw [step1]
  simp_rw [hzw_k, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A finite union of proper linear subspaces does not cover R^m when m ≥ 2.
    Equivalently: given finitely many nonzero vectors s₁,...,sₖ ∈ R^m, there exists
    w ∈ R^m not orthogonal to any of them.

    This follows from the fact that R is an infinite field and proper subspaces
    are nowhere dense (Baire category), or more directly from the algebraic result
    that a finite union of proper submodules over an infinite field ≠ the whole space. -/
private lemma exists_avoiding_finite_hyperplanes (m : ℕ) (_hm : 2 ≤ m)
    (S : Finset (Fin m → ℝ)) (hS : ∀ s ∈ S, s ≠ 0) :
    ∃ w : Fin m → ℝ, ∀ s ∈ S, ∑ μ, w μ * s μ ≠ 0 := by
  induction S using Finset.induction with
  | empty => exact ⟨0, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  | @insert a S' ha ih =>
    have hS_a : a ≠ 0 := hS a (Finset.mem_insert_self a S')
    have hS' : ∀ s ∈ S', s ≠ 0 := fun s hs => hS s (Finset.mem_insert_of_mem hs)
    obtain ⟨w, hw⟩ := ih hS'
    -- w avoids all hyperplanes in S'. Need to also avoid a's hyperplane.
    by_cases hwa : ∑ μ, w μ * a μ ≠ 0
    · -- w already avoids a, so it avoids all of insert a S'
      exact ⟨w, fun s hs => by
        rw [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · exact hwa
        · exact hw s hs⟩
    · -- w is orthogonal to a. Need to perturb.
      push_neg at hwa
      -- Since a ≠ 0, there exists μ with a μ ≠ 0
      have ⟨μ₀, hμ₀⟩ : ∃ μ₀, a μ₀ ≠ 0 := by
        by_contra h; push_neg at h; exact hS_a (funext h)
      -- Let e_μ₀ be the standard basis vector
      let e : Fin m → ℝ := fun ν => if ν = μ₀ then 1 else 0
      -- Bad t values: t = 0 (for a) and t = -⟨w,s⟩/(s μ₀) for s ∈ S' with s μ₀ ≠ 0
      let bad : Finset ℝ := {0} ∪ (S'.filter (fun s => s μ₀ ≠ 0)).image
        (fun s => -(∑ μ, w μ * s μ) / (s μ₀))
      obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
      have ht0 : t ≠ 0 := by
        intro h; exact ht (h ▸ Finset.mem_union_left _ (Finset.mem_singleton_self 0))
      -- Key identity: ∑ μ, (w μ + t * e μ) * s μ = ∑ μ, w μ * s μ + t * (s μ₀)
      have sum_eq : ∀ s : Fin m → ℝ,
          ∑ μ, (w μ + t * e μ) * s μ = ∑ μ, w μ * s μ + t * s μ₀ := by
        intro s
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1
        simp only [e, mul_assoc, ← Finset.mul_sum]
        congr 1
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      refine ⟨fun ν => w ν + t * e ν, fun s hs => ?_⟩
      rw [Finset.mem_insert] at hs
      rw [sum_eq]
      rcases hs with rfl | hs
      · -- s = a: ⟨w,a⟩ + t·(a μ₀) = 0 + t·(a μ₀) ≠ 0
        rw [hwa, zero_add]
        exact mul_ne_zero ht0 hμ₀
      · -- s ∈ S': ⟨w,s⟩ + t·(s μ₀) ≠ 0
        have hws := hw s hs
        by_cases hsμ : s μ₀ = 0
        · rw [hsμ, mul_zero, add_zero]; exact hws
        · -- t ≠ -⟨w,s⟩/(s μ₀), so ⟨w,s⟩ + t·(s μ₀) ≠ 0
          intro heq
          have ht_eq : t = -(∑ μ, w μ * s μ) / (s μ₀) := by
            have := hsμ
            field_simp at heq ⊢; linarith
          exact ht (Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨s, Finset.mem_filter.mpr ⟨hs, hsμ⟩, ht_eq.symm⟩))

/-- Any unit vector in R^m (m ≥ 1) can be extended to an orthogonal matrix with
    determinant 1 having that vector as its first row.

    Proof sketch: extend to an orthonormal basis via Gram-Schmidt, form the matrix,
    and if det = -1, negate the last basis vector. -/
private lemma exists_SO_matrix_with_first_row (m : ℕ) (hm : 2 ≤ m) [NeZero m]
    (u : Fin m → ℝ) (hu : ∑ μ, u μ ^ 2 = 1) :
    ∃ (R : Matrix (Fin m) (Fin m) ℝ), R.det = 1 ∧ R.transpose * R = 1 ∧
      ∀ μ, R 0 μ = u μ := by
  -- Convert u to EuclideanSpace
  set u' : EuclideanSpace ℝ (Fin m) := (EuclideanSpace.equiv (Fin m) ℝ).symm u with hu'_def
  have hu_norm : ‖u'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : ∀ i, ‖u'.ofLp i‖ ^ 2 = u i ^ 2 := by
      intro i; simp [u']
    simp_rw [this, hu, Real.sqrt_one]
  -- Orthonormal singleton
  have horth : Orthonormal ℝ (fun (_ : ({(0 : Fin m)} : Set (Fin m))) => u') := by
    constructor
    · intro ⟨i, hi⟩; exact hu_norm
    · intro ⟨i, hi⟩ ⟨j, hj⟩ h; exfalso; apply h
      simp [Set.mem_singleton_iff] at hi hj; exact Subtype.ext (hi.trans hj.symm)
  -- Extend to orthonormal basis with b 0 = u'
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = Fintype.card (Fin m) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
    (v := fun _ => u') (s := {0})
  have hb0 : b 0 = u' := hb 0 (Set.mem_singleton 0)
  -- Standard orthonormal basis
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  -- Change-of-basis matrix (columns = basis vectors b_i in standard coordinates)
  let M := e.toBasis.toMatrix (⇑b)
  -- M is orthogonal: M * M^T = 1 and M^T * M = 1
  have hM_mem := OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal e b
  have hMMt : M * M.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mp hM_mem
  have hMtM : M.transpose * M = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp hM_mem
  -- det M = ±1
  have hM_det := OrthonormalBasis.det_to_matrix_orthonormalBasis_real e b
  -- R = M^T has rows = b_i, so first row = b 0 = u'
  -- R^T * R = (M^T)^T * M^T = M * M^T = 1  ✓
  -- R 0 μ = M^T 0 μ = M μ 0 = e.repr(b 0) μ = (b 0)_μ = u'_μ = u μ
  -- Handle det: if det M = 1 then det M^T = 1; if det M = -1, negate last column of M
  rcases hM_det with hdet1 | hdetm1
  · -- det(e → b) = 1, so det M = 1 and det M^T = 1
    refine ⟨M.transpose, ?_, hMMt, ?_⟩
    · rw [Matrix.det_transpose]
      have : M.det = e.toBasis.det ⇑b := (e.toBasis.det_apply ⇑b).symm
      rw [this]; exact hdet1
    · intro μ
      simp only [Matrix.transpose_apply, M]
      show e.toBasis.repr (b 0) μ = u μ
      rw [hb0, OrthonormalBasis.coe_toBasis_repr_apply]
      simp [e, u']
  · -- det(e → b) = -1, negate last column of M to flip det
    -- Define M' = M with last column negated
    let last : Fin m := ⟨m - 1, by omega⟩
    have h0_ne_last : (0 : Fin m) ≠ last := by
      intro h; simp [last, Fin.ext_iff] at h; omega
    let M' : Matrix (Fin m) (Fin m) ℝ := fun i j =>
      if j = last then -M i j else M i j
    -- M' = M * D where D is diagonal with last entry -1
    let D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (fun j => if j = last then -1 else 1)
    have hM'_eq : M' = M * D := by
      ext i j; simp [M', D, Matrix.mul_apply, Matrix.diagonal]
    -- D is its own inverse: D * D = 1
    have hDD : D * D = 1 := by
      show Matrix.diagonal _ * Matrix.diagonal _ = 1
      rw [Matrix.diagonal_mul_diagonal]
      have : (fun j => (if j = last then -1 else 1 : ℝ) * if j = last then -1 else 1) = fun _ => 1 := by
        ext j; split_ifs <;> ring
      rw [this, Matrix.diagonal_one]
    -- M'.det = det M * det D = (-1) * (-1) = 1
    have hM'_det : M'.det = 1 := by
      have hM_det : M.det = -1 := by rw [← e.toBasis.det_apply]; exact hdetm1
      rw [hM'_eq, Matrix.det_mul, Matrix.det_diagonal, hM_det]
      simp [Finset.mem_univ]
    -- M' * M'^T = 1 (for R = M'^T, need R^T * R = M' * M'^T)
    have hM'Mt : M' * M'.transpose = 1 := by
      rw [hM'_eq, Matrix.transpose_mul]
      -- Goal: M * D * (D.transpose * M.transpose) = 1
      -- D is symmetric (diagonal), so D^T = D
      have hDt : D.transpose = D := by
        ext i j; simp only [D, Matrix.transpose_apply, Matrix.diagonal_apply]
        split_ifs <;> simp_all
      rw [hDt, Matrix.mul_assoc, ← Matrix.mul_assoc D D _, hDD, Matrix.one_mul]
      exact hMMt
    -- First row: M' 0 μ = M 0 μ (since the last column is the only one negated,
    -- and for row 0, M' 0 j = if j=last then -M 0 last else M 0 j)
    -- Wait, we need M'^T, not M'. R = M'^T.
    -- R 0 μ = M'^T 0 μ = M' μ 0 = (if 0 = last then -M μ 0 else M μ 0) = M μ 0
    -- since 0 ≠ last
    refine ⟨M'.transpose, ?_, hM'Mt, ?_⟩
    · rw [Matrix.det_transpose]; exact hM'_det
    · intro μ
      simp only [Matrix.transpose_apply, M']
      rw [if_neg h0_ne_last]
      -- Now need M μ 0 = u μ, same as the det=1 case
      show e.toBasis.toMatrix (⇑b) μ 0 = u μ
      rw [show (e.toBasis.toMatrix (⇑b) μ 0 : ℝ) = (e.toBasis.repr (b 0)) μ from rfl]
      rw [hb0, OrthonormalBasis.coe_toBasis_repr_apply]
      simp [e, u']

/-- For finitely many positive reals and a direction of perturbation not orthogonal
    to any difference vector, there exists a small perturbation preserving positivity
    and making all projections distinct.

    Key fact: each equation ⟨v + t·w, xᵢ - xⱼ⟩ = 0 has at most one solution in t
    (since ⟨w, xᵢ - xⱼ⟩ ≠ 0), so finitely many t-values are excluded. For small
    enough t > 0 not in this finite set, ⟨v + t·w, xᵢ⟩ > 0 and all are distinct. -/
private lemma exists_perturbation_distinct_positive {m n : ℕ}
    (x : Fin n → Fin m → ℝ)
    (v : Fin m → ℝ) (hv : ∀ i : Fin n, ∑ μ, v μ * x i μ > 0)
    (w : Fin m → ℝ) (hw : ∀ i j : Fin n, i ≠ j →
      ∑ μ, w μ * (x i μ - x j μ) ≠ 0) :
    ∃ u : Fin m → ℝ,
      (∀ i : Fin n, ∑ μ, u μ * x i μ > 0) ∧
      (∀ i j : Fin n, i ≠ j → ∑ μ, u μ * x i μ ≠ ∑ μ, u μ * x j μ) := by
  -- Strategy: take u = v + t * w for suitable t > 0
  -- Key identity: ∑ μ, (v μ + t * w μ) * x i μ = ∑ μ, v μ * x i μ + t * ∑ μ, w μ * x i μ
  -- For distinctness: ∑ μ, u μ * (x i μ - x j μ) = ∑ μ, v μ * (x i μ - x j μ) + t * ∑ μ, w μ * (x i μ - x j μ)
  -- This vanishes at exactly one t value per pair (since ⟨w, xᵢ - xⱼ⟩ ≠ 0)
  -- Bad t-values for distinctness
  let bad : Finset ℝ :=
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).image
      (fun p => -(∑ μ, v μ * (x p.1 μ - x p.2 μ)) / (∑ μ, w μ * (x p.1 μ - x p.2 μ)))
  -- Sum identity
  have sum_eq : ∀ (t : ℝ) (i : Fin n),
      ∑ μ, (v μ + t * w μ) * x i μ = (∑ μ, v μ * x i μ) + t * (∑ μ, w μ * x i μ) := by
    intro t i
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  -- Difference identity
  have diff_eq : ∀ (t : ℝ) (i j : Fin n),
      (∑ μ, (v μ + t * w μ) * x i μ) - (∑ μ, (v μ + t * w μ) * x j μ) =
      (∑ μ, v μ * (x i μ - x j μ)) + t * (∑ μ, w μ * (x i μ - x j μ)) := by
    intro t i j
    rw [sum_eq, sum_eq]
    have h1 : ∑ μ, v μ * (x i μ - x j μ) = (∑ μ, v μ * x i μ) - (∑ μ, v μ * x j μ) := by
      rw [← Finset.sum_sub_distrib]; congr 1; funext μ; ring
    have h2 : ∑ μ, w μ * (x i μ - x j μ) = (∑ μ, w μ * x i μ) - (∑ μ, w μ * x j μ) := by
      rw [← Finset.sum_sub_distrib]; congr 1; funext μ; ring
    rw [h1, h2]; ring
  by_cases hn : n = 0
  · subst hn; exact ⟨v, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · -- n > 0: need to find small t > 0 avoiding bad set
    have hvdot_pos : ∀ i : Fin n, (∑ μ, v μ * x i μ) > 0 := hv
    -- Bound for t to preserve positivity: |t| < min_i ⟨v,xᵢ⟩ / (1 + max_i |⟨w,xᵢ⟩|)
    have hfin_ne : (Finset.univ : Finset (Fin n)).Nonempty := by
      rw [Finset.univ_nonempty_iff]; exact Fin.pos_iff_nonempty.mp (by omega)
    let V := Finset.univ.inf' hfin_ne (fun i => ∑ μ, v μ * x i μ)
    have hV_pos : V > 0 := by
      simp only [V, Finset.lt_inf'_iff]
      exact fun i _ => hvdot_pos i
    let Wabs := Finset.univ.sup' hfin_ne (fun i => |∑ μ, w μ * x i μ|)
    have hWabs_nonneg : Wabs ≥ 0 := by
      obtain ⟨i, hi⟩ := hfin_ne
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun i => |∑ μ, w μ * x i μ|) hi)
    let bound := V / (1 + Wabs)
    have hbound_pos : bound > 0 := div_pos hV_pos (by linarith)
    -- (0, bound) is infinite
    have hint : Set.Infinite (Set.Ioo 0 bound) := Set.Ioo_infinite hbound_pos
    -- Pick t ∈ (0, bound) not in bad
    obtain ⟨t, ht_ioo, ht_bad⟩ := hint.exists_notMem_finset bad
    have ht_pos : t > 0 := ht_ioo.1
    have ht_lt : t < bound := ht_ioo.2
    -- Define u
    refine ⟨fun μ => v μ + t * w μ, ?_, ?_⟩
    · -- Positivity
      intro i
      rw [sum_eq]
      have hvi : (∑ μ, v μ * x i μ) ≥ V :=
        Finset.inf'_le _ (Finset.mem_univ i)
      have hwi : |∑ μ, w μ * x i μ| ≤ Wabs :=
        Finset.le_sup' (fun i => |∑ μ, w μ * x i μ|) (Finset.mem_univ i)
      have h1 : t * (∑ μ, w μ * x i μ) ≥ -(t * Wabs) := by
        have := neg_abs_le (∑ μ, w μ * x i μ)
        nlinarith [ht_pos]
      have h2 : t * Wabs < V := by
        have hW1 : 1 + Wabs > 0 := by linarith
        calc t * Wabs < bound * (1 + Wabs) := by nlinarith
          _ = V := by simp only [bound]; field_simp
      linarith
    · -- Distinctness
      intro i j hij heq
      have hdiff := diff_eq t i j
      have : (∑ μ, (v μ + t * w μ) * x i μ) - (∑ μ, (v μ + t * w μ) * x j μ) = 0 := by
        linarith
      rw [hdiff] at this
      have hwij := hw i j hij
      -- t = -(∑ μ, v μ * (x i μ - x j μ)) / (∑ μ, w μ * (x i μ - x j μ))
      have ht_eq : t = -(∑ μ, v μ * (x i μ - x j μ)) / (∑ μ, w μ * (x i μ - x j μ)) := by
        field_simp at this ⊢; linarith
      -- But t ∉ bad, contradiction
      apply ht_bad
      by_cases h : i < j
      · exact Finset.mem_image.mpr
          ⟨⟨i, j⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, ht_eq.symm⟩
      · -- j < i case
        have hji : j < i := by omega
        -- Swap: the bad value for (j, i) equals the bad value for (i, j)
        have ht_eq' : -(∑ μ, v μ * (x j μ - x i μ)) / (∑ μ, w μ * (x j μ - x i μ)) = t := by
          have h1 : ∑ μ, v μ * (x j μ - x i μ) = -(∑ μ, v μ * (x i μ - x j μ)) := by
            rw [← Finset.sum_neg_distrib]; congr 1; funext μ; ring
          have h2 : ∑ μ, w μ * (x j μ - x i μ) = -(∑ μ, w μ * (x i μ - x j μ)) := by
            rw [← Finset.sum_neg_distrib]; congr 1; funext μ; ring
          rw [h1, h2, neg_neg, div_neg]
          rw [ht_eq, neg_div]
        exact Finset.mem_image.mpr
          ⟨⟨j, i⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩, ht_eq'⟩

/-- For any real configuration whose points all lie in a common open half-space,
    there exists an SO(d+1) rotation making all first coordinates (times) distinct
    and positive.

    The hypothesis `hhs` says there exists a direction v such that ⟨v, xᵢ⟩ > 0 for
    all i. This is equivalent to all xᵢ lying in a common open half-space.

    Proof strategy:
    1. Get v from hhs with ⟨v, xᵢ⟩ > 0 for all i
    2. Find w avoiding all hyperplanes {⟨·, xᵢ - xⱼ⟩ = 0} (possible since d+1 ≥ 2)
    3. Perturb v along w to get u with ⟨u, xᵢ⟩ all positive and distinct
    4. Normalize u and extend to an SO(d+1) matrix R
    5. Then (R · xᵢ)₀ = ⟨first row of R, xᵢ⟩ = ⟨u/|u|, xᵢ⟩ which is positive and distinct

    The hypothesis is necessary: if xᵢ = 0, no rotation can make its projection positive;
    if xᵢ = -xⱼ, no rotation can make both projections positive. -/
lemma exists_rotation_distinct_positive_times {n : ℕ}
    (x : Fin n → Fin (d + 1) → ℝ)
    (hdistinct : ∀ i j : Fin n, i ≠ j → x i ≠ x j)
    (hhs : ∃ v : Fin (d + 1) → ℝ, ∀ i : Fin n, ∑ μ, v μ * x i μ > 0) :
    ∃ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.det = 1 ∧ R.transpose * R = 1 ∧
      (∀ i j : Fin n, i ≠ j → (R.mulVec (x i)) 0 ≠ (R.mulVec (x j)) 0) ∧
      (∀ i : Fin n, (R.mulVec (x i)) 0 > 0) := by
  -- Handle n = 0 vacuously
  by_cases hn0 : n = 0
  · subst hn0; exact ⟨1, Matrix.det_one, by simp, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  obtain ⟨v, hv_pos⟩ := hhs
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hd : 2 ≤ d + 1 := by have := NeZero.pos d; omega
  -- Collect difference vectors for distinct pairs (i < j)
  let diffs : Finset (Fin (d + 1) → ℝ) :=
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).image
      (fun p => fun μ => x p.1 μ - x p.2 μ)
  -- All differences are nonzero since x is injective
  have hdiffs_ne : ∀ s ∈ diffs, s ≠ 0 := by
    intro s hs
    simp only [diffs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := hs
    intro heq
    have hxeq : x i = x j := by
      ext μ; have := congr_fun heq μ; simp at this; linarith
    exact absurd hxeq (hdistinct i j (by intro h; subst h; exact absurd hij (lt_irrefl _)))
  obtain ⟨w, hw⟩ := exists_avoiding_finite_hyperplanes (d + 1) hd diffs hdiffs_ne
  -- w is not orthogonal to any difference vector xᵢ - xⱼ
  have hw' : ∀ i j : Fin n, i ≠ j → ∑ μ, w μ * (x i μ - x j μ) ≠ 0 := by
    intro i j hij
    by_cases h : i < j
    · exact hw _ (Finset.mem_image.mpr ⟨⟨i, j⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩)
    · push_neg at h
      have h' : j < i := lt_of_le_of_ne h (Ne.symm hij)
      have hmem : (fun μ => x j μ - x i μ) ∈ diffs :=
        Finset.mem_image.mpr ⟨⟨j, i⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩, rfl⟩
      intro heq
      apply hw _ hmem
      have hfact : ∀ μ, w μ * (x j μ - x i μ) = -(w μ * (x i μ - x j μ)) := by
        intro μ; ring
      simp_rw [hfact, Finset.sum_neg_distrib]
      linarith [heq]
  obtain ⟨u, hu_pos, hu_dist⟩ := exists_perturbation_distinct_positive x v hv_pos w hw'
  -- u is nonzero (since ⟨u, x₀⟩ > 0 requires u ≠ 0 when n ≥ 1)
  have hu_ne : u ≠ 0 := by
    intro heq
    have := hu_pos ⟨0, hn_pos⟩
    subst heq
    simp at this
  -- ∑ u μ ^ 2 > 0 from u ≠ 0
  have hnorm_sq_pos : 0 < ∑ μ : Fin (d + 1), u μ ^ 2 := by
    by_contra h
    push_neg at h
    have h0 : ∀ μ, u μ = 0 := by
      intro μ
      have hμ : u μ ^ 2 ≤ ∑ ν : Fin (d + 1), u ν ^ 2 :=
        Finset.single_le_sum (fun ν _ => sq_nonneg (u ν)) (Finset.mem_univ μ)
      have hle : u μ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hle
    exact hu_ne (funext h0)
  let norm_u := Real.sqrt (∑ μ : Fin (d + 1), u μ ^ 2)
  have hnorm_pos : 0 < norm_u := Real.sqrt_pos_of_pos hnorm_sq_pos
  -- Normalized unit vector
  let û : Fin (d + 1) → ℝ := fun μ => u μ / norm_u
  have hû_unit : ∑ μ, û μ ^ 2 = 1 := by
    simp only [û, div_pow]
    rw [← Finset.sum_div]
    rw [show norm_u ^ 2 = ∑ μ, u μ ^ 2 from Real.sq_sqrt (le_of_lt hnorm_sq_pos)]
    exact div_self (ne_of_gt hnorm_sq_pos)
  -- Extend û to an SO(d+1) rotation matrix
  obtain ⟨R, hR_det, hR_orth, hR_row⟩ := exists_SO_matrix_with_first_row (d + 1) hd û hû_unit
  refine ⟨R, hR_det, hR_orth, ?_, ?_⟩
  · -- Distinct projections: (R · xᵢ)₀ = ∑_μ R₀μ * xᵢ(μ) = ⟨û, xᵢ⟩ = ⟨u, xᵢ⟩ / |u|
    intro i j hij hmulvec_eq
    apply hu_dist i j hij
    -- R.mulVec (x i) 0 = ∑ μ, R 0 μ * x i μ = ∑ μ, û μ * x i μ
    have hRi : (R.mulVec (x i)) 0 = ∑ μ, û μ * x i μ := by
      simp [Matrix.mulVec, dotProduct]; congr 1; ext μ; rw [hR_row]
    have hRj : (R.mulVec (x j)) 0 = ∑ μ, û μ * x j μ := by
      simp [Matrix.mulVec, dotProduct]; congr 1; ext μ; rw [hR_row]
    rw [hRi, hRj] at hmulvec_eq
    -- ∑ û μ * x i μ = ∑ (u μ / |u|) * x i μ = (∑ u μ * x i μ) / |u|
    simp only [û, div_mul_eq_mul_div] at hmulvec_eq
    rw [← Finset.sum_div, ← Finset.sum_div] at hmulvec_eq
    exact (div_left_inj' (ne_of_gt hnorm_pos)).mp hmulvec_eq
  · -- Positive projections: (R · xᵢ)₀ = ⟨u, xᵢ⟩ / |u| > 0
    intro i
    have hRi : (R.mulVec (x i)) 0 = ∑ μ, û μ * x i μ := by
      simp [Matrix.mulVec, dotProduct]; congr 1; ext μ; rw [hR_row]
    rw [hRi]
    simp only [û, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    exact div_pos (hu_pos i) hnorm_pos

/-- Euclidean invariance of Schwinger functions follows from complex Lorentz
    invariance of the analytically continued Wightman functions.

    The key: SO(d+1) embeds into L₊(ℂ) as the subgroup of complex Lorentz
    transformations that preserve Euclidean points. -/
theorem schwinger_euclidean_invariant
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_inv : ∀ n (Λ : ComplexLorentzGroup d) z,
      z ∈ PermutedExtendedTube d n →
      W_analytic n (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = W_analytic n z)
    (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (xs : Fin n → Fin (d + 1) → ℝ)
    (htube : (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n) :
    SchwingerFromWightman d W_analytic n (fun k => R.mulVec (xs k)) =
    SchwingerFromWightman d W_analytic n xs := by
  simp only [SchwingerFromWightman]
  -- wickRotatePoint (R.mulVec x) = Λ_R · wickRotatePoint x by wickRotatePoint_ofEuclidean
  have h : (fun k => wickRotatePoint (R.mulVec (xs k))) =
      (fun k μ => ∑ ν, (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth).val μ ν *
        wickRotatePoint (xs k) ν) := by
    ext k μ
    exact wickRotatePoint_ofEuclidean R hR_det hR_orth (xs k) μ
  rw [h]
  exact hW_inv n (ComplexLorentzGroup.ofEuclidean R hR_det hR_orth)
    (fun k => wickRotatePoint (xs k)) htube

/-- Permutation symmetry of Schwinger functions follows from permutation symmetry
    of the BHW extension.

    BHW gives: W_analytic(z_{π(1)}, ..., z_{π(n)}) = W_analytic(z₁, ..., zₙ)
    for all z in the permuted extended tube.
    Restricting to Euclidean points gives S_n(x_{π(1)}, ..., x_{π(n)}) = S_n(x₁, ..., xₙ). -/
theorem schwinger_permutation_symmetric
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_perm : ∀ n (π : Equiv.Perm (Fin n)) z,
      z ∈ PermutedExtendedTube d n →
      W_analytic n (fun k => z (π k)) = W_analytic n z)
    (n : ℕ) (π : Equiv.Perm (Fin n)) (xs : Fin n → Fin (d + 1) → ℝ)
    (htube : (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n) :
    SchwingerFromWightman d W_analytic n (fun k => xs (π k)) =
    SchwingerFromWightman d W_analytic n xs := by
  simp only [SchwingerFromWightman]
  -- (fun k => wickRotatePoint (xs (π k))) = (fun k => z (π k)) where z = fun k => wickRotatePoint (xs k)
  exact hW_perm n π (fun k => wickRotatePoint (xs k)) htube

end
