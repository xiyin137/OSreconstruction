/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.VladimirovTillmann
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dual Cone Bridge Lemmas

Bridge lemmas connecting the project's unbundled cone predicates (`IsCone`, `IsSalientCone`)
to Mathlib's bundled `ConvexCone`, `PointedCone`, and `ProperCone` infrastructure,
specialized to `EuclideanSpace ℝ (Fin m)`.

This enables using Mathlib's dual cone API (`ProperCone.innerDual`, bipolar theorem,
Hahn-Banach separation) with the cones arising in the Vladimirov-Tillmann theorem.

## Main results

- `IsCone.toConvexCone`: lift an `IsCone` set to a bundled `ConvexCone`
- `convexCone_isCone`: extract `IsCone` from a `ConvexCone`
- `dualCone_separation`: Hahn-Banach separation for points outside the cone

## References

- Mathlib: `Mathlib.Analysis.Convex.Cone.InnerDual`
- Vladimirov, "Methods of the Theory of Generalized Functions", §25
-/

open scoped Classical
noncomputable section

variable {m : ℕ}

/-- The Euclidean space `ℝ^m` used for dual cone operations.
    We work in `EuclideanSpace ℝ (Fin m)` to have an `InnerProductSpace` instance,
    which is required by Mathlib's `ProperCone.innerDual`. -/
abbrev RealEuclidean (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-! ### IsCone → ConvexCone bridge -/

/-- A set satisfying `IsCone` with convexity gives a bundled `ConvexCone`. -/
def IsCone.toConvexCone {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {C : Set E} (hcone : IsCone C) (hconv : Convex ℝ C) : ConvexCone ℝ E where
  carrier := C
  smul_mem' := fun c hc x hx => hcone x hx c hc
  add_mem' := by
    intro x hx y hy
    -- x + y = 2 • (midpoint x y), and the midpoint is in C by convexity
    have hmid : (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y ∈ C :=
      hconv hx hy (by norm_num) (by norm_num) (by norm_num)
    -- Now scale by 2
    convert hcone _ hmid 2 two_pos using 1
    simp [smul_add, ← mul_smul]

/-- Every `ConvexCone` satisfies `IsCone`. -/
theorem convexCone_isCone {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (C : ConvexCone ℝ E) : IsCone (C : Set E) :=
  fun _ hy t ht => C.smul_mem ht hy

/-! ### Dual cone definition for flat sets -/

/-- The dual cone of a set S ⊆ ℝ^m, defined via the Euclidean inner product:
    `DualConeEucl S = {ξ : ℝ^m | ∀ y ∈ S, ⟪y, ξ⟫ ≥ 0}`.

    This is a thin wrapper around Mathlib's `PointedCone.dual` specialized to
    `EuclideanSpace ℝ (Fin m)` with the standard inner product pairing. -/
def DualConeEucl (S : Set (RealEuclidean m)) : Set (RealEuclidean m) :=
  {ξ | ∀ y ∈ S, (0 : ℝ) ≤ @inner ℝ (RealEuclidean m) _ y ξ}

theorem mem_dualConeEucl {S : Set (RealEuclidean m)} {ξ : RealEuclidean m} :
    ξ ∈ DualConeEucl S ↔ ∀ y ∈ S, (0 : ℝ) ≤ @inner ℝ (RealEuclidean m) _ y ξ :=
  Iff.rfl

theorem dualConeEucl_convex (S : Set (RealEuclidean m)) :
    Convex ℝ (DualConeEucl S) := by
  intro ξ₁ hξ₁ ξ₂ hξ₂ a b ha hb _
  intro y hy
  simp only [DualConeEucl, Set.mem_setOf_eq] at hξ₁ hξ₂ ⊢
  calc @inner ℝ (RealEuclidean m) _ y (a • ξ₁ + b • ξ₂)
      = a * @inner ℝ (RealEuclidean m) _ y ξ₁ + b * @inner ℝ (RealEuclidean m) _ y ξ₂ := by
        rw [inner_add_right, inner_smul_right, inner_smul_right]
    _ ≥ 0 := add_nonneg (mul_nonneg ha (hξ₁ y hy)) (mul_nonneg hb (hξ₂ y hy))

theorem dualConeEucl_isCone (S : Set (RealEuclidean m)) :
    IsCone (DualConeEucl S) := by
  intro ξ hξ t ht
  simp only [DualConeEucl, Set.mem_setOf_eq] at hξ ⊢
  intro z hz
  rw [inner_smul_right]
  exact mul_nonneg (le_of_lt ht) (hξ z hz)

theorem zero_mem_dualConeEucl (S : Set (RealEuclidean m)) :
    (0 : RealEuclidean m) ∈ DualConeEucl S := by
  intro y _
  simp [inner_zero_right]

theorem dualConeEucl_closed (S : Set (RealEuclidean m)) :
    IsClosed (DualConeEucl S) := by
  have : DualConeEucl S = ⋂ y ∈ S, {ξ | (0 : ℝ) ≤ @inner ℝ (RealEuclidean m) _ y ξ} := by
    ext ξ
    simp [DualConeEucl]
  rw [this]
  apply isClosed_biInter
  intro y _
  exact isClosed_le continuous_const (continuous_const.inner continuous_id')

/-! ### Separation theorem -/

/-- For an open convex cone `S` and a point `y` not in its closure, there exists a dual
    vector `ξ ∈ DualConeEucl S` with `⟪y, ξ⟫ < 0`.

    Proof: Apply Hahn-Banach (`geometric_hahn_banach_point_closed`) to separate `y`
    from `closure S`. This gives a continuous linear functional `f` with `f(y) < u < f(a)`
    for all `a ∈ closure S`. Since `S` is a cone, `0 ∈ closure S`, so `u < f(0) = 0`,
    hence `f(y) < 0`. The cone scaling argument shows `f(a) ≥ 0` for all `a ∈ S`:
    if `f(a) < 0`, then `f(t·a) = t·f(a) → -∞`, contradicting `f(t·a) > u`.
    By Riesz representation, `f = ⟪·, ξ⟫`, giving `ξ ∈ DualConeEucl S` with `⟪y, ξ⟫ < 0`. -/
theorem dualConeEucl_separates_of_not_mem_closure
    {S : Set (RealEuclidean m)}
    (hcone : IsCone S) (hconv : Convex ℝ S) (hne : S.Nonempty)
    {y : RealEuclidean m}
    (hy : y ∉ closure S) :
    ∃ ξ ∈ DualConeEucl S, @inner ℝ (RealEuclidean m) _ y ξ < 0 := by
  -- Step 1: Hahn-Banach separation
  obtain ⟨f, u, hfy, hfa⟩ :=
    geometric_hahn_banach_point_closed hconv.closure isClosed_closure hy
  -- f(y) < u and ∀ a ∈ closure S, u < f(a)
  -- Step 2: 0 ∈ closure S → u < 0 → f(y) < 0
  have h0_mem : (0 : RealEuclidean m) ∈ closure S := by
    obtain ⟨a, ha⟩ := hne
    rw [mem_closure_iff_seq_limit]
    refine ⟨fun n => ((n : ℝ) + 1)⁻¹ • a,
      fun n => hcone a ha _ (inv_pos.mpr (by positivity : (0 : ℝ) < (n : ℝ) + 1)), ?_⟩
    sorry -- ((n+1)⁻¹) • a → 0 as n → ∞
  have hu_neg : u < 0 := by linarith [hfa 0 h0_mem, (f.map_zero)]
  have hfy_neg : f y < 0 := lt_trans hfy hu_neg
  -- Step 3: f(a) ≥ 0 for all a ∈ S
  have hf_nonneg : ∀ a ∈ S, 0 ≤ f a := by
    intro a ha
    by_contra h_neg
    push_neg at h_neg
    sorry -- Archimedean: n*f(a) → -∞ contradicts f(n•a) > u for n•a ∈ closure S
  -- Step 4: Riesz representation
  let ξ := (InnerProductSpace.toDual ℝ (RealEuclidean m)).symm f
  refine ⟨ξ, ?_, ?_⟩
  · -- ξ ∈ DualConeEucl S: ⟪a, ξ⟫ ≥ 0 for a ∈ S
    intro a ha
    have : f a = @inner ℝ (RealEuclidean m) _ ξ a := by
      simp [ξ, InnerProductSpace.toDual_symm_apply]
    rw [real_inner_comm]
    linarith [hf_nonneg a ha]
  · -- ⟪y, ξ⟫ < 0
    have : f y = @inner ℝ (RealEuclidean m) _ ξ y := by
      simp [ξ, InnerProductSpace.toDual_symm_apply]
    rw [real_inner_comm]
    linarith

end
