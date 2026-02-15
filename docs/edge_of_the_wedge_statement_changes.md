# Edge-of-the-Wedge Theorem: Statement Changes

## Overview

The multi-dimensional `edge_of_the_wedge` theorem statement in
`AnalyticContinuation.lean` has been revised to be mathematically correct
and amenable to formal proof. The original statement had two issues that
would have made the theorem either false or unprovable.

## Changes

### 1. Added cone condition (`hcone`)

**Old:** Only `IsOpen C`, `Convex ℝ C`, `0 ∉ C`.

**New:** Added `hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C`.

**Why:** The theorem is about *tube domains* over a *cone* C. The cone property
(closure under positive scaling) is essential for the proof: the slice map
`w ↦ x_ℂ + w · η_ℂ` sends the upper half-plane (Im w > 0) into
`TubeDomain(C)` precisely because `Im(w) · η ∈ C` when `Im(w) > 0` and
`η ∈ C` — which requires the cone condition. Without it, the imaginary
part `Im(w) · η` is only a positive multiple of `η`, and there is no
guarantee it lies in C.

The cone condition also ensures that the boundary value hypothesis makes
sense: approaching the real boundary from within the tube along any ray
`t · η` with `η ∈ C` and `t → 0⁺` stays inside the tube for all `t > 0`.

Also added `hCne : C.Nonempty` to ensure the cone has at least one direction,
which is needed to construct the 1D slices.

### 2. Strengthened boundary value hypotheses

**Old:**
```lean
hmatch : ∀ x ∈ E, ∀ η ∈ C,
  ∃ (bv : ℂ),
    Filter.Tendsto
      (fun t : ℝ => f_plus (fun i => ↑(x i) + t * ↑(η i) * I))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds bv) ∧
    Filter.Tendsto
      (fun t : ℝ => f_minus (fun i => ↑(x i) - t * ↑(η i) * I))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds bv)
```

**New:**
```lean
bv : (Fin m → ℝ) → ℂ
hbv_cont : ContinuousOn bv E
hf_plus_bv : ∀ x ∈ E,
  Filter.Tendsto f_plus
    (nhdsWithin (fun i => (x i : ℂ)) (TubeDomain C)) (nhds (bv x))
hf_minus_bv : ∀ x ∈ E,
  Filter.Tendsto f_minus
    (nhdsWithin (fun i => (x i : ℂ)) (TubeDomain (Neg.neg '' C))) (nhds (bv x))
```

**Why (three issues with the old formulation):**

1. **Directional vs. full boundary values.** The old `hmatch` only required
   limits along specific rays `t · η` for each `η ∈ C`. The 1D
   edge-of-the-wedge theorem (`edge_of_the_wedge_1d`) requires
   `nhdsWithin` limits — approach from the *full* upper half-plane, not
   just along a single ray. With only ray limits, the 1D result cannot
   be applied.

2. **Existential vs. functional boundary value.** The old `hmatch` used
   `∃ bv` — the boundary value could depend on both `x` and `η`, and
   different directions could give different limits. The new formulation
   gives a single function `bv : (Fin m → ℝ) → ℂ` that is the common
   boundary value from all directions. This is the mathematically correct
   formulation (for a holomorphic function, the boundary value is
   direction-independent if it exists).

3. **Continuity of boundary values.** The old formulation did not require
   `bv` to be continuous. The 1D edge-of-the-wedge theorem needs
   continuous boundary values along the real line (the `hbv_cont` and
   `hmatch` hypotheses of `edge_of_the_wedge_1d`). The explicit
   `hbv_cont : ContinuousOn bv E` provides this.

## New infrastructure: Slice maps

The `sliceMap` definition and supporting lemmas provide the key reduction
from multi-D to 1D:

- `sliceMap x η : ℂ → (Fin m → ℂ)` — the affine embedding `w ↦ x_ℂ + w · η_ℂ`
- `sliceMap_im_eq_smul` — Im(sliceMap x η w) = Im(w) · η
- `sliceMap_upper_mem_tubeDomain` — upper half-plane maps into TubeDomain(C)
- `sliceMap_lower_mem_neg_tubeDomain` — lower half-plane maps into TubeDomain(-C)
- `differentiable_sliceMap` — the slice map is holomorphic (affine)
- `continuous_sliceMap` — the slice map is continuous

These lemmas formalize the dimensional reduction: composing `f_plus` with
`sliceMap x η` gives a function holomorphic on the upper half-plane,
to which the 1D edge-of-the-wedge theorem can be applied.

## Proof strategy (for future implementation)

The proof proceeds by:

1. **1D slicing:** For each η ∈ C and x ∈ E, compose f_± with
   `sliceMap x η` and apply `edge_of_the_wedge_1d` to get holomorphic
   extension in the η-direction.

2. **Separate holomorphicity:** Choose m linearly independent directions
   η₁,...,ηₘ ∈ C (possible since C is open and nonempty). The 1D
   extensions give holomorphicity in each ηⱼ-direction separately.

3. **Joint holomorphicity:** Apply `holomorphic_extension_across_real`
   (which internally uses `osgood_lemma`) to upgrade separate
   holomorphicity to joint holomorphicity on a complex neighborhood of E.

## Downstream impact

The `bargmann_hall_wightman` theorem (also sorry'd) will need its
application of `edge_of_the_wedge` updated to provide the new hypotheses.
Since both theorems are currently sorry'd, this is not a breaking change.
