# BHW Permutation Invariance - Status

Last updated: 2026-03-02

## Current Status

`BHW.bargmann_hall_wightman_theorem` compiles with:
- zero `sorry`s
- two project axioms

Lean check:

```lean
#print axioms BHW.bargmann_hall_wightman_theorem
```

Current non-core dependencies:
- `BHW.kakSet_dense`
- `BHW.hExtPerm_of_d1`

Core Lean axioms also appear (`propext`, `Classical.choice`, `Quot.sound`).

## Why `raw_KAK_decomposition` Was Removed

Previous axiom (now removed) claimed global surjectivity:

`forall Λ : ComplexLorentzGroup d, exists k1 k2 t, Λ = ofReal k1 * expBoost t * ofReal k2`.

This is too strong in general: non-semisimple/parabolic elements (complex null-rotation type behavior) need not lie in the single-parameter Cartan image `K exp(tK) K`.

So the global statement is mathematically risky as an axiom. It can encode a false theorem if interpreted literally over all of `SO_+(1,d;C)`.

## Replacement: Dense KAK Image

The development now uses:

- `kakSet`:
  `range (fun (k1, t, k2) => ofReal k1 * expBoost t * ofReal k2)`
- axiom `kakSet_dense (hd2 : 2 <= d) : Dense (kakSet d)`

Then `isConnected_sliceIndexSet` is proved by:
- constructing connected `J = kakSet d ∩ I` as a continuous image of `K x P x K`,
- using openness of `I` and density of `kakSet d` to show `I ⊆ closure J`,
- applying connectedness under closure sandwich.

This removes dependence on global KAK surjectivity while keeping the needed topological consequence.

## Remaining Project Axioms

1. `kakSet_dense` in [OverlapConnected.lean](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/OverlapConnected.lean:2186)
2. `hExtPerm_of_d1` in [OverlapConnected.lean](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/OverlapConnected.lean:2761)

## Key Proven Pieces (No Axiom)

- parameter normalization for nonempty slices:
  [expBoost_nonempty_parameter_normalization](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/OverlapConnected.lean:2375)
- connectedness of the slice index set via dense-KAK:
  [isConnected_sliceIndexSet](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/OverlapConnected.lean:2517)
- d >= 2 extension/permutation invariance:
  [hExtPerm_of_d2](/Users/mdouglas/Documents/GitHub/OSreconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/OverlapConnected.lean:2658)

## Build Check

Verified after the refactor:
- `lake build OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.OverlapConnected`
- `lake build OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlow`

