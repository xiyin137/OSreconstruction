# `bvt_W_positive` Proof Plan

## Original Prompt

> Following the proof in OS 1973 Section 4.3, plan a proof of `bvt_W_positive`. Be sure to make use of infrastructure available in the code base before introducing new theorem or axioms.

## Goal

Fill the private theorem `bvt_W_positive` in
[`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean)
by following the OS 1973 Section 4.3 positivity strategy:

1. build a dense image of Minkowski test data inside the honest OS Hilbert space,
2. identify the reconstructed Wightman quadratic form with the OS Hilbert norm on that dense image,
3. pass positivity to arbitrary `BorchersSequence d` by density and continuity.

This should reuse the existing Wick-rotation, OS-Hilbert, and boundary-value comparison infrastructure already in the repo. No new axioms should be introduced.

## Existing Infrastructure To Reuse

### Boundary-value package

- `bvt_W`, `bvt_F`, `bvt_W_continuous`, `bvt_W_linear` in
  [`OSToWightmanBoundaryValuesBase.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean)
- `bvt_F_perm`, `bvt_F_translationInvariant`, `bvt_F_negCanonical` and the comparison lemmas in
  [`OSToWightmanBoundaryValuesComparison.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean)

### OS positivity / quotient / Hilbert space

- `PositiveTimeBorchersSequence.osInner_nonneg_self` in
  [`SchwingerOS.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean)
- `OSHilbertSpace`, `osTimeShiftHilbert`, `fieldActionTimeShiftPositiveTimeBorchers`,
  `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single`, and related semigroup-side matrix-element lemmas in
  [`OSToWightmanSemigroup.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean)
- spatial-translation / compact positive-time approximation machinery in
  [`OSToWightmanSpatialMomentum.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSpatialMomentum.lean)

### Boundary-value positivity comparison already present

- `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero`
- `bvt_wightmanInner_single_single_eq_osInner_of_tendsto_singleSplit_xiShift_nhdsWithin_zero`
- `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
- `bvt_wightmanInner_self_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian`

These live across
[`OSToWightmanBoundaryValuesBase.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean)
and
[`OSToWightmanBoundaryValuesComparison.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean).

### General density / continuity tools

- `productTensor_span_dense` in
  [`DenseCLM.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/DenseCLM.lean)
- finite-sum algebra for `WightmanInnerProduct` in
  [`Core.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/Core.lean)

## Core Proof Strategy

### 1. First package the Hermitian input for `bvt_W`

The most useful comparison theorem for self-pairs with a possible degree-zero component is

- `bvt_wightmanInner_self_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian`

It requires a Hermitian symmetry hypothesis on `bvt_W`. That hypothesis can already be proved from existing boundary-ray infrastructure:

- use `boundary_ray_hermitian_pairing_of_F_negCanonical`,
- instantiate it with `bvt_F OS lgc n`,
- feed in `bvt_F_perm OS lgc n`,
- `bvt_F_translationInvariant OS lgc n`,
- `bvt_F_negCanonical OS lgc n`.

This is exactly the same local argument later used in the public theorem `bvt_hermitian`. For the positivity proof, define the resulting Hermitian transfer statement as a private local helper and reuse it immediately.

### 2. Do not stop at the compact positive-time comparison layer

The comparison lemmas already prove positivity for compact ordered positive-time Euclidean Borchers vectors, and even repair the degree-zero term once Hermiticity is available. But `bvt_W_positive` is quantified over arbitrary `BorchersSequence d`, so the proof has to include the Section 4.3 dense-image step rather than stopping at the ordered positive-time shell.

In OS 1973 Section 4.3, positivity is proved by showing that the Wightman quadratic form is the Hilbert norm of vectors in a dense image of Euclidean test data. The Lean proof should follow the same architecture.

### 3. Build the degree-1 dense image map

Add a private construction in
[`OSToWightmanBoundaryValues.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean)
that plays the role of the OS map from positive-time Euclidean one-point tests to Minkowski one-point tests.

The target shape is:

- a linear map from the positive-time one-point Euclidean test space into `SchwartzSpacetime d`,
- injective,
- with dense range in `SchwartzSpacetime d`.

This is the one genuinely new proof ingredient missing from the current boundary-value layer. It should be implemented with existing Schwartz / translation / cutoff tools, not with axioms.

### 4. Lift the degree-1 map to product tensors

Once the one-point dense image exists, define its `n`-fold tensor lift on product tensors using `SchwartzMap.productTensor`.

Then use:

- multilinearity of `SchwartzMap.productTensor`,
- `productTensor_span_dense`,
- continuity of `bvt_W OS lgc n`,

to extend the dense-image statement from product tensors to all `SchwartzNPoint d n`.

This gives the Lean analogue of the OS statement that the image of Euclidean positive-time test data is dense in the Minkowski test-function space.

### 5. Lift again to finitely supported Borchers sequences

Package the componentwise dense image into an approximation theorem for `BorchersSequence d`:

- for every `F : BorchersSequence d`,
- there exists a net or sequence `F_N` built from the dense Euclidean image,
- with common eventual bound,
- such that each component `F_N.funcs n -> F.funcs n` in Schwartz topology.

Because Borchers sequences are finitely supported, this should be packaged componentwise over the finite range `Finset.range (F.bound + 1)` and then assembled by `BorchersSequence.linearCombo` or a direct componentwise definition.

### 6. Prove the norm identity on the dense image

For Borchers vectors coming from the Euclidean positive-time dense image, prove

```lean
WightmanInnerProduct d (bvt_W OS lgc) F F =
PositiveTimeBorchersSequence.osInner OS FE FE
```

for the corresponding Euclidean positive-time vector `FE`.

This is where the existing comparison infrastructure should do almost all of the work:

- reduce to componentwise single-split `xiShift` comparisons,
- use `bvt_wightmanInner_self_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian`,
- discharge the componentwise limit hypotheses using the already proved
  `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero` chain and its zero-translation specialization,
- use the local Hermitian helper from Step 1.

For compact ordered positive-time approximants, compactness is already handled by:

- `compactApproxPositiveTimeBorchers`,
- `compactApproxPositiveTimeBorchers_component_compact`,
- `tendsto_compactApproxPositiveTimeBorchers_diff_osInner`.

Those lemmas should be reused rather than rebuilding a fresh cutoff argument.

### 7. Add the matching continuity lemma on the Wightman side

To pass from dense-image approximants to arbitrary `F`, add a private continuity theorem for the reconstructed quadratic form:

- if `F_N` converges componentwise to `F`,
- and the bounds are uniformly dominated so the `WightmanInnerProduct` sum is eventually taken over one fixed finite box,
- then
  `WightmanInnerProduct d (bvt_W OS lgc) F_N F_N -> WightmanInnerProduct d (bvt_W OS lgc) F F`.

This should be formal from:

- `bvt_W_continuous`,
- `bvt_W_linear`,
- `WightmanInnerProduct_eq_extended`,
- finite sums commuting with limits in `Core`.

No new functional-analysis machinery should be needed here.

### 8. Finish the positivity proof by density

With Steps 5 to 7 in place:

1. approximate arbitrary `F : BorchersSequence d` by dense-image `F_N`,
2. identify each self-pair as an OS norm:
   `0 ≤ (WightmanInnerProduct ... F_N F_N).re`,
3. pass to the limit using the continuity lemma,
4. conclude
   `0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re`.

This closes `bvt_W_positive` exactly in the OS 1973 Section 4.3 style.

## Expected Local Helper Theorems

These should be private unless they become clearly reusable elsewhere.

1. A private Hermitian transfer helper for `bvt_W`, extracted from the boundary-ray reflection identity.
2. A private dense degree-1 Euclidean-to-Minkowski map.
3. A private theorem lifting density from one-point tests to product tensors.
4. A private theorem lifting tensor density to finitely supported Borchers sequences.
5. A private continuity lemma for `WightmanInnerProduct d (bvt_W OS lgc)` under componentwise convergence.

## Things To Avoid

- Do not introduce new axioms.
- Do not duplicate the later public theorem `bvt_hermitian`; factor the needed local input privately and let the public theorem reuse the same pattern.
- Do not try to prove `bvt_W_positive` only from the compact ordered positive-time comparison theorem. That proves the wrong statement; the dense-image passage is the whole point of OS §4.3.
- Do not rebuild product-tensor density by hand when `productTensor_span_dense` already exists.

## Acceptance Check

The plan is complete if the final proof of

```lean
private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0
```

uses:

- existing OS positivity on `PositiveTimeBorchersSequence`,
- existing boundary-value comparison theorems,
- a dense-image / continuity passage modeled on OS 1973 §4.3,

and does not rely on any new axiom or fake shortcut.
