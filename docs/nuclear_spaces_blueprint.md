# Nuclear Spaces Blueprint

Purpose: this note is the implementation blueprint for the nuclear-space and
Bochner-Minlos packages that feed the Wightman kernel theorem and the Euclidean
measure side.

It should be read together with:
- `docs/gns_pipeline_blueprint.md`,
- `docs/gns-pipeline-sorries.md`,
- `docs/r_to_e_blueprint.md`.

## 1. Live frontier surfaces

The relevant current open theorem surfaces are:

1. `subspace_seminorm_dominated` and `product_seminorm_dominated` in
   `Wightman/NuclearSpaces/NuclearSpace.lean`,
2. the Bochner-Minlos sorries in
   `Wightman/NuclearSpaces/BochnerMinlos.lean`,
3. the axioms
   `schwartz_nuclear_extension` and
   `exists_continuousMultilinear_ofSeparatelyContinuous`
   in `Wightman/WightmanAxioms.lean`.

These are not independent. They form one package:

1. nuclearity of the relevant Schwartz/Frechet spaces,
2. separately continuous multilinear maps become jointly continuous,
3. joint continuity feeds the Schwartz kernel theorem,
4. the kernel theorem feeds GNS cyclicity and Wightman packaging,
5. Bochner-Minlos feeds the measure-based Euclidean examples.

## 2. What is already available

The docs should treat the following as clean inputs:

1. `GaussianFieldBridge.lean` provides sorry-free Hermite and Gaussian
   infrastructure,
2. `ComplexSchwartz.lean` already transports nuclearity across complexification,
3. the basic `NuclearSpace` API exists and only two dominance theorems remain
   sorry-backed.

So the later implementation should not start from “what is a nuclear space?”
It should start from the two remaining dominance lemmas and the kernel-theorem
consumer interfaces.

## 3. Package A: Nuclearity infrastructure

The current explicit blockers in `NuclearSpace.lean` are:

1. `gauge_dominates_on_subspace_of_convex_nhd`,
2. `product_seminorm_dominated`.

These feed:

1. `subspace_seminorm_dominated`,
2. `subspace_nuclear`,
3. `product_nuclear`.

Documentation-standard theorem slots:

```lean
lemma gauge_dominates_on_subspace_of_convex_nhd
theorem subspace_seminorm_dominated
theorem subspace_nuclear

lemma product_coordinate_seminorm_control
theorem product_seminorm_dominated
theorem product_nuclear
```

The proof discipline should be:

1. prove subspace domination geometrically from convex neighborhoods and the
   gauge construction,
2. prove product domination from countable seminorm bookkeeping,
3. only then apply the generic nuclear-space closure lemmas already in the file.

### 3.1. Exact proof transcript for subspace domination

The later Lean file should prove `gauge_dominates_on_subspace_of_convex_nhd`
by the standard gauge argument, not by guessing constants.

Exact route:

1. let `i : S →L[ℝ] E` be the continuous inclusion,
2. for a given continuous seminorm `p` on `S`, choose a balanced convex
   neighborhood `V` of `0` in `S` such that `p x ≤ 1` on `V`,
3. use continuity of `i` at `0` to find a balanced convex neighborhood `U` in
   `E` with `i ⁻¹' U ⊆ V`,
4. define the Minkowski gauge `μ_U` on `E`,
5. show `p x ≤ μ_U (i x)` for all `x : S`,
6. package `μ_U` as the dominating ambient seminorm.

So the proof should be split as:

```lean
lemma subspace_preimage_of_convex_balanced_nhd
lemma minkowskiGauge_continuousSeminorm_of_convex_balanced_nhd
lemma seminorm_le_minkowskiGauge_on_preimage
lemma gauge_dominates_on_subspace_of_convex_nhd
theorem subspace_seminorm_dominated
```

The important point is that the constant should be `1` after the gauge choice;
the whole purpose of the Minkowski functional is to avoid a later rescaling
fight.

### 3.2. Exact proof transcript for countable-product domination

The later Lean proof of `product_seminorm_dominated` should proceed as:

1. let `p` be a continuous seminorm on `∀ i, E i`,
2. continuity of `p` at `0` gives a product neighborhood
   `∏ i, U_i` on which `p ≤ 1`,
3. by the product-topology basis, all but finitely many `U_i` are the whole
   space,
4. extract the finite support set `F`,
5. for each `i ∈ F`, replace `U_i` by a balanced convex neighborhood and form
   the corresponding coordinate gauge `q_i`,
6. prove
   `p x ≤ ∑ i in F, q_i (x i)`,
7. package the finite weighted sum as the dominating product seminorm.

The theorem-slot inventory should therefore include:

```lean
lemma continuousSeminorm_has_finite_coordinate_control
lemma product_coordinate_gauge_family
lemma product_coordinate_sum_dominates
theorem product_seminorm_dominated
```

This is the point where the countability/finiteness bookkeeping belongs. It
should not be postponed to `product_nuclear`.

## 4. Package B: Separate continuity to joint continuity

The axiom

```lean
exists_continuousMultilinear_ofSeparatelyContinuous
```

should eventually be replaced by a theorem package with exact slots:

```lean
lemma schwartz_isFrechet
lemma separatelyContinuous_multilinear_on_frechet
theorem exists_continuousMultilinear_ofSeparatelyContinuous
```

This is the Banach-Steinhaus / Frechet-space package. The docs should keep it
separate from the nuclear theorem itself.

### 4.1. Primary route and fallback route

The honest implementation choice should be:

1. **Primary route**: import the already-proved theorem from the local
   `gaussian-field` dependency and wrap it in the repo’s theorem surface,
2. **Fallback route**: prove the Frechet-space multilinear theorem locally by
   Banach-Steinhaus / barrelled-space arguments.

The primary route should be the default because the mathematical content is
already settled externally and the repo gap is mostly integration.

### 4.2. Exact proof transcript for the fallback route

If the import route is unavailable, the local proof should be organized as:

1. prove each Schwartz test space is a Frechet space,
2. prove the target scalar space is complete,
3. convert separate continuity into hypocontinuity on bounded sets,
4. apply the multilinear Banach-Steinhaus theorem on Frechet spaces,
5. package the resulting jointly continuous multilinear map.

The theorem slots should be:

```lean
lemma schwartzSpace_isFrechet
lemma separatelyContinuous_multilinear_is_hypocontinuous
lemma frechet_multilinear_banach_steinhaus
theorem exists_continuousMultilinear_ofSeparatelyContinuous
```

## 5. Package C: Schwartz kernel / nuclear theorem

The axiom

```lean
schwartz_nuclear_extension
```

is the next package and should be treated as the main direct consumer of
Packages A and B.

Documentation-standard theorem slots:

```lean
lemma schwartz_productTensor_dense
lemma schwartz_joint_space_nuclear
lemma multilinear_to_linear_kernel_candidate
lemma kernel_candidate_agrees_on_productTensor
theorem schwartz_nuclear_extension
```

This package is what later closes:

1. `wightmanDistribution_extends`,
2. `gns_cyclicity`,
3. any “product tests are dense” statements in the GNS uniqueness lane.

### 5.1. Primary route and exact consumer theorem

Again the honest primary route is:

1. import the Schwartz nuclearity instance / theorem from the local
   `gaussian-field` work,
2. derive the exact consumer theorem
   `schwartz_nuclear_extension`
   on the repo’s `SchwartzMap` / `SchwartzNPoint` surfaces,
3. immediately use that theorem to close the GNS and Wightman consumer files.

The local fallback route should only be used if the import/integration fails.

### 5.2. Exact proof transcript for the fallback route

The local proof should be decomposed as:

1. prove the algebraic product-tensor span is dense in the projective tensor
   product model of the joint Schwartz space,
2. use nuclearity to identify projective and injective tensor topologies,
3. convert the separately continuous multilinear functional into a continuous
   linear functional on the completed tensor product,
4. transport that functional to the concrete joint Schwartz space,
5. prove uniqueness by agreement on the dense product-tensor image.

So the theorem slots should be read as:

```lean
lemma schwartz_projectiveTensor_dense
lemma schwartz_projective_eq_jointSpace
lemma separatelyContinuous_to_projectiveTensor_linear
lemma projectiveTensor_linear_to_jointSpace_linear
lemma kernel_candidate_agrees_on_productTensor
theorem schwartz_nuclear_extension
```

The later implementation should not compress steps 2-4 into one opaque import
wrapper. Those are the exact places where the topology model has to match the
repo’s concrete `SchwartzMap` surface.

### 5.3. Exact intermediate extension package used by GNS consumers

The GNS and Wightman consumer files will be easier to implement if the kernel
theorem route is split into the exact “multilinear -> tensor -> joint space”
intermediate steps instead of jumping directly to
`schwartz_nuclear_extension`.

The later Lean file should therefore isolate:

```lean
lemma separatelyContinuous_multilinear_to_projectiveTensorMap
lemma projectiveTensorMap_continuous
lemma projectiveTensorMap_descends_to_jointSchwartz
lemma jointSchwartz_extension_agrees_on_productTensors
theorem schwartz_nuclear_extension
```

with the intended proof order:

1. build the algebraic multilinear-to-tensor linear map on pure tensors,
2. use separate-to-joint continuity plus nuclearity to extend it continuously
   to the completed projective tensor product,
3. identify that completed tensor product with the concrete joint Schwartz
   space,
4. transport the extension to the joint Schwartz space,
5. prove agreement on product tensors,
6. prove uniqueness from density.

That is the exact intermediate infrastructure a later `wightmanDistribution`
or `gns_cyclicity` implementation will need. The docs should no longer leave
that layer implicit.

## 6. Package D: Bochner finite-dimensional existence

The first open finite-dimensional theorem is:

```lean
private theorem bochner_tightness_and_limit
```

The later implementation should decompose it into:

1. approximate finite measures from mollified/compactly truncated data,
2. tightness,
3. weak-limit extraction,
4. characteristic-function recovery.

Documentation-standard theorem slots:

```lean
lemma bochner_approximate_measures_exist
lemma bochner_approximate_measures_tight
lemma bochner_weak_limit_exists
lemma bochner_limit_has_correct_characteristic_function
theorem bochner_tightness_and_limit
theorem bochner_existence
theorem bochner_theorem
```

### 6.1. Exact proof transcript

The later Lean file should prove the private tightness theorem by the following
literal sequence:

1. regularize the target characteristic function by compact cutoffs /
   mollification so Bochner’s classical finite-dimensional theorem applies to
   each approximant,
2. obtain a family of probability measures `μ_k` with characteristic functions
   `φ_k`,
3. prove tightness of `μ_k` from the uniform control inherited from the
   positive-definite normalized characteristic functions,
4. apply Prokhorov to obtain a weakly convergent subsequence,
5. use weak convergence plus continuity of bounded exponentials to identify the
   limit characteristic function with `φ`,
6. package the limit measure as the output of
   `bochner_tightness_and_limit`.

The theorem slots should therefore include:

```lean
lemma bochner_regularized_charfun
lemma bochner_regularized_measure_exists
lemma bochner_regularized_family_tight
lemma prokhorov_subsequence_of_tight
lemma weakLimit_charfun_eq_limit
theorem bochner_tightness_and_limit
```

## 7. Package E: Minlos projective family and uniqueness

The open Minlos-side theorems are:

1. `minlos_projective_consistency`,
2. `minlos_nuclearity_tightness`,
3. `eval_maps_generate_sigma_algebra`,
4. `eval_charfun_implies_fd_distributions`,
5. the downstream `minlos_theorem` / `minlos_unique` consumers.

The implementation order should be:

1. finite-dimensional projection measures,
2. projective consistency,
3. nuclearity-driven tightness,
4. Kolmogorov/projective extension,
5. uniqueness from evaluation-characteristic functions.

Documentation-standard theorem slots:

```lean
lemma minlos_finite_dim_projection
lemma minlos_projective_consistency
lemma minlos_nuclearity_tightness
lemma minlos_kolmogorov_extension
theorem minlos_theorem

lemma eval_maps_generate_sigma_algebra
lemma eval_charfun_implies_fd_distributions
theorem measures_eq_of_eval_charfun_eq
theorem minlos_unique
```

### 7.1. Exact proof transcript

The later Lean implementation should split Minlos into two separate chains.

Existence chain:

1. define finite-dimensional projection measures by Bochner on each finite set
   of test directions,
2. prove projective consistency under coordinate restriction,
3. use nuclearity to prove tightness / cylindrical Radon control,
4. apply the projective-extension theorem to get a measure on the dual,
5. prove its characteristic functional equals the original one.

Uniqueness chain:

1. prove evaluation maps generate the relevant sigma-algebra,
2. prove equality of characteristic functionals implies equality of every
   finite-dimensional marginal,
3. conclude equality of measures from equality on the generating cylinder
   sigma-algebra.

So the theorem slots should be read as:

```lean
lemma eval_projection_charfun
lemma projection_family_projectively_consistent
lemma nuclearity_implies_cylindrical_tightness
lemma projective_family_extension_exists
theorem minlos_theorem

lemma cylinder_sets_generate_sigma
lemma charfun_eq_implies_projection_eq
lemma measures_eq_of_projection_eq
theorem minlos_unique
```

## 8. Exact dependency graph

The later implementation should proceed in this order:

1. finish `NuclearSpace.lean` dominance lemmas,
2. replace separate-continuity axiom,
3. replace Schwartz nuclear-extension axiom,
4. close `gns_cyclicity`,
5. separately finish the Bochner finite-dimensional existence package,
6. then the Minlos projective/tightness/uniqueness package.

The docs should not present Bochner-Minlos as if it were required before the
GNS/kernel theorem. They are parallel consumers of overlapping nuclear-space
infrastructure.

## 9. Lean-style pseudocode for the kernel-theorem consumer side

```lean
theorem wightmanDistribution_extends (qft : WightmanQFT d) (n : ℕ) :
    ∃ W_n : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ,
      ∀ fs, W_n (SchwartzMap.productTensor fs) =
        qft.vacuumExpectation n fs := by
  obtain ⟨PhiCont, hPhiCont⟩ :=
    exists_continuousMultilinear_ofSeparatelyContinuous
      (d := d) (n := n) (wightman_separately_continuous qft n)
  obtain ⟨W_n, hW_n, _⟩ := schwartz_nuclear_extension (d := d) (n := n) PhiCont
  exact ⟨W_n, hW_n⟩
```

## 10. Do not do this

1. Do not mix the Frechet separate-continuity theorem with the kernel theorem.
2. Do not treat Bochner and Minlos as one undifferentiated measure theorem.
3. Do not reopen the sorry-free GaussianFieldBridge package.
4. Do not let GNS cyclicity smuggle in the nuclear theorem implicitly.

## 11. What counts as implementation-ready

This blueprint should be considered ready only when:

1. the two open `NuclearSpace.lean` dominance lemmas are isolated,
2. the two current axioms are split into theorem packages,
3. the Bochner and Minlos packages are separated into finite-dimensional,
   projective, tightness, and uniqueness layers,
4. the dependency from these packages to GNS cyclicity is explicit.

## 12. Recommended implementation order and size

The later implementation should treat these as five separate work packages:

1. `NuclearSpace.lean` domination lemmas: 180-260 lines,
2. separate-to-joint continuity import/wrapper or fallback proof:
   80-160 lines,
3. kernel-theorem consumer package:
   140-220 lines,
4. Bochner finite-dimensional existence:
   180-260 lines,
5. Minlos existence/uniqueness:
   220-320 lines.

The whole package is ready for implementation once these five items are read as
literal construction units with the stated order, not as a single “nuclear
spaces” blob.
