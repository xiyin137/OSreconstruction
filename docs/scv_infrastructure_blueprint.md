# SCV Infrastructure Blueprint

Purpose: this note is the implementation blueprint for the remaining
several-complex-variables infrastructure that other proof lanes depend on.

It should be read together with:
- `docs/theorem2_locality_blueprint.md`,
- `docs/theorem3_os_route_blueprint.md`,
- `docs/general_k_continuation_blueprint.md`,
- `docs/gns_pipeline_blueprint.md`.

## 1. Scope

This blueprint covers the SCV packages that are still axiomatic or sorry-backed:

1. `SCV/VladimirovTillmann.lean`,
2. `SCV/BochnerTubeTheorem.lean`,
3. `SCV/TubeBoundaryValues.lean`,
4. the pure tube-domain / identity-theorem interfaces those packages consume.

It does **not** re-document the already proved:

1. `SCV.edge_of_the_wedge_theorem`,
2. `identity_theorem_SCV`,
3. `identity_theorem_tubeDomain`,
4. `identity_theorem_product`.

## 2. Current status by file

### 2.1. `VladimirovTillmann.lean`

Still axiomatic:

1. `vladimirov_tillmann`,
2. `distributional_cluster_lifts_to_tube`.

These are major analytical packages, not single missing lemmas.

### 2.2. `TubeBoundaryValues.lean`

Still axiomatic:

1. `tube_boundaryValueData_of_polyGrowth`.

This is the QFT-free boundary-value theorem from polynomial growth on a tube
domain.

### 2.3. `BochnerTubeTheorem.lean`

Still sorry-backed:

1. `bochner_local_extension`,
2. `bochner_tube_extension`.

The good news is that the global gluing theorem
`holomorphic_extension_from_local_family`
is already in place, so the remaining content is precise.

## 3. Package A: Tube boundary values from polynomial growth

The theorem surface to replace is:

```lean
tube_boundaryValueData_of_polyGrowth
```

The later Lean port should split it into:

```lean
lemma tubeSlice_polyGrowth_uniform
lemma tubeSlice_family_is_equicontinuous_on_schwartz
lemma tubeSlice_pairing_cauchy_as_epsilon_to_zero
lemma tubeSlice_limit_defines_continuous_functional
lemma tube_boundary_value_exists_of_polyGrowth
theorem tube_boundaryValueData_of_polyGrowth
```

This package is the honest SCV input behind later boundary-value reconstruction
steps. It should stay QFT-free.

## 4. Package B: Vladimirov-Tillmann

The theorem

```lean
vladimirov_tillmann
```

should not be treated as one indivisible axiom. The later implementation should
split it into:

1. boundary-value distribution gives Fourier support in the dual cone,
2. Fourier-Laplace representation on the tube,
3. compact-subcone polynomial growth,
4. global distance-to-boundary growth estimate.

Documentation-standard theorem slots:

```lean
lemma boundary_distribution_supports_dual_cone
lemma tube_function_has_fourier_laplace_repr
lemma compact_subcone_growth_of_fourier_laplace_repr
lemma global_boundary_distance_growth
theorem vladimirov_tillmann
```

This package is the natural supplier for later `HasFourierLaplaceReprRegular`
and uniqueness theorems.

## 5. Package C: Distributional cluster lifts to tube interior

The theorem

```lean
distributional_cluster_lifts_to_tube
```

should be documented as a Poisson-kernel / boundary-value transport package,
not as a free corollary of analyticity.

Documentation-standard theorem slots:

```lean
lemma poisson_kernel_for_tube_domain
lemma tube_interior_eval_as_boundary_pairing
lemma translated_boundary_pairing_tends_to_factorized_limit
lemma poisson_pairing_respects_block_translation
theorem distributional_cluster_lifts_to_tube
```

This package is currently on the reverse-direction cluster lane, not the active
`E -> R` theorem-3 lane.

## 6. Package D: Bochner tube extension

The remaining content in `BochnerTubeTheorem.lean` is already sharply isolated.

The later implementation should proceed as:

1. strengthen local extension to a standard convex local family,
2. prove compatibility on overlaps,
3. invoke `holomorphic_extension_from_local_family`,
4. conclude the global extension theorem.

Documentation-standard theorem slots:

```lean
lemma convex_local_tube_patch_around_convexHull_point
lemma cauchy_integral_local_extension_on_patch
lemma distinguished_boundary_of_patch_lies_in_original_tube
theorem bochner_local_extension
theorem bochner_tube_extension
```

The current docs should treat the remaining blocker as “construct the compatible
local family,” not “global gluing is missing.”

## 7. Exact dependency order

The SCV infrastructure should be implemented in this order:

1. finish `BochnerTubeTheorem.lean`,
2. replace `tube_boundaryValueData_of_polyGrowth`,
3. replace `vladimirov_tillmann`,
4. replace `distributional_cluster_lifts_to_tube`.

The order matters because:

1. Bochner extension is a local analyticity/gluing theorem,
2. boundary values need polynomial growth input,
3. Vladimirov-Tillmann supplies the global growth machinery,
4. cluster lifting is a later consumer of the full boundary-value transport
   package.

## 8. Consumers

The current main consumers are:

1. theorem 2 locality uses the forward-tube regular boundary-value package,
2. the general-`k` continuation blueprint uses Bochner/Malgrange-Zerner style
   SCV infrastructure,
3. the GNS holomorphic bridge needs forward-tube boundary-value transport,
4. the reverse-direction cluster lane currently references
   `distributional_cluster_lifts_to_tube`.

## 9. Do not do this

1. Do not re-axiomatize `edge_of_the_wedge`; it is already proved.
2. Do not mix QFT-specific support hypotheses into the SCV theorem statements.
3. Do not state Vladimirov-Tillmann as a single future proof obligation without
   the Fourier-support / Laplace-representation / growth subpackages.
4. Do not let later proof docs say “by several-complex-variables machinery”
   unless they point to an exact theorem slot here.

## 10. What counts as implementation-ready

This SCV blueprint should be considered ready only when:

1. the remaining axioms/sorries are decomposed into theorem packages,
2. each package has a named consumer,
3. the dependency order is explicit,
4. already-proved SCV theorems are kept separate from the live open ones.

This note now records all four.

## 11. Exact proof transcript for tube boundary values from polynomial growth

Package A should now be written at theorem-3-style detail. The later Lean proof
should proceed in the following order.

1. Fix a compact subcone `Γ₀` of the open cone `Γ`.
2. For each `y ∈ Γ₀` and `ε > 0`, define the slice functional
   `L_{ε,y}(φ) := ∫ F(x + i ε y) φ(x) dx`.
3. Use polynomial growth of `F` on the tube to prove a uniform Schwartz
   seminorm bound on `L_{ε,y}` as `ε -> 0`.
4. Prove the family `L_{ε,y}` is Cauchy on Schwartz test functions by applying
   Cauchy estimates to differences in the imaginary direction.
5. Define the limiting continuous functional `L_y`.
6. Prove `L_y` is independent of the chosen approach direction `y` inside the
   same cone component.
7. Package the common limit as the boundary-value distribution.
8. Prove the recovered distribution gives back the original tube function by
   the standard Poisson/Fourier-Laplace reconstruction formula.

The implementation theorem slots should therefore be:

```lean
def tubeSliceFunctional (ε : ℝ) (y : ConeDir) : SchwartzMap →L[ℂ] ℂ
lemma tubeSliceFunctional_seminorm_bound
lemma tubeSliceFunctional_cauchy_as_epsilon_to_zero
lemma tubeSliceFunctional_limit_exists
lemma tubeSliceFunctional_limit_independent_of_direction
def tubeBoundaryValueDistribution
lemma tubeBoundaryValueDistribution_isContinuous
lemma tubeBoundaryValueDistribution_recovers_tube_function
theorem tube_boundaryValueData_of_polyGrowth
```

The critical documentation point is that this theorem is a QFT-free
distributional boundary-value package. It should not mention Wightman,
Schwinger, or Borchers data anywhere in its final statement.

## 12. Exact one-point forward-tube bridge used by theorem 2 and GNS

The repo now has two consumers that want the same one-variable forward-tube
package:

1. theorem 2 locality, through the flattened regular-input constructor,
2. the GNS matrix-coefficient holomorphic bridge.

So the SCV docs should isolate the common one-point package explicitly:

```lean
lemma onePoint_forward_support_to_flatRegular
    (u : TemperedDistribution (MinkowskiSpace d))
    (hsupp : ForwardSupported u) :
    HasFourierLaplaceReprRegularOnePoint u

lemma onePoint_boundary_value_recovery
    (u : TemperedDistribution (MinkowskiSpace d))
    (hreg : HasFourierLaplaceReprRegularOnePoint u) :
    boundaryValueOfOnePointExtension hreg = u

lemma onePoint_forwardTube_uniqueness
    (F G : ComplexSpacetime d → ℂ)
    (hF : DifferentiableOn ℂ F (TranslationForwardTube d))
    (hG : DifferentiableOn ℂ G (TranslationForwardTube d))
    (hbdry : sameOnePointBoundaryValue F G) :
    EqOn F G (TranslationForwardTube d)
```

This package is deliberately smaller than the full tube-boundary theorem. The
future Lean port should prove it first if theorem 2 / GNS resume before the
full SCV boundary-value package is complete.

### 12.1. Exact proof transcript for the one-point forward-tube bridge

The later Lean proof should not leave the one-point package as a mere trio of
consumer theorem names. The exact mathematical route should be:

1. start from a one-point tempered distribution `u` with forward support,
2. take its Fourier transform `û`,
3. use forward support to prove `supp û` lies in the closed dual forward cone,
4. define the candidate holomorphic extension on the one-point forward tube by
   the Fourier-Laplace integral
   `F(z) := ∫ e^{-i⟨p,z⟩} dû(p)`,
5. prove the integral is absolutely/convergently well-defined for
   `Im z ∈ ForwardCone`,
6. prove holomorphy by differentiating under the integral,
7. prove the boundary value along `z = x + i ε y` tends to `u` in tempered
   distribution sense as `ε -> 0+`,
8. prove uniqueness by applying the one-variable tube identity theorem to the
   difference of two candidate extensions with the same boundary value.

So the real theorem-slot inventory should be:

```lean
lemma onePoint_distribution_supports_dual_forwardCone
lemma onePoint_fourierLaplace_integral_converges
lemma onePoint_fourierLaplace_integral_holomorphic
def onePoint_forwardTube_extension
lemma onePoint_forward_support_to_flatRegular
lemma onePoint_boundary_value_recovery
lemma onePoint_zero_boundaryValue_implies_zero
lemma onePoint_forwardTube_uniqueness
```

The proof discipline should be:

1. support theorem first,
2. explicit Fourier-Laplace construction second,
3. boundary-value recovery third,
4. uniqueness last.

That is the route both theorem 2 and the GNS matrix-coefficient bridge should
consume. Neither should build its own one-point SCV theory.

## 13. Exact proof transcript for Vladimirov-Tillmann

Package B should be written as a four-stage chain, not a single theorem.

1. Start with a boundary-value distribution on the real edge of a tube.
2. Use dual-cone test-function estimates to prove Fourier support in the dual
   cone.
3. Use that support theorem to build the Fourier-Laplace representation of the
   tube function.
4. Prove growth on compact subcones by estimating the Laplace kernel against
   the supported Fourier transform.
5. Convert compact-subcone growth to a global distance-to-boundary estimate.

The theorem slots should therefore be read as:

```lean
lemma boundary_distribution_supports_dual_cone
lemma dual_cone_supported_distribution_has_laplace_repr
lemma laplace_repr_matches_tube_function
lemma compact_subcone_growth_bound
lemma distance_to_boundary_growth_bound
theorem vladimirov_tillmann
```

The later Lean proof should not skip directly from "boundary distribution" to
"global boundary-distance growth." The Fourier-support / Laplace-representation
middle layer is the real mathematical content of the theorem.

## 14. Exact proof transcript for Bochner tube extension

Package D should also be made proof-transcript-level explicit.

1. Fix a point in the convex hull of the original tube base.
2. Construct a small convex neighborhood whose translated distinguished
   boundary still lies in the original tube.
3. Define the local holomorphic extension on that patch by a Cauchy integral on
   the distinguished boundary.
4. Prove that on overlaps of two such patches, the two local extensions agree
   by the identity theorem.
5. Feed the compatible local family to the already-proved global gluing theorem
   `holomorphic_extension_from_local_family`.
6. Conclude the global Bochner extension on the convex hull.

The implementation theorem slots should therefore be:

```lean
lemma convex_local_tube_patch_around_convexHull_point
lemma distinguished_boundary_of_patch_lies_in_original_tube
lemma cauchy_integral_local_extension_on_patch
lemma local_extensions_agree_on_overlap
lemma local_family_is_compatible
theorem bochner_local_extension
theorem bochner_tube_extension
```

The important route constraint is that the global gluing theorem is already in
place. So the later proof should spend its effort on the explicit local family
construction and overlap agreement, not on reproving a general sheaf-gluing
result.

## 15. Estimated Lean size by SCV package

The SCV docs should now record rough proof sizes so later implementation can be
split honestly.

1. one-point forward-tube bridge:
   `80-180` lines.
2. tube boundary values from polynomial growth:
   `180-320` lines.
3. Vladimirov-Tillmann:
   `220-420` lines.
4. Bochner local/global tube extension:
   `140-260` lines.

So the live open SCV package should now be thought of as roughly
`620-1180` lines of QFT-free analysis, split across four packages rather than
one monolithic "SCV machinery" theorem.
