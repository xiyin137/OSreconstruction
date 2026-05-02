# Theorem 2 Locality Blueprint

Purpose: this note is the theorem-specific implementation blueprint for the
theorem-2 `E -> R` locality frontier.  The current production code still has
the private sufficient-condition frontier

- `OSToWightmanBoundaryValues.lean`, private theorem
  `bvt_F_swapCanonical_pairing`.

The recommended proof route is no longer to force that overstrong finite-height
canonical-shell theorem first.  The primary OS route is now the BHW/PET
boundary route: prove a non-circular permutation-edge theorem for
`extendF (bvt_F OS lgc n)`, add the corresponding boundary-transfer theorem,
and then retire or bypass the private finite-shell sufficient condition.  The
finite-shell packet remains a fallback only if we deliberately keep the current
private consumer unchanged.

This note supersedes older gap notes that were written before
`edge_of_the_wedge` was proved as a theorem.

This note should be read together with:
- `docs/os1_detailed_proof_audit.md`, Section 9,
- `docs/theorem3_os_route_blueprint.md` only for route discipline,
- `docs/edge_of_the_wedge_proof_plan.md` and
  `docs/edge_of_the_wedge_gap_analysis.md` only as historical reference.

### 0.1. Checked production inventory and current trap

Theorem-2 work spans several support layers, so this blueprint now fixes the
checked file inventory before any Lean implementation resumes:

- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean`
- `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
- `OSReconstruction/ComplexLieGroups/JostPoints.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`

Checked-present theorem surfaces that are useful but must be used with their
actual hypotheses:

- `BHWExtension.lean :: W_analytic_swap_boundary_pairing_eq`
- `BHWExtension.lean :: analytic_extended_local_commutativity`
- `BHWExtension.lean :: analytic_boundary_local_commutativity_of_boundary_continuous`
- `AdjacencyDistributional.lean :: extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
- `Adjacency.lean :: exists_real_open_nhds_adjSwap`
- `ForwardTubeDistributions.lean :: boundary_function_continuous_forwardTube_of_flatRegular`
- `OSToWightmanBoundaryValuesComparison.lean :: bv_local_commutativity_transfer_of_swap_pairing`
- `OSToWightmanTubeIdentity.lean :: eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen`
- `OSToWightmanTubeIdentity.lean :: EuclideanOrderedPositiveTimeSector`
- `OSToWightmanTubeIdentity.lean :: positiveTimeTranslate`
- `OSToWightmanTubeIdentity.lean :: exists_uniform_positiveTimeShift_of_compact_tsupport`
- `OSToWightmanTubeIdentity.lean :: isOpen_positiveTimeTranslate_image`
- `OSToWightmanTubeIdentity.lean :: wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector`
- `OSToWightmanTubeIdentity.lean :: positiveTimeTranslate_mem_orderedPositiveTimeSector_of_pairwise_distinct`
- `OSToWightmanTubeIdentity.lean :: timeShiftSchwartzNPoint_apply_positiveTimeTranslate`
- `OSToWightmanTubeIdentity.lean :: hasCompactSupport_timeShiftSchwartzNPoint`
- `OSToWightmanTubeIdentity.lean :: tsupport_timeShiftSchwartzNPoint_subset_positiveTimeTranslate_image`
- `OSToWightmanTubeIdentity.lean :: measure_timeCoord_eq_zero`
- `OSToWightmanTubeIdentity.lean :: ae_pairwise_distinct_timeCoords`
- `Connectedness/PermutedTube.lean :: mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube`
- `Connectedness/PermutedTube.lean :: permutedExtendedTubeBranch`
- `Connectedness/PermutedTube.lean :: permutedExtendedTubeBranch_mem_extendedTube`
- `ForwardTubeLorentz.lean :: isOpen_translatedPET`
- `ForwardTubeLorentz.lean :: translatedPET_perm`
- `ForwardTubeLorentz.lean :: translatedPET_perm_iff`
- `ForwardTubeLorentz.lean :: translatedPET_value_eq_of_translation_invariant`
- `ForwardTubeLorentz.lean :: translatedPETValue`
- `ForwardTubeLorentz.lean :: translatedPETValue_eq_on_PET`
- `ForwardTubeLorentz.lean :: translatedPETValue_translation_invariant`
- `ForwardTubeLorentz.lean :: translatedPETValueTotal`
- `ForwardTubeLorentz.lean :: translatedPETValueTotal_eq_on_PET`
- `ForwardTubeLorentz.lean :: translatedPETValueTotal_translation_invariant`
- `OSToWightmanBoundaryValuesBase.lean :: bvt_F_acrOne_package`
- `Connectedness/PermutedTube.lean :: permutedExtendedTubeSector`
- `Connectedness/PermutedTube.lean :: isOpen_permutedExtendedTubeSector`
- `Connectedness/PermutedTube.lean :: permutedExtendedTube_eq_iUnion_sectors`
- `Connectedness/PermutedTube.lean :: permutedExtendedTubeSector_subset_permutedExtendedTube`
- `Connectedness/PermutedTubeConnected.lean :: permutedExtendedTubeSector_isPreconnected`
- `Connectedness/PermutedTubeConnected.lean :: permutedExtendedTubeSector_adjacent_overlap_nonempty`
- `Connectedness/PermutedTubeGluing.lean :: gluedPETValue`
- `Connectedness/PermutedTubeGluing.lean :: gluedPETValue_eq_of_mem_sector`
- `Connectedness/PermutedTubeGluing.lean :: gluedPETValue_holomorphicOn`
- `OSToWightmanSelectedWitness.lean :: SelectedAdjacentPermutationEdgeData`
- `OSToWightmanSelectedWitness.lean :: SelectedAllPermutationEdgeData` (overstrong conditional helper only)
- `OSToWightmanSelectedWitness.lean :: bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETBranch`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETBranch_holomorphicOn_sector`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`
- `OSToWightmanSelectedWitness.lean :: bvt_F_extendF_perm_overlap_of_selectedEdgeData`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_eq_extendF_perm`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_eq_bvt_F_on_forwardTube`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_holomorphicOn_PET`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_lorentzInvariant`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_permInvariant`
- `OSToWightmanSelectedWitness.lean :: bvt_route1AbsolutePrePullback`
- `OSToWightmanSelectedWitness.lean :: bvt_route1AbsolutePrePullback_translate`
- `OSToWightmanSelectedWitness.lean :: bvt_route1AbsolutePrePullback_eq_bvt_F_on_forwardTube`
- `OSToWightmanSelectedWitness.lean :: bvt_reducedWightmanFamily`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedReducedPreInput_factorization_absoluteApproach`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedReducedBoundaryIntegral_eq_absoluteBoundaryIntegral`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedReducedBoundaryValues`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedReducedForwardTubeInput`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData_translate`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData_translate_on_PET`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData_eq_bvt_F_on_forwardTube`

Important correction: the first four BHW/adjacency locality surfaces above
currently take an input of the form
`IsLocallyCommutativeWeak d W`.  When `W := bvt_W OS lgc`, that is exactly the
public theorem-2 locality conclusion being proved downstream.  Therefore none
of these theorem surfaces may be instantiated directly with
`bvt_locally_commutative` or with any equivalent global locality hypothesis for
`bvt_W OS lgc` in the theorem-2 proof.  Doing so would be circular even if the
Lean term typechecks.

The missing theorem-2 work is consequently sharper than older drafts suggested.
The primary OS-I-faithful route needs a non-circular BHW/PET permutation-edge
supplier for `extendF`, plus the geometry and transfer adapters that feed it.
The older adjacent-swap finite-shell package remains a fallback only if we
retain the current overstrong canonical-shell consumer.

### 0.2. Route-contract ledger for the missing theorem-2 package

The following names are planned theorem-package names fixed by this blueprint.
They are not assumed to exist in the current tree until implemented.

Important correction: the primary route must not prove locality by asserting
global continuity of the raw real trace
`x ↦ bvt_F OS lgc n (BHW.realEmbed x)`.  Wightman boundary values are
distributional in general.  Any `HasFourierLaplaceReprRegular` or
`boundary_continuous` package below is fallback/support context, not the primary
theorem-2 bridge.

| Slot | Home | Must consume | Must export |
| --- | --- | --- | --- |
| `choose_real_open_edge_for_adjacent_swap` | `BHWPermutation/Adjacency.lean` or a theorem-2 wrapper next to it | `exists_real_open_nhds_adjSwap` plus compact support inclusion for `tsupport f` | an open real edge `V` containing `tsupport f`, with ET and swapped-ET control |
| `swapped_support_lies_in_swapped_open_edge` | same Route-B geometry layer | the swap identity for `g` and `tsupport f ⊆ V` | support transport for `g` into the swapped open edge |
| `bvt_F_acrOne_package` | `OSToWightmanBoundaryValuesBase.lean` or a small selected-witness support file | a strengthened/refactored `full_analytic_continuation_with_symmetry_growth` theorem that retains the ACR(1) conjunct from the chosen witness | ACR(1) holomorphy, Euclidean reproduction, permutation symmetry, and translation symmetry for the selected `bvt_F OS lgc n` |
| `bvt_F_extendF_perm_eq_on_realJost_of_OS_symmetry` | `BHWExtension.lean` theorem-2 boundary layer, with OS adapters near WickRotation if cleaner | `OS.E3_symmetric`, `bvt_euclidean_restriction`, Lorentz invariance of `bvt_F`, Jost/BHW geometry, and identity/EOW propagation on the connected real Jost edge | pointwise equality of the BHW analytic continuation `extendF (bvt_F OS lgc n)` on permuted real Jost edge points |
| `BHW.HasPermutationEdgeDistributionEquality` | `BHWExtension.lean` / `BHWPermutation` support layer | a real-open Jost edge `V`, ET and permuted-ET control, and compact support of the test function | a predicate packaging permutation equality of `extendF F` as a compactly supported edge-distribution equality |
| `bvt_F_distributionalEOW_permBranch_from_euclideanEdge` | SCV/BHW theorem-2 support layer | selected `bvt_F` ACR(1) package, compact-test Euclidean edge equality, and a distributional EOW theorem | transports compact-test Euclidean branch equality to compact-test real-Jost branch equality without raw real-trace continuity |
| `bvt_F_extendF_adjacentEdgeDistribution_eq_from_OS` | WickRotation theorem-2 support layer | adjacent Euclidean order change plus `bvt_F_distributionalEOW_permBranch_from_euclideanEdge` | adjacent/order-change version of the branch distribution equality; the true local EOW seed |
| `bvt_F_extendF_perm_edgeDistribution_eq_from_OS` | WickRotation theorem-2 support layer | adjacent branch-distribution seed plus BHW/PET permutation-flow propagation, or explicit transported-overlap induction | equality of the two `extendF (bvt_F OS lgc n)` real-overlap branch pairings against compact tests for a finite permutation |
| `BHW.permuteSchwartz` and support/measure lemmas | `BHWPermutation/EdgeDistribution.lean` | implemented from coordinate permutation as a continuous linear equivalence | reusable permuted Schwartz test functions, Jost-support transport, compact-support transport, topological-support transport, and permutation-invariant integral change of variables |
| `bvt_W_perm_invariant_on_compactJostOverlap_from_OS` | WickRotation theorem-2 support layer | `bvt_F_extendF_perm_edgeDistribution_eq_from_OS`, change of variables, ET/permuted-ET support transport, and `bvt_boundary_values` | optional compatibility adapter: distributional permutation equality for `bvt_W OS lgc n` on compactly supported tests with `tsupport ⊆ V` |
| `BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality` | `BHWPermutation/EdgeDistribution.lean` | implemented from compact-test pairing equality, continuity of the two `extendF` real-edge traces, and `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` | pointwise equality of `extendF F` on any real-open Jost/permutation-overlap edge |
| `BHW.extendF_perm_eq_on_realOpen_of_jost_distribution_symmetry` | `BHWPermutation/PermutationFlow.lean` or new companion file | secondary compatibility route copying the private hLC proof spine, with `hW_overlap_perm` replacing `hF_local_dist` | same pointwise equality as the direct edge-distribution theorem; not the preferred primary route once `bvt_F_hasPermutationEdgeDistributionEquality` is available |
| `bvt_F_hasPermutationEdgeDistributionEquality` | WickRotation theorem-2 support layer | `bvt_F_extendF_perm_edgeDistribution_eq_from_OS` and the support-zero lemma outside `tsupport` | OS-side edge-distribution equality for every finite permutation, without any global `IsLocallyCommutativeWeak d (bvt_W OS lgc)` input |
| `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` | `BHWExtension.lean`, with lower helpers in `AdjacencyDistributional.lean` if needed | Route-B ET support, Euclidean/permutation symmetry, and EOW/uniqueness inputs | adjacent-only raw-boundary pairing equality without any global `IsLocallyCommutativeWeak d (bvt_W OS lgc)` input |
| `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` | `BHWExtension.lean` theorem-2 boundary-pairing layer | the adjacent-only raw-boundary supplier above | theorem-2-facing adjacent raw-boundary equality for `bvt_F`; useful edge data, not the finite-shell frontier |
| `canonical_adjacentSwap_shell_mem_EOW_domain` | BHW / adjacency geometry layer | canonical direction, `ε > 0`, adjacent spacelike support, and the Route-B overlap package | membership of the two finite canonical-shell configurations in the EOW/extended-tube domain where adjacent interchange is valid |
| `bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike` | `BHWExtension.lean` theorem-2 finite-shell layer | `bvt_F_holomorphic`, Lorentz invariance, boundary continuity, and `canonical_adjacentSwap_shell_mem_EOW_domain` | pointwise equality between the permuted-imaginary-direction shell and the canonical shell over the same real edge |
| `bvt_F_adjacentSwapCanonical_pointwise_of_spacelike` | `BHWExtension.lean` theorem-2 finite-shell layer | `swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell`, `bvt_F_perm`, and the permuted-eta finite-shell theorem | pointwise equality of the swapped-real-coordinate finite shell with the canonical shell for one adjacent spacelike pair |
| `bvt_F_adjacentSwapCanonical_pairing_from_pointwise` | `OSToWightmanBoundaryValueLimits.lean` or `OSToWightmanBoundaryValuesComparison.lean` support layer | measure-preserving coordinate reindexing, support-zero outside `tsupport f`, `hswap`, and the pointwise finite-shell theorem | adjacent canonical-shift pairing equality |
| `bvt_F_reduced` | `OSToWightmanReduced.lean` | implemented from `safeSection` and the selected OS witness | reduced-coordinate representative of `bvt_F` |
| `bvt_F_eq_bvt_F_reduced_reducedDiffMap` | `OSToWightmanReduced.lean` | implemented from `bvt_F_translationInvariant`, `reducedDiffMap_safeSection`, and `exists_uniformShift_eq_of_reducedDiffMap_eq` | pointwise factorization of `bvt_F OS lgc n z` through `reducedDiffMap n d z` |
| `canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirection` | `OSToWightmanReduced.lean` | implemented from `canonicalForwardConeDirection`, `reducedDiffMap`, and `safeBasepointVec` | reduced direction of the public canonical shell is the product-cone direction `safeBasepointVec` in every reduced slot |
| `permutedCanonicalForwardDirection_reducedDiff_eq_permOnReducedDiff` | `OSToWightmanReduced.lean` | implemented from `permOnReducedDiff_reducedDiffMap` and the previous direction lemma | reduced direction of `canonicalForwardConeDirection ∘ Equiv.swap i j` |
| `reducedPairDiff_reducedDiffMapReal` | `OSToWightmanReduced.lean` | implemented from `realDiffCoordCLE`, `prependBasepointReal`, and translation-cancellation algebra | support hypothesis `AreSpacelikeSeparated d (x i) (x j)` rewritten in reduced coordinates |
| `bvt_F_reduced_permOnReducedDiff` | `OSToWightmanReduced.lean` | implemented from reduced factorization, `permOnReducedDiff_reducedDiffMap`, and `bvt_F_perm` | reduced-coordinate permutation invariance of the descended OS-side witness |
| `permOnReducedDiff_swap_permutedCanonicalDirection` | `OSToWightmanReduced.lean` | implemented from `permOnReducedDiff_mul` and involutivity of `Equiv.swap` | selected swap sends the permuted canonical reduced direction back to the canonical reduced direction |
| `bvt_F_reduced_permutedDirection_to_realPermutedCanonical` | `OSToWightmanReduced.lean` | implemented from `bvt_F_reduced_permOnReducedDiff` | converts the permuted-imaginary-direction comparison into a canonical-direction comparison at the permuted real reduced basepoint |
| `reducedSpacelikeSwapEdge` | `OSToWightmanReduced.lean` | implemented from `reducedPairDiff` and `MinkowskiSpace.IsSpacelike` | the real reduced edge on which the selected pair is spacelike |
| `isOpen_reducedSpacelikeSwapEdge` | `OSToWightmanReduced.lean` | implemented from continuity of `reducedPairDiff` and openness of the spacelike cone | openness of the real reduced edge for local EOW neighborhoods |
| `bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge` | `OSToWightmanReduced.lean` | implemented from `bvt_F_reduced_permOnReducedDiff` | boundary equality of the two reduced branches on the spacelike real edge |
| `bvt_F_reduced_holomorphicOn_reducedForwardTube` / `bvt_F_reduced_holomorphicOn_swapPulledForwardTube` | `OSToWightmanReduced.lean` | implemented from `bvt_F_holomorphic`, `safeSection_mem_forwardTube`, and differentiability of the safe section / reduced permutation map | holomorphicity of the two reduced branches on their tube domains |
| `reduced_local_EOW_canonicalRealSwap` | reduced BHW/EOW support layer | the reduced real edge, boundary equality, branch holomorphicity, and a non-circular two-cone EOW/BHW continuation theorem | canonical-direction equality after acting on the reduced real basepoint by the selected transposition |
| `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike` | reduced finite-shell adapter layer | `reduced_local_EOW_canonicalRealSwap` | theorem-2-facing canonical real-swap equality under the pointwise spacelike hypothesis |
| `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike` | reduced finite-shell adapter layer | the three algebraic reduced-permutation lemmas and `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike` | equality between the reduced permuted-canonical-direction shell and the reduced canonical shell |
| `reducedDiffMap_canonicalShell_eq` | `OSToWightmanReduced.lean` | implemented from reduced real differences and canonical reduced direction | reduced coordinates of the canonical shell split into real reduced basepoint plus canonical imaginary direction |
| `reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq` | `OSToWightmanReduced.lean` | implemented from reduced real differences and the permuted canonical reduced direction | reduced coordinates of the permuted-eta shell split into real reduced basepoint plus permuted imaginary direction |
| `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike` | theorem-2 finite-shell layer | reduced factorization, reduced direction lemmas, `reducedPairDiff_reducedDiffMapReal`, and the reduced local-edge theorem | pointwise equality between the arbitrary-swap permuted-eta shell and the canonical shell for the same spacelike pair |
| `bvt_F_swapCanonical_pairing_from_transposition_pointwise` | `OSToWightmanBoundaryValueLimits.lean` or `OSToWightmanBoundaryValuesComparison.lean` support layer | measure-preserving coordinate reindexing, support-zero outside `tsupport f`, `hswap`, and the arbitrary-transposition pointwise finite-shell theorem | the general `swap i j` canonical pairing equality required by the frontier theorem |
| `bvt_F_swapCanonical_pairing` | `OSToWightmanBoundaryValues.lean` | only the completed arbitrary-transposition pairing theorem | final private frontier theorem consumed by `bv_local_commutativity_transfer_of_swap_pairing` |

Two negative ownership rules are part of the route contract:

1. no slot below the final frontier theorem may consume global
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)`;
2. boundary-value recovery may identify the raw boundary distribution, but it
   may not be used as if it proved equality of finite canonical-shell integrals
   for each `ε > 0`;
3. once the finite-shell pointwise theorem is closed in the BHW-extension layer,
   the pairing and general-transposition layers may not reopen BHW geometry or
   EOW arguments;
4. do not assert
   `real_spacelike_swap_edge_mem_extendedTube_overlap` in absolute coordinates:
   one selected spacelike pair does not place the whole real n-point
   configuration, or its selected transposition, in the absolute extended tube.
   The selected-pair seam belongs to reduced/local edge-of-the-wedge geometry.

## 1. The live theorem and its consumers

The live frontier theorem is:

```lean
private theorem bvt_F_swapCanonical_pairing
```

in `OSToWightmanBoundaryValues.lean`.

Its immediate consumers are:

1. `bv_local_commutativity_transfer_of_swap_pairing`
   in `OSToWightmanBoundaryValuesComparison.lean`,
2. `bvt_locally_commutative`
   in `OSToWightmanBoundaryValues.lean`,
3. the public Wightman axiom field `locally_commutative` in
   `os_to_wightman_full`.

So theorem 2 is the unique boundary-value bridge from the analytic permutation
package to the public locality axiom.

## 2. OS-paper reading of theorem 2

OS I Section 4.5 proves locality by:

1. Euclidean symmetry on the real side,
2. analytic continuation to overlapping permuted tube domains,
3. a uniqueness / edge-of-the-wedge step,
4. passage to boundary values.

This means theorem 2 belongs to the BHW / PET / Jost / edge-of-the-wedge lane.
It is not part of the theorem-3 positivity / semigroup lane.

### 2.1. OS I error / OS II correction note

The OS I / OS II correction must be kept explicit here.  The theorem-2 locality
argument may use the already-repaired many-variable analytic object `bvt_F`, but
it must not revive the broken OS I Lemma 8.8 pattern as a hidden input.

The allowed reading of OS I Section 4.5 is conceptual:

1. Euclidean symmetry supplies equality on a real edge;
2. analytic continuation and edge-of-the-wedge propagate that equality;
3. boundary values transfer the equality to the reconstructed Wightman
   functional.

The disallowed reading is:

1. assume a separate one-variable continuation can be upgraded silently to the
   joint many-variable Fourier-Laplace statement;
2. use any theorem surface that effectively presupposes global Wightman
   locality of `bvt_W OS lgc`;
3. close theorem 2 by calling a theorem whose `hLC` input is exactly
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.

## 3. Exact production hooks already available

The current code already contains the major analytic ingredients.

In `OSToWightmanBoundaryValuesBase.lean`:

1. `bvt_F_perm`
   gives permutation invariance of the analytic boundary-value continuation
   `bvt_F`.

In `BHWExtension.lean`:

1. `W_analytic_swap_boundary_pairing_eq`
   gives adjacent-swap equality of boundary pairings for compactly supported
   tests whose real support already lies in the extended tube.  It is not
   directly callable on `W := bvt_W OS lgc` in theorem 2 unless the global
   locality hypothesis is supplied non-circularly.
2. `analytic_extended_local_commutativity`
   gives pointwise adjacent-swap equality on real ET overlap points for the BHW
   extension, again with a global `IsLocallyCommutativeWeak d W` input in the
   checked theorem surface.
3. `analytic_boundary_local_commutativity_of_boundary_continuous`
   descends that pointwise equality from `BHW.extendF W_analytic` to raw
   boundary values of `W_analytic`, provided the needed boundary continuity is
   available at the two real ET points.  This theorem has the same global
   locality input and therefore belongs to the checked supplier inventory, not
   to the non-circular theorem-2 endgame by itself.
4. `W_analytic_BHW`
   packages the BHW extension used by the reverse-direction side and by any
   later uniqueness comparison.

In `AnalyticContinuation.lean` and `SCV/TubeDomainExtension.lean`:

1. `edge_of_the_wedge`
   is a proved theorem, not an axiom.
2. `SCV.edge_of_the_wedge_theorem`
   is the underlying multi-dimensional theorem.
3. `jost_lemma`
   packages the real-point spacelike geometry on the extended tube.

In `OSToWightmanBoundaryValuesComparison.lean`:

1. `bv_local_commutativity_transfer_of_swap_pairing`
   is already the public transfer theorem from the canonical BV swap pairing to
   locality of the reconstructed Wightman distribution.

So theorem 2 does not lack edge-of-the-wedge infrastructure any more. The live
gap is the last boundary-pairing adapter that feeds the existing transfer
theorem.

## 4. Honest remaining gap

The current frontier theorem asks directly for equality of the two canonical BV
pairings

```lean
∫ bvt_F(... canonical shift ...) * g
=
∫ bvt_F(... canonical shift ...) * f
```

under:

1. selected-pair spacelike separation on the support of `f`,
2. `g = f ∘ swap(i,j)`.

Older drafts said that the BHW package already proves the analogous statement
once ET-support and boundary-continuity data are supplied.  That is not precise
enough for the current tree.  The checked BHW statements do provide the correct
shape, but their theorem surfaces still include

```lean
hLC : IsLocallyCommutativeWeak d W
```

or an equivalent local-commutativity input.  For `W := bvt_W OS lgc`, that
input is circular: theorem 2 is exactly the production step meant to prove
`IsLocallyCommutativeWeak d (bvt_W OS lgc)`.

So the remaining theorem-2 task is not "prove locality from scratch," but it is
also not "instantiate the existing BHW theorem."  The honest gap is:

1. identify the exact analytic representative behind `bvt_F`;
2. prove the Route-B real-open-edge / ET-support package for the selected
   transposition `Equiv.swap i j`;
3. prove the flattened regularity and boundary-continuity package for `bvt_F`;
4. build a non-circular raw-boundary or edge-compatibility theorem whose proof
   uses Euclidean symmetry, the open-edge/EOW machinery, and boundary
   continuity, but not global locality of `bvt_W OS lgc`;
5. prove the finite canonical-shell arbitrary-transposition interchange theorem
   for each `ε > 0`; this is not a boundary-value recovery statement;
6. prove the general `swap i j` pairing adapter directly from that pointwise
   theorem.

This is the key theorem-shape correction for the next Lean stage: any proof
that closes the frontier by supplying `bvt_locally_commutative` or
`IsLocallyCommutativeWeak d (bvt_W OS lgc)` as an input has merely introduced a
cycle, not proved theorem 2.

## 5. Exact theorem-slot inventory still needed

The documentation-standard theorem slots are:

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHWCore.ExtendedTube d n) := by
  -- primary Route-B geometry package; build above
  -- `exists_real_open_nhds_adjSwap`, not by asserting global ForwardJost
  -- membership from one adjacent spacelike pair

-- Do not generalize the previous theorem by replacing the adjacent pair with
-- arbitrary `i j` and keeping the absolute ET conclusion.  That statement is
-- too strong: one selected spacelike pair does not imply absolute ET
-- membership for the whole real configuration.  The public `swap i j` theorem
-- must pass through the reduced finite-shell package below instead.

def bvt_F_reduced
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) : ReducedNPointConfig d m → ℂ :=
  fun η => bvt_F OS lgc (m + 1) (BHW.safeSection d m η)

theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    ∀ z : Fin (m + 1) → Fin (d + 1) → ℂ,
      bvt_F OS lgc (m + 1) z =
        bvt_F_reduced (d := d) OS lgc m
          (BHW.reducedDiffMap (m + 1) d z) := by
  -- global translation invariance of `bvt_F` plus the identity
  -- `safeSection (reducedDiffMap z) + constant = z`.

lemma swapped_support_lies_in_swapped_open_edge
    {V : Set (NPointDomain d n)}
    (f g : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V} := by
  -- pure support transport through the checked swap identity

lemma swapped_support_lies_in_swapped_open_edge_for_swap
    {V : Set (NPointDomain d n)}
    (f g : SchwartzNPoint d n) (i j : Fin n)
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap i j k)))
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | (fun k => x (Equiv.swap i j k)) ∈ V} := by
  -- same pure support transport, now for the selected public transposition

lemma bvt_F_boundary_continuous_at_real_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ x,
      ContinuousWithinAt
        (bvt_F OS lgc n)
        (ForwardTube d n)
        (fun k μ => (x k μ : ℂ)) := by
  -- boundary continuity of the analytic representative at the real support

lemma adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (f x) := by
  -- non-circular adjacent-only raw-boundary theorem.
  -- It may use Euclidean symmetry, EOW/uniqueness, open-edge ET data, and
  -- boundary continuity. It may not consume
  -- `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.

theorem bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (f x) := by
  -- theorem-2-facing wrapper around
  -- `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
```

The last theorem is still adjacent-only and raw-boundary-only.  The public
frontier theorem is a general transposition on the canonical imaginary cone
shift, so the downstream work is finite-shell work, not raw boundary recovery:

```lean
def canonicalShell
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def swappedCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def permutedEtaCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) +
      ε *
        ↑(canonicalForwardConeDirection
          (d := d) n (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) *
        Complex.I

lemma swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    swappedCanonicalShell (d := d) n i hi x ε =
      fun k μ =>
        permutedEtaCanonicalShell (d := d) n i hi x ε
          (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ := by
  -- ext k μ
  -- simp [swappedCanonicalShell, permutedEtaCanonicalShell, Equiv.swap_apply_self]

theorem bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) (hε : 0 < ε)
    (hsp : MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    bvt_F OS lgc n (permutedEtaCanonicalShell (d := d) n i hi x ε) =
    bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- finite-shell EOW/BHW comparison.  This is the analytic step:
  -- the two shells have the same real edge but approach it through
  -- adjacent-swapped imaginary directions.

theorem bvt_F_adjacentSwapCanonical_pointwise_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) (hε : 0 < ε)
    (hsp : MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    bvt_F OS lgc n (swappedCanonicalShell (d := d) n i hi x ε) =
    bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- Step 1: rewrite `swappedCanonicalShell` as the real-coordinate permutation
  -- of `permutedEtaCanonicalShell`.
  -- Step 2: use `bvt_F_perm` to remove that real-coordinate permutation.
  -- Step 3: apply
  -- `bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike`.
  --
  -- This finite-shell theorem is the real canonical theorem-2 bridge and is
  -- not supplied by boundary-value recovery.

theorem bvt_F_adjacentSwapCanonical_pairing_from_pointwise
    ...
```

Only after the finite-shell adjacent theorem is in place should the later file
prove the explicit reducer for a general `swap i j`.

### 5.1. Legacy/fallback strategy for the boundary-continuity slot

This subsection is retained only for the older raw-boundary / finite-height
fallback route.  It is **not** the primary OS-I theorem-2 route after the
real-Jost `extendF` correction above.  A global raw real-trace continuity theorem
for `bvt_F` is stronger than the distributional Wightman boundary-value
statement and must not be smuggled into the primary proof.

If the fallback route is deliberately retained, the continuity theorem above
should not remain a bare placeholder. There is a concrete candidate route in the
repo:

1. `ForwardTubeDistributions.lean :: boundary_function_continuous_forwardTube_of_flatRegular`
   proves continuity of the real trace of a forward-tube holomorphic function,
   provided one has a regular flattened Fourier-Laplace package
   `SCV.HasFourierLaplaceReprRegular`.
2. The later theorem-2 implementation should therefore aim first for a regular
   flattened package for `bvt_F OS lgc n`, not for pointwise continuity by raw
   epsilon-delta arguments.

For that fallback route, the theorem-slot inventory would be:

```lean
lemma bvt_F_flattened_holomorphic
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    HolomorphicOn
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.tubeDomain (ForwardConeFlat d n))

lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap)

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma flatRegular_of_boundary_distribution_and_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  exact
    flatRegular_of_boundary_distribution_and_polyGrowth
      (d := d) OS lgc n

lemma bvt_F_boundary_continuous_on_real_trace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    Continuous (fun x : NPointDomain d n => bvt_F OS lgc n (fun k μ => (x k μ : ℂ))) := by
  exact
    boundary_function_continuous_forwardTube_of_flatRegular
      (d := d) (n := n)
      (bvt_F_holomorphic OS lgc n)
      (bvt_F_hasFlatRegularRepr (d := d) OS lgc n)

lemma bvt_F_boundary_continuous_at_real_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ x,
      ContinuousWithinAt
        (bvt_F OS lgc n)
        (ForwardTube d n)
        (fun k μ => (x k μ : ℂ)) := by
  -- derive `ContinuousWithinAt` from the global real-trace continuity theorem,
  -- together with the forward-tube approach geometry at real points
```

This is a possible fallback route because it uses already-proved transport
results in `ForwardTubeDistributions.lean` rather than inventing a new local
boundary continuity argument.  It is not the current primary theorem-2 route.

If `bvt_F_hasFlatRegularRepr` turns out not to be obtainable from the current
production growth package, then that regular package is only the honest blocker
for the fallback raw-boundary route.  The primary route should instead continue
through `bvt_F_distributionalEOW_permBranch_from_euclideanEdge` and
`bvt_F_hasPermutationEdgeDistributionEquality`.

The key documentation correction is:

1. there is no current repo theorem named
   `SCV.hasFourierLaplaceReprRegular_of_boundary_and_growth`,
2. the actual missing theorem package is the constructor
   `flatRegular_of_boundary_distribution_and_polyGrowth`,
3. the later locality proof should therefore treat the regular constructor as
   the hard analytic input and the continuity theorem as a downstream consumer.

### 5.2. Fallback subpackages behind `bvt_F_hasFlatRegularRepr`

If the fallback raw-boundary route is revived, the regular flattened package
should itself be documented as a small theorem suite, not as one unexplained
miracle theorem.

The later Lean port should split it into:

```lean
lemma bvt_F_flattened_holomorphic
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    HolomorphicOn
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.tubeDomain (ForwardConeFlat d n)) := by
  -- transport `bvt_F_holomorphic` through the flattening equivalence

lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap) := by
  -- flattened form of the existing boundary-value package for `bvt_F`

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  -- transport the current growth package for `bvt_F`

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  exact
    flatRegular_of_boundary_distribution_and_polyGrowth
      (d := d) OS lgc n
```

This is the correct level of explicitness for the fallback continuity theorem
because the `ForwardTubeDistributions` package already proves the final
transport theorems.  It is not a prerequisite for the primary OS/Jost
distributional route.

The constructor theorem should be read as an actual future file target:

1. prove the flattened holomorphic theorem,
2. prove the flattened boundary-distribution theorem,
3. prove the flattened polynomial-growth theorem,
4. combine those three inputs in a new SCV/forward-tube regularity constructor,
5. only then specialize to `bvt_F_hasFlatRegularRepr`.

### 5.3. Exact route from continuity to the raw-boundary swap pairing

Once the regular flattened package is in place, the later proof should not jump
straight to the canonical shifted pairing. There is an intermediate raw-boundary
theorem surface:

```lean
theorem bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * g x
        =
      ∫ x, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * f x := by
  intro f g hf_compact hg_compact hsep hswap
  obtain ⟨V, hV_open, hf_support, hV_ET, hV_swapET⟩ :=
    choose_real_open_edge_for_adjacent_swap (d := d) (n := n) f i hi hsep
  have hg_support :=
    swapped_support_lies_in_swapped_open_edge
      (d := d) (n := n) (V := V) f g i hi hswap hf_support
  have hcont := bvt_F_boundary_continuous_at_real_support (d := d) OS lgc n
  exact
    adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility
      (d := d) (OS := OS) (lgc := lgc) n i hi f g
      hf_compact hg_compact hsep hswap
      -- the proof package supplies ET data from `hV_ET`, `hV_swapET`,
      -- `hf_support`, and `hg_support`, plus continuity from `hcont`.
```

Only after this raw-boundary theorem is in place should the later file prove
the canonical-shift adapter. That final adapter should be documented as a
separate wrapper theorem because it changes the evaluation surface from
`x ↦ x` to `x ↦ x + i ε η_can`, and that change is not part of the BHW
locality theorem itself.

### 5.4. Correct support geometry boundary

The adjacent support-to-ET package remains useful as a pilot and as context for
raw-boundary locality statements, but it is **not** the public finite-shell
transposition route.  A single selected spacelike pair does not imply that the
whole real configuration, or its selected transposition, is already in the
absolute BHW extended-tube overlap.

The adjacent pilot package therefore has these implementation targets only:

```lean
lemma choose_real_open_edge_for_adjacent_swap
lemma swapped_support_lies_in_swapped_open_edge
lemma swapped_open_edge_embeds_in_extendedTube
```

The public `swap i j` finite-shell theorem must instead pass through reduced
difference coordinates:

```lean
def bvt_F_reduced
theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
theorem reducedPairDiff_reducedDiffMapReal
theorem bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike
theorem bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike
```

`ComplexLieGroups/JostPoints.lean` remains fallback context only.  In
particular, a theorem named like
`canonical_support_mem_forwardJost_of_swap_spacelike` is not part of the
primary theorem-2 execution transcript unless it is separately proved and
recorded as a genuine geometric strengthening.  Likewise, do not introduce a
general `choose_real_open_edge_for_swap` theorem unless its statement has a new
mathematical hypothesis strong enough to imply full extended-tube membership.

### 5.5. Lean-style endgame script with all remaining theorem slots visible

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * g x
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
  intro n i j f g ε hε hsep hswap
  exact
    bvt_F_swapCanonical_pairing_from_transposition_pointwise
      (d := d) (OS := OS) (lgc := lgc) n i j f g ε hε hsep hswap
```

This is the closure standard the docs should now enforce:

1. ET support geometry named for the selected transposition,
2. boundary continuity package named,
3. non-circular raw-boundary theorem named,
4. finite-shell permuted-eta comparison named,
5. general transposition pairing adapter named.

If any one of those five is missing in a later Lean proof, then theorem 2 is
still underdocumented.

General-swap warning: any theorem named like
`bvt_F_swapCanonical_pairing_of_adjacent_chain` is not a license to bubble one
field past arbitrary intervening fields.  The live
hypothesis for `swap i j` only says that the original `i`-th and `j`-th
arguments are spacelike separated; it says nothing about the intervening
neighbors in a naive adjacent-transposition decomposition.  Therefore any
general-swap reducer is implementation-ready only after it has one of the
following exact proofs, with the direct transposition theorem as the preferred
route:

1. a direct finite-shell theorem for an arbitrary transposition `swap i j`;
2. a relabeling theorem that moves the selected pair to an adjacent pair,
   applies the adjacent theorem to that same spacelike pair, and moves back
   without changing the canonical shell statement;
3. an adjacent-chain proof whose step predicate explicitly proves that each
   adjacent step is swapping the same spacelike pair under a tracked relabeling,
   not an unrelated neighbor.

Until the direct transposition theorem or a fully tracked relabeling theorem is
written, the general-swap layer remains a proof-doc gap.

## 6. Canonical-shift adapter required by the frontier theorem

The consumer
`bv_local_commutativity_transfer_of_swap_pairing`
expects the canonical shifted pairing, not the raw real-support pairing.

Important correction: this finite-`ε` canonical shifted pairing is not obtained
by `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`.  That recovery
theorem identifies the boundary distribution/raw boundary value after taking
the boundary limit; it does not state that

```lean
∫ F(x + i ε η_can) f x = W f
```

for each fixed `ε > 0`.  The live theorem needs equality before the
`ε → 0+` limit is taken, so the canonical layer must be a finite-shell
interchange theorem.

The adjacent finite-shell package should be factored into two algebraic moves
and one analytic move.  This is important because the canonical imaginary
direction is not invariant under coordinate swaps:

1. rewrite the left shell, after changing integration variables, as a real
   coordinate permutation of a shell with the **permuted** imaginary direction;
2. use `bvt_F_perm` to remove that real coordinate permutation;
3. prove the true EOW/BHW finite-shell comparison between the permuted-eta
   shell and the canonical shell.

The implementation-ready theorem skeleton is:

```lean
def canonicalShell
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def swappedCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def permutedEtaCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) +
      ε *
        ↑(canonicalForwardConeDirection
          (d := d) n (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) *
        Complex.I

lemma swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    swappedCanonicalShell (d := d) n i hi x ε =
      fun k μ =>
        permutedEtaCanonicalShell (d := d) n i hi x ε
          (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ := by
  ext k μ
  simp [swappedCanonicalShell, permutedEtaCanonicalShell, Equiv.swap_apply_self]

theorem bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩) →
      bvt_F OS lgc n (permutedEtaCanonicalShell (d := d) n i hi x ε) =
      bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- True finite-shell EOW/BHW comparison.
  -- The two configurations have the same real edge `x`, but the imaginary
  -- direction on the left is adjacent-swapped.  This is where
  -- `canonical_adjacentSwap_shell_mem_EOW_domain`, holomorphy, boundary
  -- continuity, and uniqueness/edge-of-the-wedge are consumed.

theorem bvt_F_adjacentSwapCanonical_pointwise_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩) →
      bvt_F OS lgc n
        (fun k μ =>
          ↑(x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)
      =
      bvt_F OS lgc n
        (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) := by
  -- rewrite by `swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell`;
  -- use `bvt_F_perm` to remove the real-coordinate permutation;
  -- apply
  -- `bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike`.

theorem bvt_F_adjacentSwapCanonical_pairing_from_pointwise
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- rewrite `g` by `hswap`, change variables by the adjacent coordinate
  -- permutation, and use the pointwise finite-shell theorem on `tsupport f`;
  -- outside `tsupport f`, the integrand is zero.
```

At the current repo state, the finite-shell pointwise theorem is now isolated
as the permuted-eta comparison above, but its analytic proof transcript is not
yet complete enough for production Lean.  This remains the honest theorem-2
blocker after the first doc pass.

### 6.1. General transposition adapter, not an adjacent bubble-sort

The public frontier theorem is not adjacent-only.  Its hypothesis is:

```lean
∀ x, f.toFun x ≠ 0 →
  MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)
```

for the same selected pair `i, j` that appears in `Equiv.swap i j`.  Therefore
the final closure should use an arbitrary-transposition finite-shell theorem.
The adjacent theorem above is useful as a pilot and as the `j = i + 1` special
case, but a naive adjacent-chain decomposition is not a valid final reducer.

The general shell definitions should be:

```lean
def swappedCanonicalShellOfPerm
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x (σ k) μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def permutedEtaCanonicalShellOfPerm
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n (σ k) μ) * Complex.I

lemma swappedCanonicalShellOfPerm_eq_perm_permutedEtaCanonicalShellOfPerm
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) (ε : ℝ)
    (hσ_inv : σ * σ = 1) :
    swappedCanonicalShellOfPerm (d := d) n σ x ε =
      fun k μ =>
        permutedEtaCanonicalShellOfPerm (d := d) n σ x ε (σ k) μ := by
  ext k μ
  have hσσ : σ (σ k) = k := by
    simpa [Equiv.Perm.mul_apply] using congr_fun hσ_inv k
  simp [swappedCanonicalShellOfPerm, permutedEtaCanonicalShellOfPerm, hσσ]
```

For the live theorem, `σ = Equiv.swap i j`, so `hσ_inv` is just
`Equiv.swap_mul_self` / `Equiv.swap_apply_self` bookkeeping.  The theorem
shape that should replace the old adjacent-chain reducer is:

```lean
theorem bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) →
      bvt_F OS lgc n
        (permutedEtaCanonicalShellOfPerm
          (d := d) n (Equiv.swap i j) x ε)
      =
      bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- arbitrary-transposition finite-shell EOW comparison.
  -- This is the non-adjacent analogue of the permuted-eta theorem above.
  -- It must not be proved by swapping unrelated adjacent neighbors.

theorem bvt_F_swapCanonical_pointwise_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) →
      bvt_F OS lgc n
        (swappedCanonicalShellOfPerm
          (d := d) n (Equiv.swap i j) x ε)
      =
      bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- rewrite the swapped shell through the permuted-eta shell;
  -- apply `bvt_F_perm` with `σ := Equiv.swap i j`;
  -- apply
  -- `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike`.

theorem bvt_F_swapCanonical_pairing_from_transposition_pointwise
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n)
      (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (f x) := by
  -- rewrite `g` using `hswap`;
  -- change variables by `Equiv.swap i j` on `NPointDomain`;
  -- the left shell becomes `swappedCanonicalShellOfPerm (Equiv.swap i j)`;
  -- use the pointwise theorem wherever `f x ≠ 0`;
  -- outside that support, both integrands vanish because of the `f x` factor.
```

This is the implementation target for the final frontier theorem.  A theorem
named `bvt_F_swapCanonical_pairing_of_adjacent_chain` should either be removed
from the production plan or renamed to a genuinely tracked relabeling theorem.
It must not mean "bubble-sort the swap through arbitrary adjacent neighbors."

### 6.2. Corrected reduced-coordinate finite-shell route

The attempted absolute theorem

```lean
real_spacelike_swap_edge_mem_extendedTube_overlap
```

must not be used.  It would say that a single selected spacelike pair forces
both `realEmbed x` and `realEmbed (x ∘ Equiv.swap i j)` into the absolute
extended tube.  That is too strong: absolute `ExtendedTube d n` is controlled by
the full successive-difference/Jost geometry, while the theorem-2 hypothesis
only controls one selected pair.

The public transposition theorem should instead reduce the finite canonical
shell to the reduced difference-coordinate seam.  The Lean packet should be:

```lean
def canonicalReducedDirection (m : ℕ) :
    Fin m → Fin (d + 1) → ℝ :=
  fun _ μ => BHW.safeBasepointVec d μ

def canonicalReducedDirectionC (m : ℕ) : ReducedNPointConfig d m :=
  fun k μ => (canonicalReducedDirection (d := d) m k μ : ℂ)

def permutedCanonicalReducedDirectionC
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) : ReducedNPointConfig d m :=
  BHW.permOnReducedDiff (d := d) (n := m + 1) σ
    (canonicalReducedDirectionC (d := d) m)

def reducedPairDiff
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) : Fin (d + 1) → ℝ :=
  fun μ =>
    ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 ξ) j μ) -
      ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 ξ) i μ)

theorem reducedPairDiff_reducedDiffMapReal
    (m : ℕ) (i j : Fin (m + 1)) (x : NPointDomain d (m + 1)) :
    reducedPairDiff (d := d) m i j
        (BHW.reducedDiffMapReal (m + 1) d x)
      =
      fun μ => x j μ - x i μ := by
  -- use `reducedDiffSection_reducedDiffMap_eq_sub_basepoint` or the real
  -- `realDiffCoordCLE`/`prependBasepointReal` identities; translations cancel.

theorem canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC
    (m : ℕ) :
    BHW.reducedDiffMap (m + 1) d
        (fun k μ => (canonicalForwardConeDirection (d := d) (m + 1) k μ : ℂ))
      =
      canonicalReducedDirectionC (d := d) m := by
  -- consecutive time labels differ by `1`, spatial labels differ by `0`.

theorem permutedCanonicalForwardDirection_reducedDiff_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    BHW.reducedDiffMap (m + 1) d
        (fun k μ => (canonicalForwardConeDirection (d := d) (m + 1) (σ k) μ : ℂ))
      =
      permutedCanonicalReducedDirectionC (d := d) m σ := by
  -- apply `permOnReducedDiff_reducedDiffMap` to the absolute canonical
  -- direction, then use
  -- `canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC`.

theorem reducedDiffMap_canonicalShell_eq
    (m : ℕ) (x : NPointDomain d (m + 1)) (ε : ℝ) :
    BHW.reducedDiffMap (m + 1) d
        (canonicalShell (d := d) (m + 1) x ε)
      =
      fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
          ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
  -- linearity of `reducedDiffMap` plus
  -- `canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC`.

theorem reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (x : NPointDomain d (m + 1)) (ε : ℝ) :
    BHW.reducedDiffMap (m + 1) d
        (permutedEtaCanonicalShellOfPerm (d := d) (m + 1) σ x ε)
      =
      fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
          ε * permutedCanonicalReducedDirectionC (d := d) m σ k μ * Complex.I := by
  -- linearity of `reducedDiffMap` plus
  -- `permutedCanonicalForwardDirection_reducedDiff_eq`.

def bvt_F_reduced
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) : ReducedNPointConfig d m → ℂ :=
  fun η => bvt_F OS lgc (m + 1) (BHW.safeSection d m η)

theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    ∀ z : Fin (m + 1) → Fin (d + 1) → ℂ,
      bvt_F OS lgc (m + 1) z =
        bvt_F_reduced (d := d) OS lgc m
          (BHW.reducedDiffMap (m + 1) d z) := by
  -- `safeSection (reducedDiffMap z)` differs from `z` by a uniform
  -- translation; apply `bvt_F_translationInvariant`.

theorem bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (m : ℕ) (i j : Fin (m + 1))
      (ξ : NPointDomain d m) (ε : ℝ), 0 < ε →
      MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) →
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)
      =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  -- This is the corrected hard analytic theorem. It is a reduced local
  -- edge-of-the-wedge statement at the selected pair. It replaces the false
  -- absolute ET-overlap claim.
```

This theorem should not be implemented monolithically.  Split off the purely
algebraic reduced-permutation part first.

```lean
theorem bvt_F_reduced_permOnReducedDiff
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ζ : ReducedNPointConfig d m) :
    bvt_F_reduced (d := d) OS lgc m
      (BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ)
    =
    bvt_F_reduced (d := d) OS lgc m ζ := by
  -- Let `zσ k := safeSection d m ζ (σ k)`.
  -- `permOnReducedDiff_reducedDiffMap` and `reducedDiffMap_safeSection`
  -- identify the reduced coordinates of `zσ`.
  -- `safeSection (permOnReducedDiff σ ζ)` and `zσ` therefore differ by a
  -- uniform complex translation; use
  -- `exists_uniformShift_eq_of_reducedDiffMap_eq` and
  -- `bvt_F_translationInvariant`.
  -- Finally use `bvt_F_perm` on `safeSection d m ζ`.

theorem permOnReducedDiff_swap_permutedCanonicalDirection
    (m : ℕ) (i j : Fin (m + 1)) :
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
      (permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j))
    =
    canonicalReducedDirectionC (d := d) m := by
  -- `permutedCanonicalReducedDirectionC` is
  -- `permOnReducedDiff (Equiv.swap i j) canonicalReducedDirectionC`;
  -- use `permOnReducedDiff_mul` and `(Equiv.swap i j) * (Equiv.swap i j) = 1`.

theorem bvt_F_reduced_permutedDirection_to_realPermutedCanonical
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) (ε : ℝ) :
    bvt_F_reduced (d := d) OS lgc m
      (fun k μ =>
        (ξ k μ : ℂ) +
          ε *
            permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
            Complex.I)
    =
    bvt_F_reduced (d := d) OS lgc m
      (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)) := by
  -- Symmetry of `bvt_F_reduced_permOnReducedDiff`.
```

After expanding the linear map in the last target and applying
`permOnReducedDiff_swap_permutedCanonicalDirection`, the hard theorem can be
rephrased in the cleaner canonical-direction form:

```lean
theorem bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (m : ℕ) (i j : Fin (m + 1))
      (ξ : NPointDomain d m) (ε : ℝ), 0 < ε →
      MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) →
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
                Complex.I))
      =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  -- After linearity and the previous direction lemma, this is the statement
  -- that the canonical-direction forward-tube value is unchanged when the
  -- real reduced basepoint is acted on by the selected transposition.
  -- This is the remaining local EOW/BHW seam.
```

The original
`bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike` should
then be a short adapter:

1. rewrite the left side by
   `bvt_F_reduced_permutedDirection_to_realPermutedCanonical`;
2. simplify the permuted direction by
   `permOnReducedDiff_swap_permutedCanonicalDirection`;
3. apply
   `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike`.

Do not use `BHW.reduced_bargmann_hall_wightman_of_input` to close this seam for
`bvt_F OS lgc`: that axiom takes a `WightmanFunctions d` input and therefore
belongs on the already-reconstructed side, where locality is part of the
structure.  The theorem-2 proof needs the OS-side `bvt_F` route, not a
post-locality Wightman bundle.

The canonical-real-swap theorem has its own proof obligations.  These are not
algebraic wrappers; they are the reduced version of the local BHW/EOW argument.

```lean
def reducedSpacelikeSwapEdge
    (m : ℕ) (i j : Fin (m + 1)) : Set (NPointDomain d m) :=
  {ξ | MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ)}

theorem isOpen_reducedSpacelikeSwapEdge
    (m : ℕ) (i j : Fin (m + 1)) :
    IsOpen (reducedSpacelikeSwapEdge (d := d) m i j) := by
  -- continuity of `reducedPairDiff` plus openness of the spacelike cone.

theorem bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    ∀ ξ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ => (ξ k μ : ℂ)))
      =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ => (ξ k μ : ℂ)) := by
  -- This boundary equality is algebraic: use
  -- `bvt_F_reduced_permOnReducedDiff`.

theorem bvt_F_reduced_holomorphicOn_reducedForwardTube
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    DifferentiableOn ℂ (bvt_F_reduced (d := d) OS lgc m)
      (BHW.ReducedForwardTubeN d m) := by
  -- compose `bvt_F_holomorphic` with `safeSection`; use
  -- `safeSection_mem_forwardTube`.

theorem bvt_F_reduced_holomorphicOn_swapPulledForwardTube
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    DifferentiableOn ℂ
      (fun ζ =>
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ))
      {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
        BHW.ReducedForwardTubeN d m} := by
  -- compose the previous holomorphicity theorem with the continuous linear map
  -- `permOnReducedDiff`.
```

The missing analytic theorem is then:

```lean
theorem reduced_local_EOW_canonicalRealSwap
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    ∀ ξ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
      ∀ ε : ℝ, 0 < ε →
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I))
        =
        bvt_F_reduced (d := d) OS lgc m
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  -- This is the true local EOW/BHW content.
  -- Inputs:
  -- 1. the two holomorphic tube branches above;
  -- 2. boundary equality on `reducedSpacelikeSwapEdge`;
  -- 3. a reduced two-cone edge-of-the-wedge / BHW continuation theorem for the
  --    cones `ReducedForwardTubeN d m` and its selected-swap pullback;
  -- 4. geometry showing the two finite shell points lie in the connected
  --    reduced EOW envelope generated by that edge.
```

This last theorem is the one remaining proof-doc gap.  The algebraic reduced
packet is ready to implement, but the production proof of theorem 2 is not
fully ready until `reduced_local_EOW_canonicalRealSwap` is expanded into a
Lean-level proof from existing SCV/BHW surfaces or into a new, non-QFT-specific
SCV theorem with a proof.

The current SCV surface must be used honestly here.  The checked theorem

```lean
SCV.edge_of_the_wedge_theorem
```

is an opposite-cone theorem for `TubeDomain C` and
`TubeDomain (Neg.neg '' C)`.  The selected-swap reduced branch naturally lives
over the pullback cone

```lean
{ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
  BHW.ReducedForwardTubeN d m}
```

which is not automatically `Neg.neg '' ReducedForwardTubeN d m`.  Therefore
the opposite-cone EOW theorem does not directly close the selected-swap seam.

There is also an endpoint issue that the proof docs must not hide.  After the
reduced permutation algebra, the genuinely hard finite-height endpoints are

```lean
def canonicalReducedShell
    (m : ℕ) (ξ : NPointDomain d m) (ε : ℝ) :
    ReducedNPointConfig d m :=
  fun k μ => (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I

def realPermutedCanonicalReducedShell
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ) :
    ReducedNPointConfig d m :=
  fun k μ =>
    (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
      (fun k μ => (ξ k μ : ℂ))) k μ
      + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I
```

and the target equality is

```lean
bvt_F_reduced (d := d) OS lgc m
  (realPermutedCanonicalReducedShell (d := d) m i j ξ ε)
=
bvt_F_reduced (d := d) OS lgc m
  (canonicalReducedShell (d := d) m ξ ε)
```

Equivalently, the left endpoint is the existing theorem statement after
expanding linearity of `permOnReducedDiff` and using
`permOnReducedDiff_swap_permutedCanonicalDirection`.  A one-variable slice that
only compares upper and lower half-planes over the same real point does not by
itself compare these two endpoints, because the real reduced basepoint has
also changed from `ξ` to `permOnReducedDiff swap ξ`.

So the next proof-doc task is one of the following, in this order of
preference:

1. prove a concrete linear-slice reduction showing that the selected
   canonical-real-swap comparison really hits both finite-height endpoints
   above and only needs an opposite-cone EOW in the one-dimensional normal
   direction to the spacelike pair;
2. otherwise prove a general two-cone EOW transport theorem in `SCV` for two
   open convex cones `C₁`, `C₂` with common real edge and a connected local
   envelope;
3. only after one of those SCV bridges exists, instantiate it for
   `ReducedForwardTubeN d m` and the selected-swap pullback cone.

Do not treat the existing opposite-cone theorem as if it directly applies to
the selected-swap cone without this reduction.

Do not treat the existing adjacent-swap EOW helpers as this bridge either.
The checked `eow_adj_swap_extension_holo_only` only places two holomorphic
branches on a union of forward-tube pieces and does not prove a connected EOW
continuation.  The checked `eow_adj_swap_on_overlap` only applies on the actual
overlap of a forward tube with its swapped copy; in the nontrivial selected
swap situation, that overlap is not the finite-height bridge required here.

The first required geometry input is therefore the connected-envelope theorem
below.  This is not enough by itself, but it records the domain membership and
connectedness that any later symmetry transport must consume.

```lean
theorem reduced_canonicalRealSwap_sameEnvelope
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (ReducedNPointConfig d m),
      IsOpen U ∧ IsPreconnected U ∧
      canonicalReducedShell (d := d) m ξ ε ∈ U ∧
      realPermutedCanonicalReducedShell (d := d) m i j ξ ε ∈ U ∧
      U ⊆
        (BHW.ReducedForwardTubeN d m) ∪
        {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
          BHW.ReducedForwardTubeN d m} ∪
        {ζ | ∃ ξ₀ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
          ζ = fun k μ => (ξ₀ k μ : ℂ)} := by
  -- Geometry of the reduced selected-pair BHW/EOW envelope.  This theorem
  -- must include the endpoint membership and connectedness needed by analytic
  -- continuation; it must not be replaced by a disconnected union statement.
```

The previous connected-envelope theorem is therefore only a geometry input, not
the analytic transport theorem.  A correct transport theorem must include a
symmetry or reflection map on the envelope and must use a real-edge identity
theorem.  The existing production theorem

```lean
SCV.identity_theorem_totally_real_product
```

is the right identity-theorem surface for this last propagation step.  The
Lean-facing transport theorem should have the following shape:

```lean
theorem reduced_connectedEnvelope_symmetry_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) (ε : ℝ)
    (U : Set (ReducedNPointConfig d m))
    (Fext : ReducedNPointConfig d m → ℂ)
    (R : ReducedNPointConfig d m → ReducedNPointConfig d m)
    (V : Set (NPointDomain d m))
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hFext_holo : DifferentiableOn ℂ Fext U)
    (hR_holo : DifferentiableOn ℂ R U)
    (hR_maps : ∀ z ∈ U, R z ∈ U)
    (hVopen : IsOpen V) (hVnonempty : V.Nonempty)
    (hVedge : V ⊆ reducedSpacelikeSwapEdge (d := d) m i j)
    (hVsubU : ∀ ξ₀ ∈ V, (fun k μ => (ξ₀ k μ : ℂ)) ∈ U)
    (hR_edge_symm :
      ∀ ξ₀ ∈ V,
        Fext (R (fun k μ => (ξ₀ k μ : ℂ))) =
        Fext (fun k μ => (ξ₀ k μ : ℂ)))
    (hR_endpoint :
      R (canonicalReducedShell (d := d) m ξ ε) =
        realPermutedCanonicalReducedShell (d := d) m i j ξ ε)
    (hcanonical_mem : canonicalReducedShell (d := d) m ξ ε ∈ U)
    (hcanonical_agree :
      Fext (canonicalReducedShell (d := d) m ξ ε) =
        bvt_F_reduced (d := d) OS lgc m
          (canonicalReducedShell (d := d) m ξ ε))
    (hrealPermuted_agree :
      Fext (realPermutedCanonicalReducedShell (d := d) m i j ξ ε) =
        bvt_F_reduced (d := d) OS lgc m
          (realPermutedCanonicalReducedShell (d := d) m i j ξ ε)) :
    bvt_F_reduced (d := d) OS lgc m
      (realPermutedCanonicalReducedShell (d := d) m i j ξ ε)
    =
    bvt_F_reduced (d := d) OS lgc m
      (canonicalReducedShell (d := d) m ξ ε) := by
  -- Apply `SCV.identity_theorem_totally_real_product` to
  -- `fun z => Fext (R z) - Fext z` on `U`.
  -- The real-open set is `V`; `hR_edge_symm` is supplied by the reduced
  -- boundary permutation equality.  Evaluate the resulting equality at
  -- `canonicalReducedShell`, rewrite with `hR_endpoint`, then use the two
  -- branch-agreement hypotheses.
```

Thus the real missing analytic/geometric theorem is not merely
`reduced_canonicalRealSwap_sameEnvelope`; it is the construction of a package

```lean
theorem exists_reduced_canonicalRealSwap_symmetricEnvelope
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (U : Set (ReducedNPointConfig d m))
      (Fext : ReducedNPointConfig d m → ℂ)
      (R : ReducedNPointConfig d m → ReducedNPointConfig d m)
      (V : Set (NPointDomain d m)),
      IsOpen U ∧ IsConnected U ∧
      DifferentiableOn ℂ Fext U ∧
      DifferentiableOn ℂ R U ∧
      (∀ z ∈ U, R z ∈ U) ∧
      IsOpen V ∧ V.Nonempty ∧
      V ⊆ reducedSpacelikeSwapEdge (d := d) m i j ∧
      (∀ ξ₀ ∈ V, (fun k μ => (ξ₀ k μ : ℂ)) ∈ U) ∧
      (∀ ξ₀ ∈ V,
        Fext (R (fun k μ => (ξ₀ k μ : ℂ))) =
        Fext (fun k μ => (ξ₀ k μ : ℂ))) ∧
      R (canonicalReducedShell (d := d) m ξ ε) =
        realPermutedCanonicalReducedShell (d := d) m i j ξ ε ∧
      canonicalReducedShell (d := d) m ξ ε ∈ U ∧
      Fext (canonicalReducedShell (d := d) m ξ ε) =
        bvt_F_reduced (d := d) OS lgc m
          (canonicalReducedShell (d := d) m ξ ε) ∧
      Fext (realPermutedCanonicalReducedShell (d := d) m i j ξ ε) =
        bvt_F_reduced (d := d) OS lgc m
          (realPermutedCanonicalReducedShell (d := d) m i j ξ ε) := by
  -- This package is the precise current proof-doc gap.  It must construct the
  -- connected EOW/BHW envelope, the continuation `Fext`, and the endpoint
  -- symmetry map `R`.  The old disconnected `FT ∪ σFT` helper does not provide
  -- these data.
```

The construction of `R` is now the named mathematical gap.  The next proof-doc
stage should not try to implement this theorem until the following subpacket is
made explicit:

```lean
def selectedSwapEnvelopeSymmetry
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ) :
    ReducedNPointConfig d m → ReducedNPointConfig d m :=
  -- To be a valid production definition, this must be an explicit affine or
  -- complex-linear map coming from the reduced BHW/Lorentz geometry, not an
  -- arbitrary function chosen only to hit the endpoint.

theorem selectedSwapEnvelopeSymmetry_maps_envelope
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) (U : Set (ReducedNPointConfig d m)) :
    ∀ z ∈ U,
      selectedSwapEnvelopeSymmetry (d := d) m i j ξ ε z ∈ U := by
  -- invariance of the constructed envelope under the selected-swap symmetry.

theorem selectedSwapEnvelopeSymmetry_holomorphic
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ)
    (U : Set (ReducedNPointConfig d m)) :
    DifferentiableOn ℂ
      (selectedSwapEnvelopeSymmetry (d := d) m i j ξ ε) U := by
  -- affine/linear maps are holomorphic; this should be a short proof once the
  -- definition is explicit.

theorem selectedSwapEnvelopeSymmetry_endpoint
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ) :
    selectedSwapEnvelopeSymmetry (d := d) m i j ξ ε
      (canonicalReducedShell (d := d) m ξ ε)
    =
      realPermutedCanonicalReducedShell (d := d) m i j ξ ε := by
  -- endpoint calculation; this is where the exact formula for `R` is checked.

theorem selectedSwapEnvelopeSymmetry_real_edge_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ)
    (Fext : ReducedNPointConfig d m → ℂ)
    (V : Set (NPointDomain d m)) :
    ∀ ξ₀ ∈ V,
      Fext
        (selectedSwapEnvelopeSymmetry (d := d) m i j ξ ε
          (fun k μ => (ξ₀ k μ : ℂ)))
      =
      Fext (fun k μ => (ξ₀ k μ : ℂ)) := by
  -- real-edge equality transferred through the reduced boundary permutation
  -- equality and the branch-agreement facts for `Fext`.
```

There is no checked production lemma yet that directly supplies this `R`.
Existing relevant surfaces are:

1. `SCV.identity_theorem_totally_real_product`, which proves propagation after
   `R`, `U`, and `Fext` are built;
2. `BHW.reduced_bargmann_hall_wightman_of_input`, which would provide reduced
   PET extension and permutation invariance for a `WightmanFunctions` input but
   is not an OS-side theorem-2 proof tool;
3. `BHW.complexLorentzAction` and reduced Lorentz equivariance of
   `reducedDiffMap`, which are likely ingredients for a non-circular
   construction of `R`;
4. the existing adjacent-swap overlap helpers, which are not enough because
   they either use a disconnected union or require actual ET-overlap already.

#### Candidate audit for the endpoint symmetry

The tempting candidates for `selectedSwapEnvelopeSymmetry` must be rejected
explicitly.  This is the current guard against reintroducing a wrapper-style
transport argument.

Use the following local notation for the selected transposition:

```lean
local notation "P" =>
  BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)

local notation "η₀" =>
  canonicalReducedDirectionC (d := d) m

local notation "ησ" =>
  permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j)

local notation "z₀" =>
  canonicalReducedShell (d := d) m ξ ε

local notation "z₁" =>
  realPermutedCanonicalReducedShell (d := d) m i j ξ ε

local notation "zσ" =>
  fun k μ => (ξ k μ : ℂ) + ε * ησ k μ * Complex.I
```

The reduced permutation algebra gives the key endpoint relation

```lean
theorem permOnReducedDiff_permutedDirection_endpoint :
    P zσ = z₁ := by
  -- This is the reduced form of permuting the real labels and the imaginary
  -- canonical direction together.
```

Consequently the analytic seam can be stated in either of two equivalent
endpoint forms:

```lean
-- canonical-real-swap form
bvt_F_reduced (d := d) OS lgc m z₁ =
  bvt_F_reduced (d := d) OS lgc m z₀

-- same-real/direction-swap form, followed by reduced permutation algebra
bvt_F_reduced (d := d) OS lgc m zσ =
  bvt_F_reduced (d := d) OS lgc m z₀
```

However, neither form is supplied by a simple global linear or affine map:

```lean
def purePermutationCandidate :
    ReducedNPointConfig d m → ReducedNPointConfig d m :=
  P

theorem purePermutationCandidate_endpoint_obstruction
    (hη : P η₀ ≠ η₀) :
    purePermutationCandidate (d := d) m i j z₀ ≠ z₁ := by
  -- Expanding `z₀` gives `P ξ + I * ε * P η₀`, while `z₁` has
  -- imaginary direction `η₀`.  Thus the pure permutation has the right
  -- real-edge action but the wrong finite-height endpoint unless the selected
  -- swap fixes the canonical reduced direction.
```

The affine correction that fixes the endpoint is

```lean
def affineEndpointCandidate
    (z : ReducedNPointConfig d m) : ReducedNPointConfig d m :=
  P z + fun k μ => ε * (η₀ k μ - (P η₀) k μ) * Complex.I
```

and it satisfies the desired endpoint calculation

```lean
theorem affineEndpointCandidate_endpoint :
    affineEndpointCandidate (d := d) m i j ξ ε z₀ = z₁ := by
  -- direct expansion
```

but it does not preserve the real edge:

```lean
theorem affineEndpointCandidate_real_edge_obstruction
    (hη : P η₀ ≠ η₀) :
    ∃ ξ₀ : NPointDomain d m,
      ¬ ∃ ξr : NPointDomain d m,
        affineEndpointCandidate (d := d) m i j ξ ε
          (fun k μ => (ξ₀ k μ : ℂ)) =
        fun k μ => (ξr k μ : ℂ) := by
  -- The imaginary translation is nonzero under `hη`; hence a real point is
  -- sent off the totally-real edge.  The real-edge boundary permutation
  -- identity therefore cannot be used to prove `Fext (R z) = Fext z` there.
```

The same obstruction appears if one instead keeps the real endpoint fixed and
tries to shift only the imaginary direction:

```lean
def sameRealDirectionCandidate
    (z : ReducedNPointConfig d m) : ReducedNPointConfig d m :=
  z + fun k μ => ε * (ησ k μ - η₀ k μ) * Complex.I

theorem sameRealDirectionCandidate_endpoint :
    sameRealDirectionCandidate (d := d) m i j ξ ε z₀ = zσ := by
  -- direct expansion

theorem sameRealDirectionCandidate_real_edge_obstruction
    (hη : ησ ≠ η₀) :
    ∃ ξ₀ : NPointDomain d m,
      ¬ ∃ ξr : NPointDomain d m,
        sameRealDirectionCandidate (d := d) m i j ξ ε
          (fun k μ => (ξ₀ k μ : ℂ)) =
        fun k μ => (ξr k μ : ℂ) := by
  -- Again the endpoint-hitting affine map translates the real edge into a
  -- finite-height imaginary slice, so it cannot be justified by the existing
  -- real-edge equality without a new finite-height theorem, which would be
  -- circular here.
```

Therefore the analytic seam is not a bookkeeping problem.  A valid proof must
produce either:

1. a genuine local BHW/Lorentz envelope symmetry whose real-edge action is a
   selected spacelike swap and whose finite-height endpoint calculation is
   `z₀ ↦ z₁`; or
2. a one-variable slice reflection theorem where the reflection lives in the
   slice parameter and the endpoint/reflection identities are proved before
   Lean implementation.

#### Route correction after the candidate audit

The audit above shows that the current private frontier theorem

```lean
bvt_F_swapCanonical_pairing
```

is a sufficient finite-height route to locality, but it is stronger than the
OS I Section 4.5 argument actually proves.  OS I uses the
Bargmann-Hall-Wightman/Jost theorem in the boundary-distribution form:

1. construct a single-valued analytic continuation on the permuted extended
   tube;
2. prove it is complex-Lorentz invariant and symmetric under permutations;
3. conclude local commutativity for the boundary distributions.

It does **not** require pointwise equality of the canonical finite-shell
integrands for every `ε > 0`.  The finite-shell target forces us to compare
`z₀` and `z₁` inside the forward/permuted tube geometry, and that is exactly
where the endpoint-symmetry obstruction appears.

So the recommended theorem-2 route should be split into two alternatives:

```lean
-- Recommended OS-I-faithful route: boundary locality directly.
theorem bv_local_commutativity_transfer_of_symmetric_PET_boundary
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (Fext : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_bv : ∀ (f : SchwartzNPoint d n)
        (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W_n f)))
    (hFext_holo : DifferentiableOn ℂ Fext (BHW.PermutedExtendedTube d n))
    (hFext_agree : ∀ z ∈ ForwardTube d n, Fext z = F z)
    (hFext_lorentz :
      ∀ (Λ : ComplexLorentzGroup d) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (BHW.complexLorentzAction Λ z) = Fext z)
    (hFext_perm :
      ∀ (σ : Equiv.Perm (Fin n)) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (fun k => z (σ k)) = Fext z) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  -- This is the Lean-facing Jost boundary theorem.  It replaces equality at
  -- every finite canonical shell by equality of the distributional boundary
  -- values obtained from the symmetric PET continuation.
```

For the OS-side witness this should be fed by a non-circular PET-extension
theorem:

```lean
theorem bvt_F_symmetric_PET_extension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ Fext : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fext (BHW.PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, Fext z = bvt_F OS lgc n z) ∧
      (∀ (Λ : ComplexLorentzGroup d) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (BHW.complexLorentzAction Λ z) = Fext z) ∧
      (∀ (σ : Equiv.Perm (Fin n)) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (fun k => z (σ k)) = Fext z) := by
  -- OS I Section 4.5 BHW extension stage for the already-constructed OS-side
  -- analytic witness `bvt_F`.  This theorem must use Euclidean symmetry,
  -- translation invariance, and the Lorentz covariance package already proved
  -- for `bvt_F`; it must not consume `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.
```

This theorem is not supplied by the checked production theorem

```lean
BHW.bargmann_hall_wightman_theorem
```

because that theorem currently takes

```lean
hF_local_dist : IsLocallyCommutativeWeak d W
```

as an input.  For theorem 2 with `W := bvt_W OS lgc`, that input is the target
conclusion and is therefore circular.  The primary route needs a sibling BHW
theorem whose matching datum is Euclidean/permutation symmetry of the OS-side
analytic continuation, not Wightman local commutativity.

There is already an important production hook for the primary route.  In
`Connectedness/BHWPermutation/PermutationFlow.lean`, the private theorem

```lean
iterated_eow_permutation_extension_of_extendF_perm
```

shows that the right non-circular input is not global Wightman locality.  It is
the extended-tube overlap equality

```lean
∀ z, z ∈ ExtendedTube d n →
  permAct (d := d) σ z ∈ ExtendedTube d n →
  extendF F (permAct (d := d) σ z) = extendF F z
```

for each permutation `σ`.  This is exactly the seam where the existing BHW
theorem currently obtains equality from `IsLocallyCommutativeWeak d W`.  The
OS-side theorem-2 route should expose this overlap-equality spine publicly and
prove it from Euclidean/permutation symmetry of the OS boundary data.

Do not replace this seam by the private theorem

```lean
extendF_perm_overlap_from_forwardTube_permInvariance
```

unless its strong input has actually been proved.  Its hypothesis is not the
same as the checked `bvt_F_perm`: it asks for

```lean
F (Γ • (w ∘ σ)) = F w
```

whenever `w ∈ ForwardTube` and `Γ • (w ∘ σ) ∈ ForwardTube`.  Plain global
coordinate-permutation invariance of `bvt_F` does not give this, because the
intermediate point `Γ • w` need not be in the forward tube.  This is precisely
the BHW/Jost continuation content.

The generic BHW theorem needed for the primary route should therefore have this
shape:

```lean
theorem bargmann_hall_wightman_theorem_of_extendF_perm
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hExtPerm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ExtendedTube d n →
        BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n →
        BHW.extendF F (BHW.permAct (d := d) σ z) =
          BHW.extendF F z) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (BHW.PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) z,
        z ∈ BHW.PermutedExtendedTube d n →
        F_ext (BHW.complexLorentzAction Λ z) = F_ext z) ∧
      (∀ (σ : Equiv.Perm (Fin n)) z,
        z ∈ BHW.PermutedExtendedTube d n →
        F_ext (fun k => z (σ k)) = F_ext z) ∧
      (∀ (G : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ G (BHW.PermutedExtendedTube d n) →
        (∀ z ∈ ForwardTube d n, G z = F z) →
        ∀ z ∈ BHW.PermutedExtendedTube d n, G z = F_ext z) := by
  -- Same output as the existing BHW theorem, but with the non-circular
  -- `extendF` overlap-invariance input replacing `hF_local_dist`.
```

The overlap-invariance input should be supplied by a smaller real-open-edge
package.  The named package must be a concrete distributional branch equality,
not an abstract proposition with no content:

```lean
def BHW.HasPermutationEdgeDistributionEquality
    (d n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (V : Set (NPointDomain d n)),
    IsOpen V →
    (∀ x ∈ V, x ∈ BHW.JostSet d n) →
    (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) →
    (∀ x ∈ V,
      BHW.realEmbed (fun k => x (σ k)) ∈ BHWCore.ExtendedTube d n) →
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      ∫ x : NPointDomain d n,
        (BHW.extendF F
            (BHW.realEmbed (fun k => x (σ k))) -
          BHW.extendF F (BHW.realEmbed x)) * φ x
      = 0
```

From this package, the production theorem should follow the same structure as
the current private hLC-based proof, with the hLC-dependent step replaced by
the OS-side edge equality:

```lean
theorem BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (hEdge :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
          =
          ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed x) * φ x) :
    ∀ x ∈ V,
      BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) =
        BHW.extendF F (BHW.realEmbed x) := by
  -- implemented in `BHWPermutation/EdgeDistribution.lean`.
  -- This is the direct compact-test pairing form consumed by the SCV theorem.

theorem BHW.extendF_perm_overlap_of_edgePairingEquality
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hOverlap_conn :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
          BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n})
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V) (hV_ne : V.Nonempty)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (hEdge :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
          =
          ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed x) * φ x) :
    ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ BHW.ExtendedTube d n →
      BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n →
      BHW.extendF F (BHW.permAct (d := d) σ z) =
        BHW.extendF F z := by
  -- implemented in `BHWPermutation/EdgeDistribution.lean`.
  -- It applies `BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality`
  -- on `V`, then uses `extendF_perm_eq_on_connectedDomain_of_realOpen`
  -- on the explicit connected overlap.
```

For `F := bvt_F OS lgc n`, the concrete theorem slot is:

```lean
theorem bvt_F_restrictedLorentzInvariant_forwardTube
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      bvt_F OS lgc n
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
      bvt_F OS lgc n z := by
  -- implemented in `OSToWightmanSelectedWitness.lean` from
  -- `BHW.Task5Bridge.real_lorentz_invariance_from_euclidean_distributional`
  -- and `bvt_F_ofEuclidean_wick_pairing`.

theorem bvt_F_complexLorentzInvariant_forwardTube
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n →
      BHW.complexLorentzAction Λ z ∈ ForwardTube d n →
      bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
        bvt_F OS lgc n z := by
  -- implemented in `OSToWightmanSelectedWitness.lean` from
  -- `BHW.complex_lorentz_invariance` and the restricted real theorem above,
  -- with the `BHW.ForwardTube`/root `ForwardTube` adapter made explicit.

theorem bvt_F_extendF_perm_eq_on_realJost_of_OS_symmetry
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ σ : Equiv.Perm (Fin n),
      ∀ x : NPointDomain d n,
        x ∈ BHW.JostSet d n →
        BHW.realEmbed x ∈ BHW.ExtendedTube d n →
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n →
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (σ k))) =
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  -- This is the OS-side Jost theorem replacing the hLC-based real-open
  -- equality currently used inside `PermutationFlow.lean`.
  --
  -- It must not be proved by asserting global continuity of the raw real trace
  -- `x ↦ bvt_F OS lgc n (realEmbed x)`: Wightman boundary values are
  -- distributional in general.  The equality is instead an equality of the
  -- BHW analytic continuation `extendF` on real Jost points.
  --
  -- Proof inputs:
  -- 1. Euclidean permutation symmetry `OS.E3_symmetric`;
  -- 2. the Euclidean restriction theorem for `bvt_F`;
  -- 3. `bvt_F_restrictedLorentzInvariant_forwardTube` and the derived complex
  --    Lorentz invariance;
  -- 4. Jost/BHW geometry identifying real Jost points as real edges of the
  --    extended tube;
  -- 5. the identity theorem / edge-of-the-wedge propagation on the connected
  --    real Jost edge.

theorem bvt_F_hasPermutationEdgeDistributionEquality
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ σ : Equiv.Perm (Fin n),
      BHW.HasPermutationEdgeDistributionEquality d n (bvt_F OS lgc n) σ := by
  intro σ V hV_open hV_jost hV_ET hV_permET φ hφ_compact hφ_supp
  have hpoint :=
    bvt_F_extendF_perm_eq_on_realJost_of_OS_symmetry
      (d := d) OS lgc n σ
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hxV : x ∈ V
  · have hx_eq := hpoint x (hV_jost x hxV) (hV_ET x hxV) (hV_permET x hxV)
    simp [hx_eq]
  · have hφ_zero : φ x = 0 := by
      -- `hφ_supp` says `tsupport φ ⊆ V`; outside `V`, the value is zero.
      have hx_not_tsupport : x ∉ tsupport (φ : NPointDomain d n → ℂ) := by
        intro hx
        exact hxV (hφ_supp hx)
      exact image_eq_zero_of_notMem_tsupport hx_not_tsupport
    simp [hφ_zero]
```

For `F := bvt_F OS lgc n`, this boundary equality should be proved from:

1. the OS Euclidean permutation axiom `OS.E3_symmetric`;
2. `bvt_euclidean_restriction`, identifying the Euclidean real section of the
   analytic witness with the OS Schwinger functional;
3. `bvt_F_restrictedLorentzInvariant_forwardTube` and
   `bvt_F_complexLorentzInvariant_forwardTube`;
4. Jost/BHW real-edge geometry and the connected-domain identity theorem;
5. the elementary support lemma that a Schwartz function vanishes outside its
   topological support.

Global `bvt_F_perm` is useful context, but it is not by itself the proof of PET
symmetry: `extendF` is defined by choosing forward-tube representatives, and a
permuted real Jost point may have a different representative.  The primary
edge theorem must compare the BHW continuation values themselves.

#### The exact OS replacement for the forbidden hLC step

The current private proof
`extendF_perm_eq_on_realOpen_of_distributional_local_commutativity` should be
mined very literally.  Its analytic and measure-theoretic spine is usable:

1. define the two continuous real-edge traces
   `gV x := extendF F (realEmbed (x ∘ σ))` and
   `hVf x := extendF F (realEmbed x)`;
2. use `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`;
3. recover both integrals as boundary values of the same forward-tube witness;
4. reduce the equality of those two integrals to a distributional permutation
   equality for the boundary distribution on Jost-supported test functions.

The only circular line in that private proof is:

```lean
have hW_eq : W n φσ = W n φ :=
  distributional_perm_invariant_on_jost_support (d := d) n W hF_local_dist
    φ hφ_jost σ⁻¹
```

For theorem 2 this must be replaced by the OS theorem:

```lean
theorem bvt_W_perm_invariant_on_compactJostOverlap_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (σ : Equiv.Perm (Fin n))
      (V : Set (NPointDomain d n)),
      IsOpen V →
      (∀ x ∈ V, x ∈ BHW.JostSet d n) →
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) →
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) →
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      bvt_W OS lgc n
        (BHW.permuteSchwartz (d := d) σ⁻¹ φ) =
      bvt_W OS lgc n φ := by
  -- Compatibility adapter, not the theorem-2 OS core:
  -- the direct branch-distribution theorem plus boundary recovery implies that
  -- the reconstructed Wightman boundary distribution has permutation-equal
  -- values on compact tests supported in the chosen Jost overlap `V`.
```

The local-overlap, compact-support, and topological-support hypotheses are
deliberate.  The existing open-real-edge
uniqueness theorem
`SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` only
tests compactly supported Schwartz functions with `tsupport` in the chosen real
open set `V`.  Proving permutation equality for all Jost-supported Schwartz
functions would be stronger than the current BHW/PET spine needs and should not
be made a blocker for theorem 2.  Requiring `tsupport φ ⊆ V` is also the
OS-correct condition: since `V ⊆ JostSet`, it lets the Euclidean test be
regarded as a `ZeroDiagonalSchwartz` test by separating its topological support
from the coincidence locus.  A pointwise nonzero-support condition is enough
for the old hLC proof, but it is too weak for the OS axiom surface.

The existing private `permuteSchwartz` construction from `PermutationFlow.lean`
must be publicized with its support, compact-support, and measure-preserving
lemmas:

```lean
def BHW.permuteSchwartz
    (σ : Equiv.Perm (Fin n)) (φ : SchwartzNPoint d n) :
    SchwartzNPoint d n := ...

@[simp] theorem BHW.permuteSchwartz_apply ...
@[simp] theorem BHW.permuteSchwartz_mul ...
theorem BHW.permute_support_jost ...
theorem BHW.permute_tsupport_jost ...
theorem BHW.permuteSchwartz_hasCompactSupport ...
theorem BHW.integral_perm_eq_self ...
```

With the direct edge-distribution package available, the preferred
Lean-facing pointwise theorem should not pass through `W` at all.  It is just
the compact-support uniqueness theorem applied to the two continuous
`extendF` traces:

```lean
theorem BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (hEdge :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
          =
          ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed x) * φ x) :
    ∀ x ∈ V,
      BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) =
        BHW.extendF F (BHW.realEmbed x) := by
  -- Define `gV x := extendF F (realEmbed (x ∘ σ))` and
  -- `hVf x := extendF F (realEmbed x)`.
  -- Use `extendF_holomorphicOn` to get continuity of both traces on `V`.
  -- Apply
  -- `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`.
  -- In the test-function callback, pass
  -- `hEdge φ hφ_compact hφ_tsupport` directly.
```

This theorem is implemented and exact-checked in
`BHWPermutation/EdgeDistribution.lean`.  The zero-of-difference formulation of
edge distribution equality remains useful as an OS-side mathematical package,
but the Lean-facing uniqueness theorem consumes pairing equality directly,
which avoids smuggling an extra integrability obligation into this adapter.

The theorem below is a secondary compatibility route, useful only if we decide
to mine the private hLC proof literally.  It should not be the primary route
once `bvt_F_hasPermutationEdgeDistributionEquality` has been proved.

```lean
theorem BHW.extendF_perm_eq_on_realOpen_of_jost_distribution_symmetry
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist :
      ∀ (φ : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W n φ)))
    (hW_overlap_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (V : Set (NPointDomain d n)),
        IsOpen V →
        (∀ x ∈ V, x ∈ BHW.JostSet d n) →
        (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) →
        (∀ x ∈ V,
          BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) →
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        W n (BHW.permuteSchwartz (d := d) σ⁻¹ φ) = W n φ)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) :
    ∀ x ∈ V,
      BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) =
        BHW.extendF F (BHW.realEmbed x) := by
  -- Copy the private proof, replacing the hLC-derived `hW_eq` with
  -- `hW_overlap_perm σ V hV_open hV_jost hV_ET hV_permET
  --   φ hφ_compact hφ_tsupport`.
```

Then the OS specialization is:

```lean
theorem bvt_F_extendF_perm_eq_on_realJost_of_OS_symmetry
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ σ x,
      x ∈ BHW.JostSet d n →
      BHW.realEmbed x ∈ BHW.ExtendedTube d n →
      BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n →
      BHW.extendF (bvt_F OS lgc n)
        (BHW.realEmbed (fun k => x (σ k))) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  -- Apply the generic real-open theorem on the open set
  -- `{y | y ∈ JostSet d n ∧ realEmbed y ∈ ET ∧ realEmbed (y∘σ) ∈ ET}`
  -- or on a smaller neighborhood supplied by the caller.
  -- Inputs:
  --   hF_holo      := bvt_F_holomorphic OS lgc n
  --   hF_lorentz   := bvt_F_restrictedLorentzInvariant_forwardTube OS lgc n
  --   hEdge        := bvt_F_hasPermutationEdgeDistributionEquality OS lgc n σ V ...
```

This decomposition is the current proof-doc frontier.  The generic
`extendF`/Schwartz/support code is close to implementation because it is already
present privately.  The genuinely mathematical theorem still requiring proof
documentation is `bvt_F_extendF_perm_edgeDistribution_eq_from_OS`.

That theorem must be proved by an OS/BHW edge argument, not by raw continuity
and not by first proving global Wightman locality:

1. construct the OS-side analytic branches for the two permutation orderings
   from the ACR(1) witness behind `bvt_F`;
2. prove their Euclidean restrictions agree by `OS.E3_symmetric` and
   `bvt_euclidean_restriction`;
3. use the repaired many-variable identity/EOW theorem on the Jost real edge;
4. identify the resulting real-edge distribution with the two
   `extendF (bvt_F OS lgc n)` boundary traces on the chosen overlap `V`.

Until this four-step OS edge theorem is written at this level of precision, the
production Lean proof should stop before `bvt_F_extendF_perm_eq_on_realJost...`.

#### Selected-witness issue for the OS edge theorem

The selected-witness ACR package is now implemented.  The current definition

```lean
def bvt_F (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (full_analytic_continuation_with_acr_symmetry_growth OS lgc n).choose
```

keeps the theorem-2 proof about the same selected analytic object used by all
downstream boundary-value theorems and avoids any transfer theorem between
independent `Classical.choose` witnesses.  The implemented theorem surface is:

```lean
theorem full_analytic_continuation_with_acr_symmetry_growth
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (AnalyticContinuationRegion d k 1) ∧
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) ∧
      (∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        W_analytic (fun j => z (σ j)) = W_analytic z) ∧
      (∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        W_analytic (fun j => z j + a) = W_analytic z) ∧
      (∀ (x : NPointDomain d k) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (W_analytic (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        W_analytic (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ ForwardTube d k,
          ‖W_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N
```

It is proved by reusing the already-checked
`schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant`;
the `ForwardTube` holomorphy conjunct is just `hACR.mono
(forwardTube_subset_acr_one ...)`, and the growth conjunct is the existing
ACR(1) growth restricted to `ForwardTube`.

The selected `bvt_F` API now exposes:

```lean
theorem bvt_F_acrOne_package ...
```

by projection from the stronger `choose_spec`.

#### Local-overlap decomposition of the OS branch equality

The OS distribution theorem needed by the public real-open `extendF` theorem is
not a global all-Jost statement and does not need to be routed through `bvt_W`
first.  The preferred object is the compact edge-distribution equality for the
two `extendF` real-edge traces on the same real-open overlap `V`.

Important implementation guardrail: the theorem below is an exported package
for an arbitrary permutation `σ`; it is not meant to be proved by a single
ACR(1) edge-of-the-wedge application for arbitrary `σ`.  The local EOW seed is
the adjacent/order-change statement.  The arbitrary-permutation export must be
obtained either by the BHW/PET permutation-flow machinery or by an explicit
transported-overlap induction that supplies every intermediate ET/permuted-ET
overlap.  Do not hide that propagation inside the name below.

```lean
theorem bvt_F_extendF_perm_edgeDistribution_eq_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (σ k))) * φ x
      =
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- Export theorem.  The proof must factor through the adjacent/order-change
  -- OS EOW seed plus BHW/PET propagation, or through an explicit transported
  -- overlap induction.  It is not a one-shot ACR(1) theorem for arbitrary σ.
```

The adjacent seed is the actual local EOW theorem:

```lean
theorem bvt_F_extendF_adjacentEdgeDistribution_eq_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_swapET :
      ∀ x ∈ V,
        BHW.realEmbed
          (fun k => x ((Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈
            BHW.ExtendedTube d n)
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed
            (fun k => x ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) * φ x
      =
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- OS.E3_symmetric gives equality on the Euclidean edge.
  -- The selected ACR(1) branch package and many-variable EOW propagate that
  -- equality to the adjacent real-open Jost overlap `V`.
```

The analytic theorem hidden in the last comment must be stated separately.  The
checked theorem

```lean
SCV.edge_of_the_wedge_theorem
```

has pointwise continuous boundary hypotheses.  The OS input supplied by
`OS.E3_symmetric` and `bvt_euclidean_restriction` is instead a compact-test
distributional equality on the Euclidean edge.  Therefore the production proof
needs a distributional EOW bridge, not a call to the pointwise theorem with an
unstated raw boundary-continuity assumption:

```lean
theorem bvt_F_distributionalEOW_permBranch_from_euclideanEdge
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (hEuclid :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x (σ k))) * φ x
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x) :
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (σ k))) * φ x
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- This is the honest analytic seam.  It should be proved as a compact-test
  -- distributional EOW statement for the selected `bvt_F_acrOne_package`.
  -- It must not assert pointwise continuity of
  -- `x ↦ bvt_F OS lgc n (BHW.realEmbed x)`.
```

This theorem is allowed to be an SCV/BHW support theorem if stated without QFT
objects, but if it mentions `OS`, `bvt_F`, or `bvt_W`, it belongs in the
Wick-rotation theorem-2 support layer.  In either placement, it is the remaining
mathematical proof-doc gap for the branch-distribution route.

The implementation-ready decomposition is the following.  The local version of
the already-checked Wick-section identity theorem has now been added in
`OSToWightmanTubeIdentity.lean`.  The older theorem
`eqOn_openConnected_of_distributional_wickSection_eq` asks for compact-test
equality on the full Wick section of `U`; the theorem-2 route only has equality
on a chosen real-open overlap `V`.  The needed general SCV lemma is:

```lean
theorem eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (V : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_wick :
      ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U)
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F U)
    (hG : DifferentiableOn ℂ G U)
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) * φ x =
        ∫ x : NPointDomain d n,
            G (fun k => wickRotatePoint (x k)) * φ x) :
    Set.EqOn F G U := by
  -- Copy the proof of
  -- `eqOn_openConnected_of_distributional_wickSection_eq`.
  -- The only change is that the preliminary real equality is obtained on
  -- `V`, not on the whole Wick section of `U`:
  --
  --   1. use continuity of the Wick traces on `V`;
  --   2. apply
  --      `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`
  --      with `hV_open` and `hint`;
  --   3. apply `SCV.identity_theorem_totally_real_product` to the holomorphic
  --      difference on the connected domain `U`, with the nonempty open real
  --      edge `V`.
```

If `V = ∅`, the branch-distribution theorem should bypass this identity theorem:
`tsupport φ ⊆ ∅` implies the test is zero, so both integrals vanish.  All
nontrivial applications to pointwise real-open equality use neighborhoods of a
chosen point and therefore have `V.Nonempty`.

Second, isolate the genuine BHW/PET analytic continuation data as an envelope
theorem.  This theorem is not a wrapper: it is exactly the missing statement
that the two branches have a common connected holomorphic domain joining the
Euclidean Wick edge to the real Jost overlap.

Important correction: this envelope is sector-local on the Euclidean side.
For a general real-open Jost overlap `V`, the Wick-rotated points
`fun k => wickRotatePoint (x k)` need not lie in `ACR(1)` or in the forward
tube.  The ACR(1) witness is holomorphic on the ordered Euclidean time sector;
outside that sector its values are still defined as a total function, but they
cannot be used as boundary values of a holomorphic branch without first
permuting to an ordered sector.  Therefore the implementation must prove the
branch envelope in the following order:

1. Sector-local envelope for a fixed strict Euclidean time ordering `τ`.
2. Distributional EOW on that sector.
3. Finite sector decomposition / partition of the compact test pairing,
   using permutation symmetry to rewrite each sector back to the original
   branch.
4. A separate null-wall lemma for the time-tie hyperplanes, or a smooth
   partition-of-unity construction that avoids non-Schwartz indicator
   functions.

The theorem name below is the exported all-`V` package.  Its proof must not
pretend that the all-`V` Euclidean edge is a single ACR(1) edge.

```lean
theorem bvt_F_permBranchEnvelope_on_jostOverlap_from_ACR_and_BHW
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
      (F_id F_perm : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U ∧
      IsConnected U ∧
      (∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
      DifferentiableOn ℂ F_id U ∧
      DifferentiableOn ℂ F_perm U ∧
      (∀ x ∈ V,
        F_id (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
      (∀ x ∈ V,
        F_perm (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (σ k)))) ∧
      (∀ x ∈ V,
        F_id (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) ∧
      (∀ x ∈ V,
        F_perm (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (σ k)))) := by
  -- This is the analytic/PET seam.  The proof should use:
  --   * `bvt_F_acrOne_package` for the selected witness on the Euclidean side;
  --   * the checked BHW `extendF` holomorphy on the extended tube;
  --   * Jost/ET geometry for `V`;
  --   * adjacent/order-change EOW plus permutation-flow propagation for
  --     arbitrary `σ`.
  --
  -- Do not prove the arbitrary-`σ` envelope by a one-shot ACR(1) argument.
  -- The adjacent envelope is the local seed; the arbitrary envelope is an
  -- export of the BHW/PET permutation-flow spine.
```

The sector-local statement should be explicit:

```lean
def EuclideanOrderedPositiveTimeSector
    (τ : Equiv.Perm (Fin n)) : Set (NPointDomain d n) :=
  {x | (fun k => x (τ k)) ∈ OrderedPositiveTimeRegion d n}

theorem wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
    (τ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ) :
    (fun k => wickRotatePoint (x (τ k))) ∈ ForwardTube d n := by
  -- Apply `euclidean_ordered_in_forwardTube` to the permuted Euclidean
  -- configuration.  The positivity condition is essential because the
  -- absolute-coordinate forward tube compares the first point with the origin.

theorem bvt_F_permBranchEnvelope_on_timeSector_from_ACR_and_BHW
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ τ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_sector : V ⊆ EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
      (F_id F_perm : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U ∧
      IsConnected U ∧
      (∀ x ∈ V, (fun k => wickRotatePoint (x (τ k))) ∈ U) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
      DifferentiableOn ℂ F_id U ∧
      DifferentiableOn ℂ F_perm U ∧
      (∀ x ∈ V,
        F_id (fun k => wickRotatePoint (x (τ k))) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
      (∀ x ∈ V,
        F_perm (fun k => wickRotatePoint (x (τ k))) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (σ k)))) ∧
      (∀ x ∈ V,
        F_id (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) ∧
      (∀ x ∈ V,
        F_perm (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (σ k)))) := by
  -- Use `bvt_F_acrOne_package` and
  -- `wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector` to place the Wick edge
  -- on an honest holomorphic branch.  The equations on the Wick edge use
  -- `bvt_F_perm` to remove the sector-ordering permutation `τ`.  For the
  -- permuted branch, the relevant forward-tube permutation is
  -- `ρ := τ⁻¹ * σ`, since
  -- `(fun k => wickRotatePoint (x (τ k))) ∘ ρ =
  --   fun k => wickRotatePoint (x (σ k))`.
  -- The real-edge equations use BHW `extendF`.
```

This correction also changes the all-sector export.  The old phrase "strict
time sector decomposition" is not implementation-ready by itself for two
separate reasons:

1. ordering alone does not put the Wick point in the absolute-coordinate
   forward tube; positive time is needed for the first point relative to the
   origin;
2. an arbitrary compactly supported Euclidean test is not supported in the
   positive-time cone.

The production-ready export should use a **uniform translation of the compact
support**, not a pointwise translation depending on `x`.  This keeps the
Schwartz-test surface honest.  Given a compactly supported test `φ`, choose one
real Euclidean time shift `A` so that every point in `tsupport φ` has positive
time after adding `A` to the time coordinate.  Then work with the translated
test and translate the resulting real-edge equality back by real translation
invariance.

The support and null-wall lemmas needed for this are:

```lean
theorem ae_pairwise_distinct_timeCoords :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0

def positiveTimeTranslate (A : ℝ) (x : NPointDomain d n) :
    NPointDomain d n :=
  fun k μ => x k μ + if μ = 0 then A else 0

theorem exists_uniform_positiveTimeShift_of_compact_tsupport
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ),
        ∀ k : Fin n, 0 < positiveTimeTranslate (d := d) (n := n) A x k 0

theorem positiveTimeTranslate_mem_orderedSector_of_pairwise_distinct
    (A : ℝ) (hApos :
      ∀ k : Fin n, 0 < positiveTimeTranslate (d := d) (n := n) A x k 0)
    (hdistinct : ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0) :
    ∃ τ : Equiv.Perm (Fin n),
      positiveTimeTranslate (d := d) (n := n) A x ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ
```

For the compact-support shift, use compactness of `tsupport φ` and continuity
of the finitely many coordinate functions `x ↦ x k 0` to get a lower bound.
For the sector theorem, use `τ := Tuple.sort (fun k => x k 0)`; pairwise
distinctness upgrades monotone sorting to strict monotonicity, and the uniform
positivity hypothesis gives the positive-time part.

The theorem-2 use of this shift is only branch placement.  It must not replace
the OS-side Euclidean equality with a Wightman-side permutation theorem.  The
actual equality still comes from

```lean
OS.E3_symmetric
bvt_euclidean_restriction
bvt_F_translationInvariant
bvt_F_perm
```

The translated-test surface should be explicit.  If `a_A` is the real
spacetime vector with time component `A` and spatial components `0`, then
`positiveTimeTranslate A x = fun k => x k + a_A`.  The existing semigroup
test map is exactly the required translated test:

```lean
timeShiftSchwartzNPoint (d := d) A φ
```

and prove:

```lean
@[simp] theorem timeShiftSchwartzNPoint_apply_positiveTimeTranslate
    (A : ℝ) (φ : SchwartzNPoint d n) (y : NPointDomain d n) :
    timeShiftSchwartzNPoint (d := d) A φ y =
      φ (positiveTimeTranslate (d := d) (n := n) (-A) y)

theorem hasCompactSupport_timeShiftSchwartzNPoint
    (A : ℝ) (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ)) :
    HasCompactSupport
      (timeShiftSchwartzNPoint (d := d) A φ :
        NPointDomain d n → ℂ)

theorem tsupport_timeShiftSchwartzNPoint_subset_positiveTimeTranslate_image
    (A : ℝ) (φ : SchwartzNPoint d n)
    (V : Set (NPointDomain d n))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    tsupport
        (timeShiftSchwartzNPoint (d := d) A φ :
          NPointDomain d n → ℂ)
      ⊆ positiveTimeTranslate (d := d) (n := n) A '' V
```

The real-open image data can be transported by the same real translation:

```lean
theorem isOpen_positiveTimeTranslate_image
    (A : ℝ) (V : Set (NPointDomain d n)) (hV_open : IsOpen V) :
    IsOpen (positiveTimeTranslate (d := d) (n := n) A '' V)
```

However, the following tempting theorem shapes are **false** for the current
absolute-coordinate BHW definitions and must not be implemented:

```lean
-- false
positiveTimeTranslate A x ∈ BHW.JostSet d n ↔ x ∈ BHW.JostSet d n

-- false
BHW.realEmbed (positiveTimeTranslate A x) ∈ BHW.ExtendedTube d n ↔
  BHW.realEmbed x ∈ BHW.ExtendedTube d n
```

Reason: `BHW.JostSet d n` is not only a pairwise-difference condition; by
definition it also requires every absolute point `x i` to be spacelike relative
to the origin.  Uniform time translation preserves pairwise differences but can
turn an individual spacelike vector into a timelike vector.  The
absolute-coordinate `ExtendedTube` has the same issue: translation invariance of
the **value** of the BHW extension is available only under explicit hypotheses
that both configurations already lie in `PermutedExtendedTube`, not as
membership invariance of the tube itself.

Therefore the translated compact-support route cannot transport the Jost/ET
real-edge hypotheses by asserting membership invariance.  It must use one of
the following honest repairs:

1. a translated-PET extension for the selected OS witness, analogous to the
   `BHWTranslation.lean` `F_ext_on_translatedPET` package, so the translated
   positive-time branch is evaluated through a PET witness rather than through
   raw `BHW.extendF` membership; or
2. a reduced-difference-coordinate formulation in which uniform translations
   are quotient-killed before the Jost/ET hypotheses are applied.

The only honest raw-`extendF` translation theorem has **ET hypotheses**, not PET
hypotheses.  It is useful as an adapter on points that already lie in the
ordinary extended tube, but it is not a membership-transport theorem and does
not by itself justify applying a sector-local BHW branch theorem at a translated
real point:

```lean
theorem bvt_extendF_realTimeTranslate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (A : ℝ)
    (x : NPointDomain d n)
    (hxET : BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hxAET :
      BHW.realEmbed (positiveTimeTranslate (d := d) (n := n) A x) ∈
        BHW.ExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.realEmbed (positiveTimeTranslate (d := d) (n := n) A x)) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
```

These are real-translation invariance facts, not complex-time translation
facts.  They should be proved from existing BHW translation-invariance
geometry and always retain the two ET-membership hypotheses.  They do not
assume local commutativity of `bvt_W OS lgc`.  The value theorem
`bvt_extendF_realTimeTranslate` should use the absolute forward-tube input
already exposed as
`bvt_absoluteForwardTubeInput`: descend to the reduced/Route-1 BHW extension,
use the algebraic translation-invariance of the reduced pullback, and identify
it back with `BHW.extendF (bvt_F OS lgc n)` on `ExtendedTube`.  This is the same
translation-invariance mechanism as `BHWTranslation.lean`, but with the
selected OS witness instead of an already-packaged `WightmanFunctions` object.

#### 6.7.1. Selected-OS translated-PET repair package

The repair above should be implemented as a selected-OS analogue of the already
proved `BHWTranslation.lean` translated-PET package.  This is the next proof-doc
unit that must be made Lean-ready before any branch-envelope theorem consumes
translated positive-time support.

The following theorem shape is now explicitly rejected:

```lean
-- wrong surface: raw `BHW.extendF` is only the ordinary ET branch,
-- not the full PET extension.
theorem bvt_extendF_translation_invariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n) (fun k μ => z k μ + c μ) =
      BHW.extendF (bvt_F OS lgc n) z
```

Reason: `BHW.extendF F` is the choice-based complex-Lorentz extension from the
forward tube to the ordinary `BHW.ExtendedTube`.  The full PET value in
`BHWTranslation.lean` is `(W_analytic_BHW Wfn n).val`, not raw
`BHW.extendF`.  For theorem 2 we cannot use
`W_analytic_BHW (os_to_wightman_full OS lgc) n`, because its uniqueness proof
uses `Wfn.locally_commutative`, which is exactly the target theorem.

The first corrected theorem slot is the ET-local adapter:

```lean
theorem bvt_extendF_translation_invariant_on_ET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ BHW.ExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n) (fun k μ => z k μ + c μ) =
      BHW.extendF (bvt_F OS lgc n) z
```

This adapter is still nontrivial, but its domain matches raw `extendF`.  It
should be proved by identifying raw `extendF (bvt_F OS lgc n)` on ET with the
Route-1 reduced pullback associated to `bvt_absoluteForwardTubeInput`, then
using algebraic translation-invariance of the reduced pullback.

The PET-level object must be a selected OS extension value, not raw
`BHW.extendF`.  The theorem-2 route needs the following existence package:

```lean
theorem bvt_selectedPETExtension_exists
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ Fpet : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fpet (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, Fpet z = bvt_F OS lgc n z) ∧
      (∀ z ∈ BHW.ExtendedTube d n,
        Fpet z = BHW.extendF (bvt_F OS lgc n) z) ∧
      (∀ (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n →
        Fpet (fun k μ => z k μ + c μ) = Fpet z)
```

Once this theorem exists, the selected extension is chosen in the usual way:

```lean
noncomputable def bvt_F_PETExtension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (bvt_selectedPETExtension_exists OS lgc n).choose

theorem bvt_F_PETExtension_eq_extendF_on_ET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d n) :
    bvt_F_PETExtension OS lgc n z =
      BHW.extendF (bvt_F OS lgc n) z

theorem bvt_F_PETExtension_translation_invariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    bvt_F_PETExtension OS lgc n (fun k μ => z k μ + c μ) =
      bvt_F_PETExtension OS lgc n z
```

The proof of `bvt_selectedPETExtension_exists` must follow the non-circular
Route-1/reduced-difference pattern:

1. split the `n = 0` and `n = m + 1` cases;
2. instantiate the absolute forward-tube input
   `bvt_absoluteForwardTubeInput OS lgc m`;
3. descend it with `BHW.descendAbsoluteForwardTubeInput`;
4. build or reuse the reduced BHW extension for that descended input;
5. pull it back along `reducedDiffMap`;
6. prove the pulled-back extension is algebraically translation-invariant by
   `BHW.reduced_pullback_translation_invariant`;
7. identify the pulled-back extension with raw
   `BHW.extendF (bvt_F OS lgc (m+1))` on the non-permuted ET branch;
8. use the selected OS permutation/edge-distribution package, not
   `Wfn.locally_commutative`, to glue the PET branches needed by theorem 2.

The missing substep is item 4 plus the PET gluing part of item 8 for a selected
OS input.  The current `BHWTranslation.lean` implementation proves the same
translation-invariance pattern for an already packaged `WightmanFunctions`
object using `route1AbsoluteBHWExtensionCanonical` and
`W_analytic_BHW_unique`; theorem 2 cannot instantiate that route with
`os_to_wightman_full OS lgc`, because that structure already contains locality.
So the theorem-2 repair must either generalize the Route-1 reduced extension
from `WightmanFunctions` to a non-circular selected OS input carrying
`bvt_F_acrOne_package`, or prove the same comparison directly for
`bvt_absoluteForwardTubeInput`.

Implementation status after the generic `TranslatedPET` value API: the TPET
witness-independence algebra is no longer a blocker.  The remaining
implementation blocker is specifically the PET scalar `bvt_F_PETExtension`
and its PET translation invariance:

```lean
-- the exact hard input now needed by `translatedPETValue`
theorem bvt_F_PETExtension_translation_invariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    bvt_F_PETExtension OS lgc n (fun k μ => z k μ + c μ) =
      bvt_F_PETExtension OS lgc n z
```

The tempting shortcut is invalid:

```lean
-- forbidden/circular: constructs a full WightmanFunctions record in order to
-- call `W_analytic_BHW` or `W_analytic_BHW_unique`
let Wfn := os_to_wightman_full OS lgc
```

Reason: `os_to_wightman_full` contains the theorem-2 locality field being
proved.  Likewise, the existing `BHWTranslation.lean::bhw_translation_invariant`
is not a selected-OS theorem; its proof uses `W_analytic_BHW_unique`, whose BHW
theorem input includes `Wfn.locally_commutative`.

Therefore the next production theorem must have one of the following non-
circular shapes.

First possible route: generalize Route 1 away from `WightmanFunctions`.

```lean
-- Generic selected reduced/PET route.  The statement should not mention
-- `WightmanFunctions`, and should consume an `AbsoluteForwardTubeInput` plus
-- the reduced boundary/permutation edge data that replaces global locality.
theorem selectedPETExtension_exists_of_absoluteInput
    {Wabs : SchwartzNPoint d (m + 1) → ℂ}
    (hAbs : BHW.AbsoluteForwardTubeInput (d := d) m Wabs)
    (hEdge :
      -- compact-test permutation/edge equality for the selected input,
      -- strong enough to replace `IsLocallyCommutativeWeak`
      BHW.SelectedPermutationEdgeData d m hAbs.toFun Wabs) :
    ∃ Fpet : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fpet (PermutedExtendedTube d (m + 1)) ∧
      (∀ z ∈ ForwardTube d (m + 1), Fpet z = hAbs.toFun z) ∧
      (∀ (z : Fin (m + 1) → Fin (d + 1) → ℂ)
          (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d (m + 1) →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1) →
        Fpet (fun k μ => z k μ + c μ) = Fpet z)
```

This route should reuse the already checked algebra
`BHW.reduced_pullback_translation_invariant`; its hard analytic input is the
selected reduced BHW/PET existence and gluing theorem, not the TPET translation
choice argument.

Second possible route: prove only the selected translation-invariant PET scalar
needed by theorem 2, postponing full PET permutation invariance.

```lean
theorem bvt_selectedPETTranslationScalar_exists
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    ∃ Fpet : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fpet (PermutedExtendedTube d (m + 1)) ∧
      (∀ z ∈ ForwardTube d (m + 1), Fpet z = bvt_F OS lgc (m + 1) z) ∧
      (∀ z ∈ BHW.ExtendedTube d (m + 1),
        Fpet z = BHW.extendF (bvt_F OS lgc (m + 1)) z) ∧
      (∀ (z : Fin (m + 1) → Fin (d + 1) → ℂ)
          (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d (m + 1) →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1) →
        Fpet (fun k μ => z k μ + c μ) = Fpet z)
```

This narrower route is enough for `translatedPETValue` and the compact
positive-time support argument.  It still must not be proved from global
`IsLocallyCommutativeWeak d (bvt_W OS lgc)`.  Its proof should identify `Fpet`
with the reduced pullback on PET and with raw `BHW.extendF` only on the ordinary
ET branch, where raw `extendF` is meaningful.

For both routes, the first Lean-ready preinput sublemmas are now implemented:

```lean
theorem bvt_route1AbsolutePrePullback_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    bvt_route1AbsolutePrePullback OS lgc m (fun k μ => z k μ + c μ) =
      bvt_route1AbsolutePrePullback OS lgc m z

theorem bvt_route1AbsolutePrePullback_eq_bvt_F_on_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1)) :
    bvt_route1AbsolutePrePullback OS lgc m z =
      bvt_F OS lgc (m + 1) z
```

These sublemmas are algebraic/reduced-coordinate and forward-tube comparison
statements.  They isolate the selected translation-invariant preinput without
mentioning PET gluing or locality.  They must not be mistaken for the selected
PET extension: outside the forward tube, `bvt_route1AbsolutePrePullback`
evaluates the original total forward-tube witness on a safe representative, and
is not known to be holomorphic on ET/PET or to agree with raw `BHW.extendF`.

The next hard theorem surface is therefore **not** the following overstrong
statement about the pre-pullback:

```lean
-- do not try to prove this for the pre-pullback alone
theorem bvt_route1AbsolutePrePullback_eq_extendF_on_ET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d (m + 1)) :
    bvt_route1AbsolutePrePullback OS lgc m z =
      BHW.extendF (bvt_F OS lgc (m + 1)) z
```

That statement would require precisely the missing selected reduced BHW/PET
extension.  The correct next production theorem should first construct a
selected reduced BHW extension `Fred` from the selected OS input and selected
edge/permutation data, then define the PET scalar as its absolute pullback:

```lean
noncomputable def bvt_selectedPETExtension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ :=
  BHW.pullbackReducedExtension
    (bvt_selectedReducedBHWExtension OS lgc m)

theorem bvt_selectedPETExtension_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    bvt_selectedPETExtension OS lgc m (fun k μ => z k μ + c μ) =
      bvt_selectedPETExtension OS lgc m z
```

The translation theorem is then immediate from
`BHW.reduced_pullback_translation_invariant`.  The hard part is the existence
and uniqueness/gluing theorem for `bvt_selectedReducedBHWExtension`, including
agreement with the pre-pullback on `ReducedForwardTubeN` and agreement with raw
`BHW.extendF (bvt_F OS lgc (m+1))` on the ordinary ET branch.  This is exactly
where selected OS edge-distribution data replaces the forbidden global
`Wfn.locally_commutative`.

The implementation-ready part of this paragraph is now in production in its
honest "given reduced data" form:

```lean
noncomputable def bvt_selectedPETExtensionOfReducedData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ

theorem bvt_selectedPETExtensionOfReducedData_translate_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d (m + 1))
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1)) :
    bvt_selectedPETExtensionOfReducedData OS lgc m Fred
        (fun k μ => z k μ + c μ) =
      bvt_selectedPETExtensionOfReducedData OS lgc m Fred z

theorem bvt_selectedPETExtensionOfReducedData_eq_bvt_F_on_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1)) :
    bvt_selectedPETExtensionOfReducedData OS lgc m Fred z =
      bvt_F OS lgc (m + 1) z
```

This closes the reduced-pullback algebra seam.  It deliberately does not
construct `Fred`.  The next proof-doc item must therefore specify the exact
non-circular construction of

```lean
Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
  (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
    (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun
```

from selected OS edge-distribution/permutation data.

The reduced forward-tube input required by that theorem is no longer a gap.
Production now constructs it directly from the selected OS witness:

```lean
noncomputable def bvt_reducedWightmanFamily
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d) :
    (m : ℕ) → SchwartzNPoint d m → ℂ

theorem bvt_selectedReducedBoundaryValues
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    BHW.HasReducedBoundaryValues (d := d)
      (bvt_reducedWightmanFamily OS lgc χ) m
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun

noncomputable def bvt_selectedReducedForwardTubeInput
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    BHW.ReducedForwardTubeInput (d := d)
      (bvt_reducedWightmanFamily OS lgc χ) m
```

The proof is the exact reduced/absolute change-of-variables argument already
used for the Route-1 spectrum-condition input, but specialized non-circularly
to `bvt_F`/`bvt_W`: `bvt_selectedReducedPreInput_factorization_absoluteApproach`
identifies the descended preinput with the absolute `bvt_F` approach point,
`bvt_selectedReducedBoundaryIntegral_eq_absoluteBoundaryIntegral` integrates
out the normalized basepoint cutoff, and `bvt_boundary_values` supplies the
limit.  No PET gluing, `W_analytic_BHW_unique`, `os_to_wightman_full`, or
locality input is used.

Consequently the next hard theorem surface is now narrower, but one correction
is essential.  The OS/BHW route must construct edge data only for adjacent
transpositions, not for arbitrary finite permutations.  Arbitrary permutations
can have empty real edge overlap in high arity, so an all-permutation
`V.Nonempty` witness is too strong to be the construction target.

The active selected edge-data structure and adjacent overlap adapter are now
implemented in `OSToWightmanSelectedWitness.lean`:

```lean
structure SelectedAdjacentPermutationEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) : Prop where
  overlap_connected :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
              BHW.ExtendedTube d n}
  edge_witness :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∃ V : Set (NPointDomain d n),
        IsOpen V ∧ V.Nonempty ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
        (∀ x ∈ V,
          BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
            =
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)

theorem bvt_F_extendF_adjacent_overlap_of_selectedEdgeData
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ z, z ∈ BHW.ExtendedTube d n →
      BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
        BHW.ExtendedTube d n →
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z) =
        BHW.extendF (bvt_F OS lgc n) z

def BHW.permutedExtendedTubeSector (d n : ℕ) (π : Equiv.Perm (Fin n))
theorem BHW.isOpen_permutedExtendedTubeSector
theorem BHW.permutedExtendedTube_eq_iUnion_sectors
theorem BHW.permutedExtendedTubeSector_subset_permutedExtendedTube
theorem BHW.permutedExtendedTubeSector_isPreconnected
theorem BHW.permutedExtendedTubeSector_adjacent_overlap_nonempty

def bvt_selectedPETBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z => BHW.extendF (bvt_F OS lgc n) (fun k => z (π k))

theorem bvt_selectedPETBranch_holomorphicOn_sector
    (π : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (bvt_selectedPETBranch OS lgc n π)
      (BHW.permutedExtendedTubeSector d n π)

theorem bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzπswap :
      z ∈ BHW.permutedExtendedTubeSector d n
        (π * Equiv.swap i ⟨i.val + 1, hi⟩)) :
    bvt_selectedPETBranch OS lgc n
        (π * Equiv.swap i ⟨i.val + 1, hi⟩) z =
      bvt_selectedPETBranch OS lgc n π z

theorem bvt_selectedReducedBHWExtensionData_exists
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc (m + 1)) :
    ∃ Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_selectedReducedForwardTubeInput OS lgc χ m).toFun,
      True
```

`SelectedAdjacentPermutationEdgeData` is not a global locality hypothesis.  Its
`edge_witness` field is exactly the compact-test equality consumed by
`BHW.extendF_perm_overlap_of_edgePairingEquality`, but only on adjacent
spacelike edges where the OS/Jost input is expected to exist.  Its
`overlap_connected` field supplies the adjacent connected-domain propagation.
The branch-cover package above is the Lean-ready local compatibility layer:
each branch is holomorphic on its own explicit sector, and adjacent branches
agree on adjacent sector overlaps.

The purely formal finite-cover gluing step has now been split off and
implemented in `PermutedTubeGluing.lean`.  It deliberately assumes compatibility
on all sector overlaps:

```lean
def BHW.gluedPETValue
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)

theorem BHW.gluedPETValue_eq_of_mem_sector
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hcompat :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n ρ →
        G π z = G ρ z)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π) :
    BHW.gluedPETValue G z = G π z

theorem BHW.gluedPETValue_holomorphicOn
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hG_holo :
      ∀ π, DifferentiableOn ℂ (G π) (BHW.permutedExtendedTubeSector d n π))
    (hcompat :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n ρ →
        G π z = G ρ z) :
    DifferentiableOn ℂ (BHW.gluedPETValue G) (BHW.PermutedExtendedTube d n)
```

The remaining hard gap is therefore even sharper: prove all-overlap branch
compatibility from adjacent overlap compatibility.

```lean
theorem bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    bvt_selectedPETBranch OS lgc n π z =
      bvt_selectedPETBranch OS lgc n ρ z
```

This is the exact point where the proof must use the BHW sector-graph/monodromy
argument: adjacent swaps generate the permutation graph and PET is the connected
analytic continuation domain for the adjacent-glued sectors.  It is not enough
to chain adjacent equalities at a fixed point, because a fixed `z` in two
non-adjacent sectors need not lie in every intermediate sector.  The proof must
obtain independence of analytic continuation over the finite open cover,
rather than asking for a nonexistent all-permutation real edge.

The Lean implementation is therefore not ready to close this theorem from the
current local data alone.  The missing item is a BHW cover-gluing/monodromy
theorem, not another wrapper around `SelectedAdjacentPermutationEdgeData`.

The incorrect pointwise route is already visible in the older
`BHWPermutation/PermutationFlow.lean` scaffolding:

```lean
Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ
```

or its midpoint form

```lean
permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈
    BHW.ExtendedTube d n →
  permAct (d := d) σ y ∈ BHW.ExtendedTube d n
```

This is too strong for the PET all-overlap theorem.  It asks for a single
configuration `y` to remain inside ET along a chosen adjacent-swap word.  The
whole reason to use PET is that analytic continuation can move through the
sector cover even when that fixed configuration is not in the intermediate
absolute ET sectors.

The correct theorem should be formulated at the level of analytic branches on
open sectors.  Write

```lean
S π := BHW.permutedExtendedTubeSector d n π
G π := bvt_selectedPETBranch OS lgc n π
```

The current production facts give:

1. `IsOpen (S π)`;
2. `IsPreconnected (S π)`;
3. `BHW.PermutedExtendedTube d n = ⋃ π, S π`;
4. `DifferentiableOn ℂ (G π) (S π)`;
5. `G (π * τ) = G π` on `S π ∩ S (π * τ)` for every adjacent swap `τ`;
6. `S π ∩ S (π * τ)` is nonempty for every adjacent swap `τ`.

These six facts still do not imply all-overlap compatibility for an arbitrary
finite open cover.  A tempting additional statement would be:

```lean
-- Do not adopt this as a target without a separate proof.
theorem BHW.petSector_pathSaturation_inter_next_preconnected ...
```

meaning that, for an adjacent path list `L` ending at `α` and a neighboring
sector `β`, every connected component of
`(⋃ π ∈ L, S π) ∩ S β` meets `S α ∩ S β`.  This would make an inductive
path-gluing proof straightforward, because equality on the last adjacent
overlap could be propagated to all of the new intersection by the identity
theorem.

But this path-saturation statement is itself a strong global geometry claim and
should be treated as unproved and possibly false until established from BHW
geometry.  It is not a safe next Lean target.  The production route should
instead expose the actual BHW monodromy / well-definedness theorem:

```lean
theorem BHW.extendF_pet_branch_independence_of_adjacent
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hAdj :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) →
        BHW.extendF F (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
          BHW.extendF F (fun k => z (π k))) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π →
      z ∈ BHW.permutedExtendedTubeSector d n ρ →
      BHW.extendF F (fun k => z (π k)) =
        BHW.extendF F (fun k => z (ρ k))
```

This theorem is not a wrapper: it is the hard single-valued analytic
continuation statement for the PET sector cover.  It is the selected-data
analogue of the older private `fullExtendF_well_defined` spine in
`BHWPermutation/PermutationFlow.lean`, but it must not consume
`IsLocallyCommutativeWeak d (bvt_W OS lgc)` or any theorem equivalent to the
public locality conclusion.

The proof obligations for this theorem are:

1. construct the analytic continuation space from the disjoint union of sector
   charts `Σ π, S π`, identifying adjacent charts on the full adjacent overlaps
   where `hAdj` gives equality;
2. prove the projection of this continuation space to
   `BHW.PermutedExtendedTube d n` is single-valued, or equivalently that the
   value of `BHW.extendF F` is constant on every fiber over a PET point;
3. prove this single-valuedness by the standard BHW monodromy argument, using
   adjacent swaps as the local edge-of-the-wedge seeds and the connected PET
   continuation domain, not by requiring a fixed point to remain in all
   intermediate absolute ET overlaps;
4. explicitly handle the low-dimensional branch (`d = 1`) if the available BHW
   geometry splits by dimension, as the existing `PermutationFlow` scaffolding
   does;
5. after single-valuedness is proved, define the PET scalar and use the already
   checked formal gluing adapter only as the final value-selection mechanism.

Once `BHW.extendF_pet_branch_independence_of_adjacent` exists, the algebraic
tail can follow the existing private `fullExtendF_well_defined` proof almost
verbatim, but with no `W` and no `hF_local_dist`.  The intermediate theorem
should be:

```lean
theorem BHW.F_permutation_invariance_of_petBranchIndependence
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hPET :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n ρ →
        BHW.extendF F (fun k => z (π k)) =
          BHW.extendF F (fun k => z (ρ k))) :
    ∀ {w : Fin n → Fin (d + 1) → ℂ}, w ∈ BHW.ForwardTube d n →
      ∀ {τ : Equiv.Perm (Fin n)} {Γ : ComplexLorentzGroup d},
        BHW.complexLorentzAction Γ (fun k => w (τ k)) ∈
          BHW.ForwardTube d n →
        F (BHW.complexLorentzAction Γ (fun k => w (τ k))) = F w
```

Proof sketch for the Lean term:

1. set `z := BHW.complexLorentzAction Γ (fun k => w (τ k))`;
2. `z ∈ S 1` because the hypothesis says `z ∈ ForwardTube`, hence `z ∈ ET`;
3. `z ∈ S τ⁻¹` because `fun k => z (τ⁻¹ k) = BHW.complexLorentzAction Γ w`,
   and `BHW.complexLorentzAction Γ w ∈ ET` since `w ∈ ForwardTube ⊆ ET`;
4. apply `hPET 1 τ⁻¹ z` to get
   `BHW.extendF F z = BHW.extendF F (BHW.complexLorentzAction Γ w)`;
5. rewrite the left side by `BHW.extendF_eq_on_forwardTube`;
6. rewrite the right side by `BHW.extendF_complex_lorentz_invariant` and
   `BHW.extendF_eq_on_forwardTube`.

Then the existing `fullExtendF_well_defined` algebra becomes:

```lean
theorem BHW.fullExtendF_well_defined_of_petBranchIndependence
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hPET : -- branch independence as above)
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ}
    (hw₁ : w₁ ∈ BHW.ForwardTube d n)
    (hw₂ : w₂ ∈ BHW.ForwardTube d n)
    {π₁ π₂ : Equiv.Perm (Fin n)} {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : BHW.complexLorentzAction Λ₁ (fun k => w₁ (π₁ k)) =
         BHW.complexLorentzAction Λ₂ (fun k => w₂ (π₂ k))) :
    F w₁ = F w₂
```

The proof is the existing private proof with the call to
`F_permutation_invariance` replaced by
`F_permutation_invariance_of_petBranchIndependence`.

An equivalent theorem shape is also acceptable if it is closer to the existing
private code:

```lean
theorem BHW.fullExtendF_well_defined_of_adjacentBranchEquality
    -- same analytic inputs and adjacent branch equality as above
    -- any two PET representations of the same point give the same `F` value
```

This version would let the existing `fullExtendF` construction be reused
non-circularly.  The key requirement is the same: the theorem must prove
single-valued PET analytic continuation from adjacent branch equality, not
assume all-permutation real edge data and not assume global Wightman locality.

Only after one of these BHW monodromy / well-definedness statements is proved
should the selected theorem be implemented:

```lean
theorem bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    bvt_selectedPETBranch OS lgc n π z =
      bvt_selectedPETBranch OS lgc n ρ z
```

by instantiating `G` with `bvt_selectedPETBranch OS lgc n`, `hG_holo` with
`bvt_selectedPETBranch_holomorphicOn_sector`, and `hAdj` with
`bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`.

This is the next proof-doc completion target.  Production Lean should not add a
theorem named `bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData` until
the single-valued PET monodromy / well-definedness theorem above is proved.

There is also an explicitly overstrong conditional helper:

```lean
structure SelectedAllPermutationEdgeData
theorem bvt_F_extendF_perm_overlap_of_selectedEdgeData
```

This all-permutation helper should not be treated as the OS-route construction
target.  It is retained only to keep the checked conditional branch-gluing
lemmas available while the real adjacent-to-general chain theorem is developed.
Under that overstrong hypothesis, value-level branch gluing has been checked:

```lean
noncomputable def bvt_selectedAbsolutePETGluedValue
theorem bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
theorem bvt_selectedAbsolutePETGluedValue_eq_bvt_F_on_forwardTube
theorem bvt_selectedAbsolutePETGluedValue_holomorphicOn_PET
theorem bvt_selectedAbsolutePETGluedValue_lorentzInvariant
theorem bvt_selectedAbsolutePETGluedValue_permInvariant
```

This conditional package proves what the final adjacent-chain package must
recover: the selected branch value is independent of the chosen permutation
branch, agrees with `bvt_F OS lgc n` on the original forward tube, is
holomorphic on PET, and has the expected absolute Lorentz and finite-permutation
invariance on PET.  The missing theorem is now the honest one:

```lean
theorem bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_adjacentEdgeData
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hπz : (fun k => z (π k)) ∈ BHW.ExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue OS lgc n z =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k))
```

It must be proved by chaining adjacent-swap branch equalities through the PET
sector graph, not by requiring real edge data for `π₀⁻¹ * π` directly.

The remaining implementation work inside
`bvt_selectedReducedBHWExtensionData_exists` is therefore:

1. prove adjacent-to-general PET branch gluing from
   `SelectedAdjacentPermutationEdgeData`;
2. prove the glued absolute PET scalar is constant on uniform-translation
   fibers wherever the two representatives lie in PET;
3. descend the glued absolute PET scalar through `BHW.reducedDiffMap` to the
   image domain `BHW.ReducedPermutedExtendedTubeN d m`;
4. prove the descended function agrees with
   `(bvt_selectedReducedForwardTubeInput OS lgc χ m).toFun` on
   `BHW.ReducedForwardTubeN d m`, and transport the already-proved absolute
   Lorentz/permutation invariance to the reduced invariance fields required by
   `BHW.ReducedBHWExtensionData`;
5. feed the resulting `Fred` to
   `bvt_selectedPETExtensionOfReducedData`.

#### Next quotient-descent seam: selected translation-fiber constancy

The next theorem is not yet a Lean-ready one-liner.  The exact mathematical
surface needed before reduced descent is:

```lean
theorem bvt_selectedAbsolutePETGluedValue_translationInvariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ BHW.PermutedExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue OS lgc n
        (fun k μ => z k μ + c μ) =
      bvt_selectedAbsolutePETGluedValue OS lgc n z
```

This is the real quotient-descent gate.  Once it is proved, the reduced function
can be defined on `BHW.ReducedPermutedExtendedTubeN d m` by choosing any absolute
PET representative `z` of the reduced point and evaluating
`bvt_selectedAbsolutePETGluedValue OS lgc (m + 1) z`; the theorem above gives
representative independence because equal reduced differences differ by a
uniform complex translation.

The proof should follow the already-existing base-fiber architecture, but with
the selected glued scalar in place of the old global `W_analytic_BHW` scalar:

```lean
theorem bvt_selectedAbsolutePETGluedValue_translationLocal
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d n) :
    ∃ ε > 0, ∀ t : ℂ, ‖t‖ < ε →
      (fun k μ => z k μ + t * c μ) ∈ BHW.PermutedExtendedTube d n ∧
      bvt_selectedAbsolutePETGluedValue OS lgc n
          (fun k μ => z k μ + t * c μ) =
        bvt_selectedAbsolutePETGluedValue OS lgc n z
```

Local translation should be proved by unpacking a PET witness
`z = Λ • w` with `w ∈ PermutedForwardTube π`, shrinking `t` so the same
permuted forward-tube branch remains valid, and chaining:

```text
G(z + t c)
= G(Λ • (w + t Λ⁻¹c))       by selected Lorentz invariance
= G(w + t Λ⁻¹c)             by selected Lorentz invariance
= bvt_F((w + t Λ⁻¹c)∘π)     by selected PET branch equality + FT agreement
= bvt_F(w∘π)                by selected forward-tube translation invariance
= G(w)
= G(z)
```

The local proof requires one additional named selected forward-tube theorem:

```lean
theorem bvt_F_translation_invariant_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ForwardTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ BHW.ForwardTube d n) :
    bvt_F OS lgc n (fun k μ => z k μ + c μ) =
      bvt_F OS lgc n z
```

This should be a direct extraction from
`bvt_absoluteForwardTubeInput (d := d) OS lgc (n - 1)` when `n = m + 1`, plus
the existing `AbsoluteForwardTubeInput.translation_invariant` field.  The
`n = 0` case should be treated separately or avoided by stating the selected
quotient-descent theorem at public arity `m + 1`.

To globalize local translation to arbitrary `c`, define the selected base-fiber
value for fixed reduced tail:

```lean
def bvt_selectedBaseFiberValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc (m + 1))
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    (Fin (d + 1) → ℂ) → ℂ :=
  fun ζ₀ =>
    bvt_selectedAbsolutePETGluedValue OS lgc (m + 1)
      (baseFiberConfig m d ζtail ζ₀)
```

Then prove:

```lean
theorem fderiv_bvt_selectedBaseFiberValue_eq_zero
theorem exists_isConst_bvt_selectedBaseFiberValue_of_isPreconnected
theorem bvt_selectedAbsolutePETGluedValue_translationInvariant_of_baseFiber_isPreconnected
```

The remaining mathematical gap is therefore sharply isolated: either prove the
needed `IsPreconnected (baseFiber m d ζtail)` geometry without relying on the
old WIP `sorry`, or give a different direct proof of selected
translation-fiber constancy.  Until that geometry is closed, the reduced
quotient descent is **not** 100% implementation-ready.

Once PET value-invariance exists, define the selected translated-PET value
without any arbitrary branch choice.  The purely geometric part of this step is
now implemented in `ForwardTubeLorentz.lean`: for any scalar `F` on PET that is
invariant under uniform complex translations between PET points,
`translatedPETValue F z hz` evaluates `F` at a chosen PET witness for
`z ∈ TranslatedPET`, and theorems
`translatedPET_value_eq_of_translation_invariant`,
`translatedPETValue_eq_on_PET`, and
`translatedPETValue_translation_invariant` prove witness independence,
agreement on PET, and TPET translation invariance.  The remaining theorem-2
task is therefore not the TPET choice algebra; it is to construct the selected
OS PET scalar `bvt_F_PETExtension` with the required PET translation
invariance, non-circularly.

```lean
theorem isOpen_translatedPET {d n : ℕ} [NeZero d] :
    IsOpen (TranslatedPET d n) := by
  -- `TranslatedPET` is the union over uniform translations `c` of the
  -- preimages of the open `PermutedExtendedTube d n` under
  -- `z ↦ fun k μ => z k μ + c μ`.

theorem translatedPET_perm {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ TranslatedPET d n) :
    (fun k => z (σ k)) ∈ TranslatedPET d n := by
  -- If `z + c` is in the PET, then `(z ∘ σ) + c` is in the PET by absorbing
  -- the extra permutation into the PET permutation index.

theorem translatedPET_perm_iff {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    (fun k => z (σ k)) ∈ TranslatedPET d n ↔ z ∈ TranslatedPET d n := by
  -- Apply `translatedPET_perm` with `σ` and with `σ.symm`.

theorem bvt_F_PETExtension_value_on_translatedPET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c₁ c₂ : Fin (d + 1) → ℂ)
    (h₁ : (fun k μ => z k μ + c₁ μ) ∈ PermutedExtendedTube d n)
    (h₂ : (fun k μ => z k μ + c₂ μ) ∈ PermutedExtendedTube d n) :
    bvt_F_PETExtension OS lgc n (fun k μ => z k μ + c₁ μ) =
      bvt_F_PETExtension OS lgc n (fun k μ => z k μ + c₂ μ) := by
  have key :=
    bvt_F_PETExtension_translation_invariant_on_PET
      (d := d) OS lgc n (fun μ => c₂ μ - c₁ μ)
      (fun k μ => z k μ + c₁ μ) h₁
      (by
        convert h₂ using 1
        ext k μ
        ring)
  simpa [sub_eq_add_neg, add_assoc] using key.symm

noncomputable def bvt_F_on_translatedPET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) : ℂ :=
  translatedPETValue (bvt_F_PETExtension OS lgc n) z hz
```

Then mirror the existing translated-PET API:

```lean
theorem bvt_F_on_translatedPET_eq_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz_pet : z ∈ PermutedExtendedTube d n)
    (hz_tpet : z ∈ TranslatedPET d n) :
    bvt_F_on_translatedPET OS lgc n z hz_tpet =
      bvt_F_PETExtension OS lgc n z

theorem bvt_F_on_translatedPET_translation_invariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ TranslatedPET d n) :
    bvt_F_on_translatedPET OS lgc n z hz =
      bvt_F_on_translatedPET OS lgc n (fun k μ => z k μ + c μ) hzc
```

If an everywhere-defined integrand is later needed, it may follow the existing
`F_ext_on_translatedPET_total` pattern:

```lean
noncomputable def bvt_F_on_translatedPET_total ... z :=
  if hz : z ∈ TranslatedPET d n then
    bvt_F_on_translatedPET OS lgc n z hz
  else 0
```

but this total version is only honest when paired with the null-set theorem
`ae_euclidean_points_in_translatedPET` or a support hypothesis proving the
integrand is used only on `TranslatedPET`.  It must not be used as a pointwise
extension off `TranslatedPET`.

Only after this selected translated-PET package is available should the
translated positive-time compact-support argument continue.  In that version,
positive-time translation is used to place Wick-rotated Euclidean points in a
forward/PET witness, while the final comparison back to the original support is
performed by `bvt_F_on_translatedPET_translation_invariant`, not by a false
Jost/ET membership-transport theorem.

The following raw `extendF` theorem remains an ET-local pointwise sublemma.  It
is useful on real-open neighborhoods where both the original and permuted real
configurations are already in PET/ET.  It is **not** by itself the translated
compact-support theorem, because positive-time translation does not transport
Jost/ET membership:

```lean
theorem bvt_F_extendF_perm_pointwise_of_positive_distinct
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (x : NPointDomain d n)
    (hxV : x ∈ V)
    (hpos : ∀ k : Fin n, 0 < x k 0)
    (hdistinct : ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.realEmbed (fun k => x (σ k))) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
```

Proof sketch for the pointwise theorem:

1. Choose the sorted order `τ` of the positive, pairwise-distinct time
   coordinates of `x`.
3. Because the strict inequalities and positivity are open, choose a real-open
   neighborhood `Vx ⊆ V` on which the same `τ` keeps every point in
   `EuclideanOrderedPositiveTimeSector τ`.
4. Apply the sector-local branch-envelope theorem on `Vx`.
5. Apply `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` on
   `Vx`, using the OS Euclidean compact-test equality transported by
   `bvt_F_perm`.
6. Specialize the resulting real-edge equality at `x`.

After the selected translated-PET repair and the corresponding TPET pointwise
positive-sector theorem are available, package the compact pairing theorem.
The theorem statement below is still the desired raw `extendF` compact pairing
on the original PET-controlled support, but its proof must pass through
translated-PET values during the positive-time translation step:

```lean
theorem bvt_F_distributionalEOW_permBranch_from_euclideanEdge_translatedSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (σ k))) * φ x
      =
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- 1. Rewrite the raw `extendF` values on the original support as
  --    `bvt_F_on_translatedPET`, using `bvt_F_on_translatedPET_eq_on_PET`
  --    and the hypotheses `hV_ET`, `hV_permET`.
  -- 2. Choose a uniform `A` from compactness of `tsupport φ`.
  -- 3. Change variables by `positiveTimeTranslate A`, using the checked
  --    `timeShiftSchwartzNPoint` support lemmas.
  -- 4. Use `bvt_F_on_translatedPET_translation_invariant` to move the TPET
  --    values between the original and translated real configurations.
  -- 5. Apply the positive-time, pairwise-distinct TPET pointwise theorem a.e.
  --    on the translated support.
  -- 6. Remove time-tie walls with `ae_pairwise_distinct_timeCoords` and finish
  --    by `integral_congr_ae`.
```

This route avoids non-Schwartz indicators entirely.  Time-tie walls are removed
only by `integral_congr_ae` using the finite-union null theorem.  Sector choices
are made locally around each a.e. point, not by multiplying the test by sector
indicator functions.

The currently missing theorem before this compact package is implementation-ready
is the TPET pointwise positive-sector version:

```lean
theorem bvt_F_on_translatedPET_perm_pointwise_of_positive_distinct
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (hpairwiseJost :
      ∀ i j : Fin n, i ≠ j →
        MinkowskiSpace.IsSpacelike d (fun μ => x i μ - x j μ))
    (hpos : ∀ k : Fin n, 0 < x k 0)
    (hdistinct : ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0)
    (hx_tpet : BHW.realEmbed x ∈ TranslatedPET d n)
    (hxσ_tpet : BHW.realEmbed (fun k => x (σ k)) ∈ TranslatedPET d n) :
    bvt_F_on_translatedPET OS lgc n
        (BHW.realEmbed (fun k => x (σ k))) hxσ_tpet =
      bvt_F_on_translatedPET OS lgc n (BHW.realEmbed x) hx_tpet
```

This statement uses the translation-invariant, pairwise-difference Jost
condition, not the absolute `BHW.JostSet`, because the latter is not preserved
by uniform time translation.  Its proof is the sector-local branch-envelope
argument: choose the sorted positive sector, use the Wick-section identity on a
small real-open neighborhood, and identify the resulting branch values with the
selected translated-PET values via the witness supplied by
`bvt_F_on_translatedPET`.

The older finite-sector export can remain as a fallback theorem slot, but it
should be secondary to the translated-compact-support theorem above:

```lean
theorem bvt_F_distributionalEOW_permBranch_from_euclideanEdge_sectorDecomp
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) :
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (σ k))) * φ x
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- Fallback route only: split the translated compact pairing into finitely
  -- many ordered positive-time sectors plus the time-tie/null-boundary pieces.
  -- On each sector, apply the sector-local branch envelope and the local
  -- Wick-section identity theorem.  The tie walls require a null-set /
  -- integrable-zero lemma or a smooth sector partition; do not use raw
  -- indicator functions as Schwartz tests.
```

With the sector-local envelope theorem, the sector-decomposition export, and
the local Wick-section identity theorem, the proof of
`bvt_F_distributionalEOW_permBranch_from_euclideanEdge` becomes mechanical:

1. If `V = ∅`, prove both sides are zero from
   `tsupport φ ⊆ ∅`.
2. Otherwise obtain `⟨U, F_id, F_perm, ...⟩` from the branch-envelope theorem.
3. Apply
   `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` to
   `F_id` and `F_perm`, using `hEuclid` rewritten by the two Wick-edge
   equations from the envelope.
4. Specialize the resulting `Set.EqOn F_id F_perm U` at
   `BHW.realEmbed x` for each `x ∈ V`, and rewrite by the two real-edge
   equations from the envelope.
5. Convert that pointwise equality on `V` to the compact-test integral equality:
   outside `tsupport φ`, the factor `φ x` is zero; inside `tsupport φ`, use
   `hφ_tsupport : tsupport φ ⊆ V`.

This leaves no hidden raw-boundary continuity assumption.  The only continuity
used in the conversion from distributional equality to pointwise equality is
continuity of holomorphic functions on the interior domain `U`, exactly as in
the checked `OSToWightmanTubeIdentity` proof.

Equivalently, package this as `bvt_F_hasPermutationEdgeDistributionEquality`
as compact-test pairing equality.  Then the checked theorem
`BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality` converts this compact
edge pairing equality to pointwise equality on `V`.

The `bvt_W` theorem below is only a compatibility adapter after the direct
branch equality has been proved.  It is useful for comparing with the private
hLC proof, but it should not be treated as the hard theorem-2 core:

```lean
theorem bvt_W_perm_invariant_on_compactJostOverlap_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (σ : Equiv.Perm (Fin n))
      (V : Set (NPointDomain d n)),
      IsOpen V →
      (∀ x ∈ V, x ∈ BHW.JostSet d n) →
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) →
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) →
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      bvt_W OS lgc n (BHW.permuteSchwartz (d := d) σ⁻¹ φ) =
      bvt_W OS lgc n φ := by
  -- Apply `bvt_F_extendF_perm_edgeDistribution_eq_from_OS`, change variables,
  -- and use boundary recovery to identify the two branch distributions with
  -- `bvt_W OS lgc n φ` and
  -- `bvt_W OS lgc n (BHW.permuteSchwartz σ⁻¹ φ)`.
```

Do not replace this by a simple adjacent-swap induction over a global
`tsupport ⊆ JostSet` theorem unless every intermediate permutation is supplied
with its transported real-open ET/permuted-ET overlap.  The local branch theorem
above is the exact compact-support hypothesis the public `SCV.eqOn_open...`
spine needs.

Its proof must be documented as the following concrete sublemmas:

```lean
def BHW.permuteZeroDiagonalSchwartz
    (σ : Equiv.Perm (Fin n)) (f : ZeroDiagonalSchwartz d n) :
    ZeroDiagonalSchwartz d n := ...

@[simp] theorem BHW.permuteZeroDiagonalSchwartz_apply
    (σ : Equiv.Perm (Fin n)) (f : ZeroDiagonalSchwartz d n)
    (x : NPointDomain d n) :
    (BHW.permuteZeroDiagonalSchwartz (d := d) σ f).1 x =
      f.1 (fun k => x (σ k))

theorem BHW.jostSet_disjoint_coincidenceLocus :
    Disjoint (BHW.JostSet d n) (CoincidenceLocus d n)

theorem zeroDiagonal_of_tsupport_subset_jostOverlap
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    VanishesToInfiniteOrderOnCoincidence φ

theorem bvt_F_euclidean_perm_branch_pairing_eq_from_E3
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x (σ k))) * φ x
      =
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x

theorem bvt_F_acrOne_perm_branches_have_common_euclidean_edge
    ... :
    -- package the previous equality as equality of the two ACR(1) branch
    -- boundary distributions on the Euclidean edge.

theorem bvt_F_perm_branch_distribution_eq_on_jostOverlap_from_OS
    ... :
    -- many-variable EOW / totally-real identity transfers the common Euclidean
    -- edge distribution to the real-open Jost overlap `V`.

theorem bvt_W_perm_eq_of_branch_distribution_eq_on_jostOverlap
    ... :
    -- use `tendsto_extendF_boundary_integral_of_hasCompactSupport_ET` and
    -- `bvt_boundary_values` for `φ` and `BHW.permuteSchwartz σ⁻¹ φ`.
```

The proof transcript for the branch theorem should then be:

1. Set `F := bvt_F OS lgc n`.
2. From `hφ_tsupport : tsupport φ ⊆ V`, obtain
   `hφ_zero : VanishesToInfiniteOrderOnCoincidence φ` using
   `BHW.jostSet_disjoint_coincidenceLocus`.
3. Form the honest Euclidean test
   `φZ : ZeroDiagonalSchwartz d n := ⟨φ, hφ_zero⟩`.
4. Use `OS.E3_symmetric` on `φZ` and
   `BHW.permuteZeroDiagonalSchwartz σ⁻¹ φZ`; rewrite both sides with
   `bvt_euclidean_restriction`; use `BHW.integral_perm_eq_self` to obtain the
   Euclidean branch pairing equality

   ```lean
   ∫ x, F (fun k => wickRotatePoint (x (σ k))) * φ x =
   ∫ x, F (fun k => wickRotatePoint (x k)) * φ x
   ```

   The inverse permutation in `permuteZeroDiagonalSchwartz σ⁻¹` is deliberate:
   after the change of variables, it produces the branch
   `x ↦ F (wickRotatePoint (x ∘ σ))`, matching the left trace
   `extendF F (realEmbed (x ∘ σ))`.

5. Feed that equality, the selected `bvt_F_acrOne_package`, and the
   many-variable EOW/totally-real identity theorem into the branch theorem

   ```lean
   theorem bvt_F_extendF_perm_edgeDistribution_eq_from_OS
       ... :
       ∫ x : NPointDomain d n,
           BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
         =
       ∫ x : NPointDomain d n,
           BHW.extendF F (BHW.realEmbed x) * φ x
   ```

This directly supplies the `hEdge` input for
`BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality`.  No difference-form
rewrite is needed in the uniqueness adapter.

The optional `bvt_W` compatibility adapter then continues:

6. Set `φσ := BHW.permuteSchwartz σ⁻¹ φ` and use the change-of-variables
   identity already present in the private proof:

   ```lean
   ∫ x, BHW.extendF F (BHW.realEmbed x) * φσ x =
   ∫ x, BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
   ```

7. Recover both Wightman boundary values with
   `tendsto_extendF_boundary_integral_of_hasCompactSupport_ET` and
   `bvt_boundary_values`.  The ET support for `φ` is `hV_ET`; the ET support
   for `φσ` is transported from `hV_permET`.
8. Conclude

   ```lean
   bvt_W OS lgc n φσ = bvt_W OS lgc n φ
   ```

   This is a useful consistency theorem, but it is no longer the preferred
   input for the pointwise real-open proof.

This is the precise place where the OS-II correction matters: the proof must use
the repaired many-variable `bvt_F` / ACR(1) branch package.  It must not invoke a
one-variable Lemma-8.8-style continuation or a hidden global locality theorem.

This subpacket is now the primary proof-doc gap.  It is smaller and more
OS-faithful than the finite-height endpoint-symmetry problem, but it is still
not a one-line instantiation of any checked production theorem.  The exact
missing proof is the OS-side branch-distribution equality
`bvt_F_extendF_perm_edgeDistribution_eq_from_OS`, packaged afterward as
`bvt_F_hasPermutationEdgeDistributionEquality`, plus the public exposure of the
already-present `extendF`-overlap/PET-extension spine.

Then the public theorem can avoid the overstrong private finite-shell frontier:

```lean
theorem bvt_locally_commutative_from_symmetric_PET_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  -- obtain `Fext` from `bvt_F_symmetric_PET_extension`;
  -- apply `bv_local_commutativity_transfer_of_symmetric_PET_boundary`
  -- with `F := bvt_F OS lgc n` and `W_n := bvt_W OS lgc n`.
```

If we deliberately keep the current finite-height consumer
`bv_local_commutativity_transfer_of_swap_pairing`, then the stronger theorem
`bvt_F_swapCanonical_pairing` still requires the symmetric-envelope or verified
slice-reflection packet below.  But that packet should now be treated as the
price of retaining an overstrong sufficient condition, not as the only OS-route
path to theorem 2.

The slice reduction remains a candidate way to prove the stronger
`exists_reduced_canonicalRealSwap_symmetricEnvelope`, but it is not currently
an implementation-ready route.  It becomes valid only after endpoint-hit lemmas
show that the slice really reaches the two finite shell points above and
produces the reflection/symmetry map `R`.  The candidate packet is:

```lean
def selectedPairTimeSlice
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) :
    ℂ → ReducedNPointConfig d m :=
  -- vary only the complex relative-time normal to the selected pair, keeping
  -- the reduced spatial data and all spectator reduced coordinates fixed.
  -- The exact Lean definition should be written using
  -- `(realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)` so the
  -- pair coordinates are changed in absolute coordinates and then pushed back
  -- through `reducedDiffMap`.

theorem selectedPairTimeSlice_real_interval_spacelike
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t| < δ →
        selectedPairTimeSlice (d := d) m i j ξ (t : ℂ) ∈
          reducedSpacelikeSwapEdge (d := d) m i j := by
  -- openness of the spacelike cone around the selected pair difference.

theorem selectedPairTimeSlice_upper_mem_reducedForwardTube
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) (hε : 0 < ε) :
    selectedPairTimeSlice (d := d) m i j ξ (Complex.I * ε) ∈
      BHW.ReducedForwardTubeN d m := by
  -- canonical ordering gives positive imaginary relative time in the selected
  -- normal direction, with spectator imaginary differences fixed in the
  -- canonical product cone.

theorem selectedPairTimeSlice_lower_mem_swapPulledForwardTube
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) (hε : 0 < ε) :
    selectedPairTimeSlice (d := d) m i j ξ (-Complex.I * ε) ∈
      {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
        BHW.ReducedForwardTubeN d m} := by
  -- swapped ordering gives the opposite imaginary normal for the selected pair.

theorem selectedPairTimeSlice_boundary_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t| < δ →
        bvt_F_reduced (d := d) OS lgc m
          (selectedPairTimeSlice (d := d) m i j ξ (t : ℂ))
        =
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
            (selectedPairTimeSlice (d := d) m i j ξ (t : ℂ))) := by
  -- combine `selectedPairTimeSlice_real_interval_spacelike` with
  -- `bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge`.

theorem selectedPairTimeSlice_hits_canonicalReducedShell
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) :
    selectedPairTimeSlice (d := d) m i j ξ (Complex.I * ε) =
      canonicalReducedShell (d := d) m ξ ε := by
  -- Required endpoint lemma.  If this equality is false for the chosen slice,
  -- the slice route is not the right bridge.

theorem selectedPairTimeSlice_hits_realPermutedCanonicalReducedShell
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) :
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
      (selectedPairTimeSlice (d := d) m i j ξ (-Complex.I * ε))
    =
      realPermutedCanonicalReducedShell (d := d) m i j ξ ε := by
  -- Required endpoint lemma.  This is the missing check that the lower branch
  -- endpoint is the real-permuted canonical shell, not just some swapped
  -- one-variable normal perturbation.

theorem selectedPairTimeSlice_connected_domain_to_all_heights
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Ω : Set ℂ,
      IsOpen Ω ∧ IsPreconnected Ω ∧
      Complex.I * ε ∈ Ω ∧ -Complex.I * ε ∈ Ω ∧
      (∀ τ ∈ Ω, selectedPairTimeSlice (d := d) m i j ξ τ ∈
        (BHW.ReducedForwardTubeN d m) ∪
        {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
          BHW.ReducedForwardTubeN d m} ∪
        {ζ | ∃ ξ₀ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
          ζ = fun k μ => (ξ₀ k μ : ℂ)}) := by
  -- Required propagation lemma.  Local 1D EOW near the real interval is not
  -- enough unless the continuation domain connects the local wedge to the
  -- requested finite height `ε`.

theorem selectedPairTimeSlice_reflection_symmetry
    (Ω : Set ℂ) (H : ℂ → ℂ) (r : ℂ → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    IsOpen Ω →
    IsConnected Ω →
    DifferentiableOn ℂ H Ω →
    DifferentiableOn ℂ r Ω →
    (∀ z ∈ Ω, r z ∈ Ω) →
    Complex.I * ε ∈ Ω →
    r (Complex.I * ε) = -Complex.I * ε →
    (∃ a b : ℝ, a < b ∧
      Set.Ioo a b ⊆ {t : ℝ | (t : ℂ) ∈ Ω} ∧
      (∀ t : ℝ, t ∈ Set.Ioo a b → H (r (t : ℂ)) = H (t : ℂ))) →
    H (-Complex.I * ε) = H (Complex.I * ε) := by
  -- This is the slice analogue of the reduced envelope symmetry map `R`.
  -- Connectedness of the slice domain alone is not enough: a holomorphic
  -- function is not constant on connected domains.  The proof is a
  -- one-dimensional totally-real identity theorem applied to
  -- `fun τ => H (r τ) - H τ`, followed by evaluation at `Complex.I * ε`.

theorem reduced_local_EOW_canonicalRealSwap_from_verified_slice
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ))
    (ε : ℝ) (hε : 0 < ε) :
    bvt_F_reduced (d := d) OS lgc m
      (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (selectedPairTimeSlice (d := d) m i j ξ (-Complex.I * ε)))
    =
    bvt_F_reduced (d := d) OS lgc m
      (selectedPairTimeSlice (d := d) m i j ξ (Complex.I * ε)) := by
  -- Define one-variable functions
  -- `f_plus τ := bvt_F_reduced ... (selectedPairTimeSlice ... τ)`
  -- on the upper half-plane and
  -- `f_minus τ := bvt_F_reduced ... (permOnReducedDiff swap
  --   (selectedPairTimeSlice ... τ))`
  -- on the lower half-plane.
  -- Apply `edge_of_the_wedge_1d` on the real interval from
  -- `selectedPairTimeSlice_boundary_eq`.
  -- Then prove the reflected slice identity, not mere connectedness, on the
  -- connected upper/lower continuation domain.  Use
  -- `selectedPairTimeSlice_reflection_symmetry` to compare the values at the
  -- two endpoint parameters.
  -- Finally rewrite the two endpoints using
  -- `selectedPairTimeSlice_hits_canonicalReducedShell` and
  -- `selectedPairTimeSlice_hits_realPermutedCanonicalReducedShell`.
```

This candidate slice packet is useful only if the endpoint, connectedness, and
reflection-symmetry lemmas above are true.  Until then, the implementation-ready
statement remains the broader symmetric-envelope seam
`exists_reduced_canonicalRealSwap_symmetricEnvelope`, followed by
`reduced_connectedEnvelope_symmetry_transport`.  In particular, theorem 2 as a
whole is not 100% Lean-ready yet, although the reduced algebraic packet
preceding this analytic seam is ready for implementation.

Then the absolute pointwise theorem is only an adapter:

1. set `m := n - 1` after eliminating the vacuous `n = 0` case;
2. factor both absolute shell values through `bvt_F_reduced`;
3. rewrite their reduced imaginary directions using the two direction lemmas;
4. rewrite the support hypothesis with `reducedPairDiff_reducedDiffMapReal`;
5. apply
   `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`.

## 7. Exact proof decomposition for theorem 2

After the candidate-symmetry audit, the recommended Lean proof should follow
the OS-I-faithful boundary route first.

1. Publicize the non-circular `extendF` overlap/PET-extension spine currently
   present only as private support in `PermutationFlow.lean`.
2. Prove `bvt_F_hasPermutationEdgeDistributionEquality`, the OS-side real-open
   Jost edge distribution equality replacing the hLC input in the current BHW
   theorem.
3. Use that edge equality to prove `bvt_F_extendF_perm_overlap`, i.e. the
   `extendF` equality on every ET/permuted-ET overlap needed by
   `bargmann_hall_wightman_theorem_of_extendF_perm`.
4. Prove or expose the OS-side PET extension theorem
   `bvt_F_symmetric_PET_extension`.
5. Prove the generic Jost/BHW boundary transfer theorem
   `bv_local_commutativity_transfer_of_symmetric_PET_boundary`.
6. Replace the proof of `bvt_locally_commutative` so it calls the boundary
   transfer theorem directly, using `bvt_F`, `bvt_W`, `bvt_boundary_values`,
   and the PET extension from step 4.
7. Leave `bvt_F_swapCanonical_pairing` as a private overstrong sufficient
   theorem, or retire it from the active dependency path if no other consumer
   needs finite-height shell equality.

This route keeps the proof aligned with OS I Section 4.5: locality is a
statement about boundary distributions of a symmetric BHW continuation, not
about equality of every positive-height canonical shell integral.

If we decide to retain the current finite-height consumer anyway, then the
fallback proof order is:

1. Prove the algebraic reduced-shell packet:
   `bvt_F_reduced`, `bvt_F_eq_bvt_F_reduced_reducedDiffMap`, the canonical
   direction lemmas, `reducedPairDiff_reducedDiffMapReal`,
   `bvt_F_reduced_permOnReducedDiff`, and
   `permOnReducedDiff_swap_permutedCanonicalDirection`.
2. Prove the reduced permutation adapter
   `bvt_F_reduced_permutedDirection_to_realPermutedCanonical`.
3. Prove the reduced local-edge theorem
   `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike`.
   This factors through `reducedSpacelikeSwapEdge`,
   `bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge`, branch
   holomorphicity, and `reduced_local_EOW_canonicalRealSwap`.
4. Derive
   `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`
   as a short adapter from the previous two steps.
5. Use the reduced packet to prove
   `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike`.
6. Use `bvt_F_perm` to prove
   `bvt_F_swapCanonical_pointwise_of_spacelike`.
7. Use measure-preserving coordinate swap and support-zero outside `tsupport f`
   to prove `bvt_F_swapCanonical_pairing_from_transposition_pointwise`.
8. Feed the result into
   `bv_local_commutativity_transfer_of_swap_pairing`.

The fallback should not be started until the symmetric-envelope or verified
slice-reflection packet is implementation-ready.  The theorem should not be
attacked by opening a new permutation-continuation front in the middle of
`OSToWightmanBoundaryValues.lean`; the generic PET/Jost machinery belongs in
the BHW/SCV layer.

## 8. Historical docs that are no longer frontier guidance

The following docs are historical and should not be used as primary route
guidance for theorem 2:

1. `docs/edge_of_the_wedge_proof_plan.md`
2. `docs/edge_of_the_wedge_gap_analysis.md`

Both were written before the theorem

```lean
SCV.edge_of_the_wedge_theorem
```

was proved. They are still useful for mathematical context, but they do not
describe the current production frontier on `main`.

## 9. Exact theorem-name dictionary for theorem 2

The later proof should distinguish checked-present support surfaces from the
new theorem-2 closure slots.

Checked-present surfaces to use only where their hypotheses are non-circular:

1. `bvt_F_perm`
2. `bv_local_commutativity_transfer_of_swap_pairing`
3. `exists_real_open_nhds_adjSwap`
4. `boundary_function_continuous_forwardTube_of_flatRegular`
5. `edge_of_the_wedge`
6. `SCV.edge_of_the_wedge_theorem`
7. `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen`
8. `bvt_F_acrOne_package`

Checked-present surfaces that are comparison/supplier context but are not
direct final theorem-2 calls on `W := bvt_W OS lgc`:

1. `W_analytic_swap_boundary_pairing_eq`
2. `analytic_extended_local_commutativity`
3. `analytic_boundary_local_commutativity_of_boundary_continuous`
4. `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`

Primary planned theorem-2 closure slots:

1. `bvt_F_restrictedLorentzInvariant_forwardTube`
2. `bvt_F_complexLorentzInvariant_forwardTube`
3. `BHW.HasPermutationEdgeDistributionEquality`
4. `bvt_F_distributionalEOW_permBranch_from_euclideanEdge`
5. `bvt_F_permBranchEnvelope_on_jostOverlap_from_ACR_and_BHW`
6. `bvt_F_extendF_adjacentEdgeDistribution_eq_from_OS`
7. `bvt_F_selectedAdjacentPermutationEdgeData_from_OS`
8. `SelectedAdjacentPermutationEdgeData`
9. `bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`
10. `bvt_selectedPETBranch`
11. `bvt_selectedPETBranch_holomorphicOn_sector`
12. `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`
13. `BHW.extendF_pet_branch_independence_of_adjacent`
14. `bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData`
15. `BHW.F_permutation_invariance_of_petBranchIndependence`
16. `BHW.fullExtendF_well_defined_of_petBranchIndependence`
17. `BHW.bargmann_hall_wightman_theorem_of_adjacentBranchEquality`
18. `bvt_F_symmetric_PET_extension_of_adjacentEdgeData`
19. `BHW.permuteSchwartz`
20. `BHW.permute_support_jost`
21. `BHW.permute_tsupport_jost`
22. `BHW.permuteSchwartz_hasCompactSupport`
23. `BHW.integral_perm_eq_self`
24. `bvt_W_perm_invariant_on_compactJostOverlap_from_OS`
25. `bv_local_commutativity_transfer_of_symmetric_PET_boundary`
26. `bvt_locally_commutative_from_symmetric_PET_boundary`

The following older slot names are no longer primary construction targets:

1. `BHW.jostWitness_exists_for_perm_overlap`;
2. `BHW.isConnected_permForwardOverlapSet_for_perm`;
3. `bvt_F_extendF_perm_edgeDistribution_eq_from_OS`;
4. `bvt_F_hasPermutationEdgeDistributionEquality`;
5. `bvt_F_extendF_perm_overlap`.

They may remain as conditional compatibility lemmas if their hypotheses are
explicitly supplied, but theorem 2 must not try to construct arbitrary
all-permutation real edge witnesses.  General permutation behavior must be
exported through adjacent edge data plus the PET monodromy / single-valuedness
theorem.

Do not insert `bvt_F_hasFlatRegularRepr` or
`bvt_F_boundary_continuous_at_real_support` into the primary list.  Those names
would require raw real-trace regularity of the Wightman boundary value and are
too strong for the theorem-2 OS route unless replaced by a sharply restricted
support theorem.  The primary bridge is the `extendF` equality on real Jost
edge points, not continuity of `bvt_F` on all real boundary points.

Fallback finite-height closure slots, needed only if the current overstrong
`bvt_F_swapCanonical_pairing` consumer is retained:

1. `choose_real_open_edge_for_adjacent_swap`
2. `swapped_support_lies_in_swapped_open_edge`
3. `bvt_F_hasFlatRegularRepr`
4. `bvt_F_boundary_continuous_at_real_support`
5. `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
6. `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
7. `canonical_adjacentSwap_shell_mem_EOW_domain`
8. `bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike`
9. `bvt_F_adjacentSwapCanonical_pointwise_of_spacelike`
10. `bvt_F_adjacentSwapCanonical_pairing_from_pointwise`
11. `bvt_F_reduced`
12. `bvt_F_eq_bvt_F_reduced_reducedDiffMap`
13. `canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC`
14. `permutedCanonicalForwardDirection_reducedDiff_eq`
15. `reducedDiffMap_canonicalShell_eq`
16. `reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq`
17. `reducedPairDiff_reducedDiffMapReal`
18. `bvt_F_reduced_permOnReducedDiff`
19. `permOnReducedDiff_swap_permutedCanonicalDirection`
20. `bvt_F_reduced_permutedDirection_to_realPermutedCanonical`
21. `reducedSpacelikeSwapEdge`
22. `isOpen_reducedSpacelikeSwapEdge`
23. `bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge`
24. `bvt_F_reduced_holomorphicOn_reducedForwardTube`
25. `bvt_F_reduced_holomorphicOn_swapPulledForwardTube`
26. `reduced_local_EOW_canonicalRealSwap`
27. `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike`
28. `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`
29. `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike`
30. `bvt_F_swapCanonical_pointwise_of_spacelike`
31. `bvt_F_swapCanonical_pairing_from_transposition_pointwise`

If a later proof jumps from checked BHW support context directly to
`bvt_F_swapCanonical_pairing` without either the primary boundary-level
PET/Jost route or the full fallback finite-shell packet above, the
implementation is drifting back toward a stale or circular locality plan.

## 10. Do not do this

1. Do not reintroduce edge-of-the-wedge as an axiom or a missing theorem.
2. Do not mix theorem 2 with theorem 3 positivity reductions.
3. Do not claim locality directly from permutation invariance of `bvt_F` alone;
   the real issue is boundary pairing and ET/Jost support geometry.
4. Do not use the historical edge-of-the-wedge gap notes as if they still
   described `main`.
5. Do not hide the finite canonical-shell interchange theorem inside the closing
   `sorry` if the overstrong finite-height consumer is retained.
6. Do not instantiate a checked BHW theorem with
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)` while proving theorem 2.
7. Do not use boundary-value recovery as if it proved finite-`ε` canonical
   shell equality.
8. Do not force the OS I locality proof through finite-shell equality if the
   boundary-level PET/Jost transfer theorem is available.

## 11. Minimal Lean pseudocode for the full closure

Primary PET-extension construction:

```lean
theorem bvt_F_selectedAdjacentPermutationEdgeData_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SelectedAdjacentPermutationEdgeData OS lgc n := by
  -- Construct only adjacent-swap edge data:
  --   * adjacent overlap connectedness;
  --   * adjacent real-open edge witness;
  --   * compact-test edge equality from OS Euclidean symmetry and
  --     distributional EOW.
  -- Do not construct arbitrary all-permutation real edge witnesses.

theorem bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    bvt_selectedPETBranch OS lgc n π z =
      bvt_selectedPETBranch OS lgc n ρ z := by
  exact
    BHW.extendF_pet_branch_independence_of_adjacent
      (d := d) n (bvt_F OS lgc n)
      (bvt_F_holomorphic (d := d) OS lgc n)
      (bvt_F_restrictedLorentzInvariant_forwardTube (d := d) OS lgc n)
      (by
        intro π i hi z hzπ hzπswap
        exact bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
          (d := d) OS lgc n hEdge π i hi z hzπ hzπswap)
      π ρ z hzπ hzρ

theorem bvt_F_symmetric_PET_extension_of_adjacentEdgeData
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n) :
    ∃ Fext : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fext (BHW.PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, Fext z = bvt_F OS lgc n z) ∧
      (∀ (Λ : ComplexLorentzGroup d) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (BHW.complexLorentzAction Λ z) = Fext z) ∧
      (∀ (σ : Equiv.Perm (Fin n)) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (fun k => z (σ k)) = Fext z) := by
  obtain ⟨Fext, hFext_holo, hFext_agree, hFext_lorentz, hFext_perm, _huniq⟩ :=
    BHW.bargmann_hall_wightman_theorem_of_adjacentBranchEquality
      (d := d) n (bvt_F OS lgc n)
      (bvt_F_holomorphic (d := d) OS lgc n)
      (bvt_F_restrictedLorentzInvariant_forwardTube (d := d) OS lgc n)
      (bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData
        (d := d) OS lgc n hEdge)
  exact ⟨Fext, hFext_holo, hFext_agree, hFext_lorentz, hFext_perm⟩
```

The old arbitrary-permutation pseudocode using
`bvt_F_extendF_perm_edgePairing_eq_from_OS`,
`BHW.jostWitness_exists_for_perm_overlap`, and
`BHW.isConnected_permForwardOverlapSet_for_perm` is no longer the primary
route.  Those names ask for all-permutation real overlap data and are too
strong as construction targets.  The primary construction is adjacent edge data
plus the PET monodromy theorem
`BHW.extendF_pet_branch_independence_of_adjacent`.

Primary boundary-level closure:

```lean
private theorem bvt_locally_commutative_boundary_route
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsep hswap
  have hEdge : SelectedAdjacentPermutationEdgeData OS lgc n :=
    bvt_F_selectedAdjacentPermutationEdgeData_from_OS (d := d) OS lgc n
  obtain ⟨Fext, hFext_holo, hFext_agree, hFext_lorentz, hFext_perm⟩ :=
    bvt_F_symmetric_PET_extension_of_adjacentEdgeData (d := d) OS lgc n hEdge
  exact
    bv_local_commutativity_transfer_of_symmetric_PET_boundary
      (d := d) n
      (bvt_W OS lgc n)
      (bvt_F OS lgc n)
      Fext
      (bvt_F_holomorphic (d := d) OS lgc n)
      (bvt_boundary_values (d := d) OS lgc n)
      hFext_holo
      hFext_agree
      hFext_lorentz
      hFext_perm
      i j f g hsep hswap
```

Fallback finite-height closure, only if the current private consumer is kept:

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- All BHW/EOW, open-edge, boundary-continuity, and canonical finite-shell work
  -- is below this frontier theorem. This proof should only consume the
  -- completed arbitrary-transposition finite-shell pairing theorem.
  exact
    bvt_F_swapCanonical_pairing_from_transposition_pointwise
      (d := d) (OS := OS) (lgc := lgc) n i j f g ε hε hsep hswap
```

## 12. Fallback regular-input constructor theorem

This section is retained as a fallback-route audit.  It is useful if we later
decide to prove raw boundary continuity, but it is not part of the primary
OS-I-faithful theorem-2 path.  The primary path runs through
`bvt_F_distributionalEOW_permBranch_from_euclideanEdge`,
`bvt_F_hasPermutationEdgeDistributionEquality`, and the BHW `extendF`
real-Jost edge theorem.  The `bvt_W_perm...` theorem is a compatibility
adapter, not the main bridge.

For the fallback continuity route, the blueprint should still be explicit about
one important fact:

```lean
SCV.hasFourierLaplaceReprRegular_of_boundary_and_growth
```

does **not** exist anywhere in the current repo.

What *does* exist is the downstream package that *consumes*
`HasFourierLaplaceReprRegular`:

1. `boundary_function_continuous_forwardTube_of_flatRegular`,
2. `boundary_value_recovery_forwardTube_of_flatRegular`,
3. `distributional_uniqueness_forwardTube_of_flatRegular`,
4. `polynomial_growth_forwardTube_of_flatRegular`.

So the fallback route should be documented as requiring a new constructor
package, not as a one-line application of an already-existing helper.

The honest fallback theorem-slot inventory is:

```lean
lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap)

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma flatRegular_of_boundary_distribution_and_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
```

The first two are already the theorem shapes the blueprint was using. The third
is the real missing theorem. Only the fourth is an adapter name specialized to
`bvt_F`.

### 12.1. What the constructor proof must look like

The later Lean proof should be documented as:

1. prove holomorphy of the flattened function from `bvt_F_holomorphic`,
2. prove distributional boundary values of the flattened function using the
   existing `bvt_W` boundary package,
3. prove polynomial growth on the flattened tube from the already-constructed
   growth package for `bvt_F`,
4. package those three inputs into a new regular constructor theorem,
5. only then call the forward-tube continuity/recovery theorems.

The critical point is that Step 4 is a real theorem package, not a missing
`simpa`.

### 12.2. Estimated Lean line counts for the regular package

1. flattened boundary-value adapter:
   roughly `25-60` lines.
2. flattened growth adapter:
   roughly `20-50` lines.
3. regular constructor theorem
   `flatRegular_of_boundary_distribution_and_polyGrowth`:
   roughly `60-120` lines if done directly in the flattened SCV language.
4. specialization to `bvt_F_hasFlatRegularRepr`:
   roughly `10-25` lines.

So the honest continuity package here is roughly `115-255` lines, and the
central missing theorem is the regular constructor, not the continuity theorem
itself.

## 13. Correct selected-pair support rewrite

The support hypothesis for the public theorem is still used pointwise, but it
must be rewritten into reduced coordinates rather than upgraded to absolute
extended-tube membership.

The public proof should proceed as follows.

1. During the finite-shell adapter, after the swap change of variables, reduce
   the two absolute shell values through
   `bvt_F_eq_bvt_F_reduced_reducedDiffMap`.
2. Rewrite the reduced real base point by
   `BHW.reducedDiffMapReal (m + 1) d x`.
3. Use `reducedPairDiff_reducedDiffMapReal` to turn the production support
   hypothesis
   `AreSpacelikeSeparated d (x i) (x j)` into the reduced local-edge hypothesis
   for `reducedPairDiff m i j ξ`.
4. Apply
   `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`.
5. Return to the absolute shell statement using the reduced-direction lemmas.

In Lean-style pseudocode:

```lean
theorem reducedPairDiff_reducedDiffMapReal
    (m : ℕ) (i j : Fin (m + 1)) (x : NPointDomain d (m + 1)) :
    reducedPairDiff (d := d) m i j
        (BHW.reducedDiffMapReal (m + 1) d x)
      =
      fun μ => x j μ - x i μ := by
  -- Expand the real difference-coordinate section.  The common basepoint
  -- translation cancels from the pair difference.

theorem bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) →
      bvt_F OS lgc n
        (permutedEtaCanonicalShellOfPerm (d := d) n (Equiv.swap i j) x ε)
      =
      bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- handle `n = 0` by `Fin n` elimination;
  -- set `m := n - 1` and identify `n` with `m + 1`;
  -- factor both sides through `bvt_F_reduced`;
  -- use the canonical/permuted reduced-direction lemmas;
  -- rewrite spacelike separation with `reducedPairDiff_reducedDiffMapReal`;
  -- apply the reduced local-edge theorem.
```

The adjacent `choose_real_open_edge_for_adjacent_swap` package may remain as a
pilot for raw-boundary arguments, but it is not the public selected-pair
finite-shell route.  In particular, do not add a theorem claiming that one
selected spacelike pair implies absolute `ExtendedTube` membership for
`realEmbed x` and `realEmbed (x ∘ Equiv.swap i j)`.

## 14. Exact proof sketch for the finite canonical-shell adapter

The adjacent theorem

```lean
bvt_F_adjacentSwapCanonical_pairing_from_pointwise
```

should not be left as a slogan.  More importantly, the public theorem needs the
general-transposition analogue

```lean
bvt_F_swapCanonical_pairing_from_transposition_pointwise
```

The later Lean proof should make this a named finite-shell adapter.

1. rewrite the left pairing using
   `hswap : g x = f (fun k => x (swap k))`;
2. change variables by the `Equiv.swap i j` coordinate permutation, using the existing
   product-volume measure-preserving reindexing theorem;
3. reduce the integrand equality to the pointwise finite-shell statement
   `bvt_F_swapCanonical_pointwise_of_spacelike`;
4. use the support hypothesis only on `tsupport f`; outside `tsupport f`, the
   `f` factor kills the integrand.

The theorem-slot inventory should therefore be:

```lean
theorem canonical_adjacentSwap_shell_mem_EOW_domain
lemma swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell
theorem bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike
theorem bvt_F_adjacentSwapCanonical_pointwise_of_spacelike
theorem bvt_F_adjacentSwapCanonical_pairing_from_pointwise
def bvt_F_reduced
theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
theorem canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC
theorem permutedCanonicalForwardDirection_reducedDiff_eq
theorem reducedDiffMap_canonicalShell_eq
theorem reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq
theorem reducedPairDiff_reducedDiffMapReal
theorem bvt_F_reduced_permOnReducedDiff
theorem permOnReducedDiff_swap_permutedCanonicalDirection
theorem bvt_F_reduced_permutedDirection_to_realPermutedCanonical
theorem bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike
theorem bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike
theorem bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike
theorem bvt_F_swapCanonical_pointwise_of_spacelike
theorem bvt_F_swapCanonical_pairing_from_transposition_pointwise
```

Estimated Lean size:

1. reduced algebraic shell packet:
   `110-210` lines, mostly definitional expansions of `reducedDiffMap`,
   `safeSection`, `permOnReducedDiff`, and permutation bookkeeping;
2. reduced canonical-real-swap local-edge theorem:
   still unestimated; this is the current hard analytic statement, now reduced
   to canonical imaginary direction and a selected real reduced-basepoint swap;
3. adjacent permuted-eta finite-shell theorem:
   `30-80` lines after the adjacent EOW-domain membership and analytic
   uniqueness surface are available;
4. adjacent pointwise finite-shell theorem:
   `20-60` lines after the EOW-domain membership theorem exists;
5. adjacent pairing adapter from pointwise equality:
   `25-60` lines, mostly measure-preserving reindexing and support-zero
   bookkeeping;
6. arbitrary-transposition pointwise finite-shell theorem:
   `30-90` lines after the reduced local-edge theorem and reduced shell packet
   exist;
7. general transposition pairing adapter:
   `30-70` lines after the pointwise theorem exists, mostly the same
   measure-preserving reindexing and support-zero bookkeeping as the adjacent
   adapter.

So the theorem-2 endgame is reduced finite-shell first: reduced-coordinate
factorization, reduced local-edge comparison, absolute pointwise shell
interchange, pairing integration, and then the direct general-transposition
adapter.

## 15. The forward-Jost / absolute-ET subtlety must stay explicit

The locality blueprint should keep one geometry subtlety visible:

1. `ForwardJostSet d n hd` is defined by a condition on every consecutive
   difference.
2. Absolute `ExtendedTube d n` is likewise a global condition on the whole
   configuration, expressed through the BHW orbit of the forward tube.
3. The theorem-2 locality hypothesis only names one selected pair of indices.
4. Therefore selected-pair spacelike separation is not enough, by itself, to
   put the whole real configuration or its selected transposition in the
   absolute forward-Jost/extended-tube geometry.

This matters most visibly in low-dimensional examples, but it is a general
theorem-shape issue.  The route should not hide it behind convenient names.

### 15.1. What is safe to claim

The docs may safely claim:

1. if the support is already known to lie in an open edge `V` with the required
   ET and swapped-ET embeddings, that edge can feed raw-boundary or adjacent
   pilot arguments;
2. if a stronger support theorem is separately proved that upgrades the
   locality support hypothesis to `ForwardJostSet` membership, then
   `forwardJostSet_subset_extendedTube` can close that stronger route;
3. the fallback finite-shell route does not need either global forward-Jost
   membership or absolute ET-overlap from one pair, because it uses reduced
   difference coordinates and a reduced local-edge theorem;
4. boundary-value recovery identifies the limiting raw boundary distribution;
   it does not replace the finite-shell pointwise interchange proof needed at
   fixed `ε > 0`.

### 15.2. What is not safe to claim

The docs should not claim, without a new stronger hypothesis:

1. one selected-pair spacelike-separation hypothesis automatically implies
   `ForwardJostSet` membership on the whole support;
2. one selected-pair spacelike-separation hypothesis automatically implies
   absolute `ExtendedTube` membership for `realEmbed x`;
3. one selected-pair spacelike-separation hypothesis automatically implies
   absolute `ExtendedTube` membership for
   `realEmbed (fun k => x (Equiv.swap i j k))`;
4. a bubble-sort chain of adjacent swaps is valid under a hypothesis that only
   controls the original selected pair;
5. the `d = 1` case is merely a cosmetic special case of the same argument.

### 15.3. Honest theorem-slot split

The later Lean port should separate three possible routes.

#### Route A: stronger forward-Jost support theorem

```lean
lemma support_mem_forwardJost_of_swap_spacelike
    (f : SchwartzNPoint d n) (i j : Fin n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) :
    ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      x ∈ ForwardJostSet d n hd
```

This is a fallback strengthening only.  It is strongest, but also most
delicate, because the conclusion is about all consecutive differences.

#### Route B: adjacent open-edge pilot

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHWCore.ExtendedTube d n)
```

This route may remain useful for adjacent raw-boundary statements and for
testing the BHW edge machinery.  It is not the public selected-transposition
finite-shell route.

#### Route C: fallback reduced finite-shell route

```lean
theorem bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (m : ℕ) (i j : Fin (m + 1))
      (ξ : NPointDomain d m) (ε : ℝ), 0 < ε →
      MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) →
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
                Complex.I))
      =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)
```

This is the honest fallback route if we deliberately keep the current private
finite-height consumer `bvt_F_swapCanonical_pairing`.  It expresses the
selected-pair seam in reduced coordinates, with the imaginary direction
normalized back to the canonical one.  It is no longer the recommended first
route to theorem 2, because the BHW/PET boundary route can prove locality by a
more direct permutation-edge theorem for `extendF`.

### 15.4. Recommended implementation order

The next Lean implementation should follow the primary BHW/PET boundary route:

1. prove the adjacent branch-envelope theorem for the selected `bvt_F`;
2. export the arbitrary-permutation branch envelope through the BHW/PET
   permutation-flow spine;
3. prove `bvt_F_distributionalEOW_permBranch_from_euclideanEdge`;
4. package the result as `bvt_F_hasPermutationEdgeDistributionEquality`;
5. apply `BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality`;
6. add the boundary-transfer theorem that proves
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)` from this PET boundary package.

Route C should be implemented only if that primary route is blocked or if we
choose to retain the current overstrong finite-shell consumer.

1. Implement the reduced algebraic packet:
   `bvt_F_reduced`, reduced factorization through `reducedDiffMap`, direction
   reduction for canonical and permuted-canonical shells, and
   `reducedPairDiff_reducedDiffMapReal`.
2. Implement the reduced permutation algebra:
   `bvt_F_reduced_permOnReducedDiff`,
   `permOnReducedDiff_swap_permutedCanonicalDirection`, and
   `bvt_F_reduced_permutedDirection_to_realPermutedCanonical`.
3. Finish or further document the reduced local-edge theorem
   `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike`.
4. Derive
   `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`
   from the reduced permutation algebra and canonical-real-swap theorem.
5. Prove the absolute adapter
   `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike` by
   factoring both sides through the reduced theorem.
6. Prove `bvt_F_swapCanonical_pointwise_of_spacelike` using `bvt_F_perm` and
   the shell algebra.
7. Prove the pairing theorem by swap change-of-variables and support-zero
   bookkeeping.

Route B can be kept as an adjacent pilot, but should not block the primary
BHW/PET boundary route.  Route A should only be revived if the stronger
forward-Jost theorem is genuinely proved under the current theorem surface.

### 15.5. Estimated Lean size after the correction

1. Reduced algebraic packet:
   `110-210` lines, mostly definitional calculation, `safeSection`
   bookkeeping, and existing `DifferenceCoordinatesReduced` permutation
   lemmas.
2. Reduced canonical-real-swap local-edge theorem:
   not yet line-estimated; this remains the single hard analytic seam.
3. Reduced permuted-direction adapter:
   `20-50` lines after the reduced permutation algebra compiles.
4. Absolute finite-shell adapter from the reduced theorem:
   `30-90` lines after the reduced packet compiles.
5. Pairing adapter:
   `30-70` lines after the pointwise shell theorem exists.

The docs should therefore treat the branch-envelope theorem and the local
distributional Wick-section identity as the next proof-doc gaps for the primary
route.  The reduced canonical-real-swap local-edge theorem is the next gap only
on the fallback finite-shell route.
