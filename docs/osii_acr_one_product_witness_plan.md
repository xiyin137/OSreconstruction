# OS II ACR(1) Product Witness Plan

Purpose: active proof plan for closing
`exists_acrOne_productTensor_witness` in
`OSToWightman.lean`.

This is not a replacement route. It records the OS II Chapter IV/V/VI route that
must be followed before editing the production proof body.

## Current Blocker

The remaining production `sorry` asks, for `k >= 2`, for a scalar witness

```lean
S_prod : (Fin k -> Fin (d + 1) -> C) -> C
```

with:

1. holomorphy on `AnalyticContinuationRegion d k 1`,
2. Euclidean reproduction on zero-diagonal product tensors,
3. permutation invariance,
4. common complex translation invariance,
5. reflected canonical reality,
6. polynomial growth on `ACR(1)`.

This theorem is upstream of `full_analytic_continuation_with_acr_symmetry_growth`
and therefore upstream of `bvt_F`. Any proof using `bvt_F` or a boundary value
constructed from `full_analytic_continuation...` is circular.

## Paper Route

OS II IV.2 states that Wightman reconstruction proceeds by:

1. Theorem 4.1 `(A0)`: real analyticity of the difference-variable Green
   functions.
2. V.1: one-variable semigroup continuations, logarithmic coordinates, and
   Malgrange-Zerner gluing on the convex envelope.
3. V.2: `(A_N)/(P_N)` induction. The base `(P0)` is not tautological:
   distributional equation `(5.2)` is smeared by positive-side
   delta-sequences and then passed to point values.
4. VI.1/VI.2: only after continuation, use the linear growth condition to prove
   the polynomial bounds.

The OS II text is explicit: `(P0)` follows from `(A0)` and `(5.2)` by smearing
both sides with delta-sequences tending to point masses. This is the exact
reason the Lean proof must build a pointwise scalar producer from distributional
pairings, not from endpoint values or downstream boundary values.

## Lean Substrate Already Present

The following checked pieces are on route:

- `OSToWightmanOSIIDeltaSmearing.lean`: shrinking Schwartz approximate
  identities and equality from equal smeared integrals.
- `OSToWightmanOSIIProductTensorRealEdge.lean`: positive-orthant product-source
  delta recovery.
- `OSToWightmanOSIIProductTensorSchwingerFunctional.lean`: selected current to
  left-shifted shell consumers and product-source/time-CLM transport.
- `OSToWightmanOSIIParametricFlatTubeBranch.lean`: one-coordinate flat-tube
  branches and Malgrange-Zerner carrier comparison.
- `OSToWightmanOSIILemma51CoordinateEstimate.lean` and
  `OSToWightmanOSIILemma51TotalBranch.lean`: the Lemma 5.1 coordinate/log-domain
  local-polydisc bridge.
- `K2VI1/Frontier.lean`: the special `k = 2` distributional assembly, useful as
  a model but not sufficient for the general `k` product witness.

## Missing Producer

The next genuine theorem is a general-`k` OS II `(A0)->(P0)` scalar producer:

```lean
theorem osiiA0P0_productTensor_scalarWitness
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : Nat) :
    exists the `S_prod` payload above
```

It must be proved by these substeps, in this order:

1. Build the real positive-time scalar representative from the OS semigroup
   scalar-product formula, in ordered difference variables.
2. Use the existing Lemma 5.1/Malgrange-Zerner carrier to show local
   holomorphy near each positive real difference point.
3. Use positive-orthant delta smearing to upgrade the distributional pairing
   identity to pointwise scalar equality on the positive real slice.
4. Extend from one ordered sector to all product tensors by Euclidean
   permutation symmetry and the checked density/product-tensor kernel package.
5. Derive common translation/permutation/reality from OS `E1`/`E3` on the same
   representative.
6. Prove the polynomial growth package from OS II VI.1/VI.2, not from a
   boundary-value theorem downstream of this witness.

## Immediate Work Item

Start with a scratch theorem for step 1-3, not production:

```lean
theorem proofideas_osii_A0P0_positiveOrthant_pointwise_scalar_identity
```

The statement should consume:

- a locally holomorphic scalar representative on the positive orthant,
- the OS semigroup scalar-product distributional equality,
- continuity on the real positive slice,
- the existing positive-orthant delta family,

and produce pointwise equality at a strict-positive difference-time vector.

Only after that theorem is checked should the production proof body of
`exists_acrOne_productTensor_witness` be edited.

## Current Progress

The `(A0)->(P0)` delta-smearing scratch theorem is checked in:

```text
test/proofideas_osii_A0P0_positiveOrthant_pointwise_scalar_identity.lean
```

The semigroup-facing form has now been promoted to production:

```lean
osiiA0P0_total_time_semigroup_pointwise_of_pairings
osiiA0P0_total_time_semigroup_pointwise_of_productTensor_distribution_eq
osiiA0P0_total_time_semigroup_pointwise_of_contDiffOn_productTensor_distribution_eq
```

These theorems instantiate the right hand side as the actual OS total
positive-time semigroup scalar, discharge the semigroup continuity from the
Chapter V branch, and convert the paper's distributional `(5.2)` input from
one-sided Laplace product-tensor equality into the compact product-source
pairings required by the delta-smearing theorem.  The strongest current surface
consumes the `(A0)` output as a `ContDiffOn` representative on an open
neighborhood of the positive orthant.  The remaining input is therefore exactly:

1. construct the OS-II `(A0)` coordinate-space scalar representative on such an
   open neighborhood;
2. identify its strict-positive imaginary-axis scalar functional;
3. prove `(5.2)` as equality with the OS semigroup functional on one-sided
   Laplace product tensors.

The OS `E1` one-variable identity-theorem step for the vacuum-left semigroup
branch has also been promoted to production:

```lean
OSInnerProductTimeShiftHolomorphicValueExpandBoth_vacuumLeft_constant
osiiFlatTotalTimeBranch_vacuumLeft_eq_const_on_tube
osiiFlatTotalTimeBranch_vacuumLeft_toDiffFlat_eq_const_on_acr
osiiFlatTotalTimeBranch_vacuumLeft_single_toDiffFlat_eq_schwinger_on_acr
```

These correspond to the Chapter V base mechanism: real positive-edge equality
from OS semigroup time translation, then holomorphic extension by the identity
theorem.  The single-right-factor theorem gives the concrete Schwinger scalar
form of the vacuum-left flat branch.  The next non-wrapper step is to connect
the actual OS-II `(A0)` coordinate-space scalar representative to the
`ContDiffOn` distributional-product-tensor bridge above.

## 2026-05-24 Local A0 Representation Frontier

Re-reading OS II V.2, especially equations (5.2), (5.15)--(5.20), confirms the
next bridge: `(P0)` follows by smearing the Hilbert-space distribution identity
with compact positive delta approximants and then taking the pointwise limit.
Therefore Lean must not identify the compact source current with the
one-sided Laplace product tensor.  The missing theorem is the local `(A0)`
regularity/representation statement:

```lean
SCV.RepresentsDistributionOn
  (osiiA0LocalCutoffTimeShellCLM OS chi hchi_disj fLeft kappa)
  S_real U
```

for the fixed cutoff shell already constructed by
`exists_osiiA0LocalCutoffSchwingerCLM_for_uniform_right_time_support`.  Once
this is available, every compact product source with time support in `U`
evaluates by the scalar integral `∫ S_real * source`, and the existing local
delta theorem `osiiA0P0_total_time_semigroup_pointwise_of_local_pairings`
matches the OS II V.2 smearing argument.

Lean substrate now written and checked in scratch:

```text
test/proofideas_osii_local_a0_timeshell_clm.lean
```

The neutral production definitions are:

```lean
osConjTensorProductRightCLM
osiiA0LocalCutoffTimeShellCLM
```

The local V.2 delta bridge has now been promoted to production:

```lean
osiiA0LocalCutoffTimeShell_rep_eq_bvt_imagAxis_of_pairings
```

This proves that a represented cutoff time-shell distribution, together with
the uniform compact product-source pairings, selects the BVT imaginary-axis
value pointwise at any strict-positive time vector.  A further scratch file
records the immediately preceding transport layer:

```text
test/proofideas_osii_full_a0_rep_to_timeshell.lean
```

It shows that a full local coordinate-space representative for the cutoff
Schwinger distribution induces the time-shell `RepresentsDistributionOn`
statement once two concrete obligations are proved: support of the fixed
tensor test in the local A0 carrier, and the partial spatial/left-variable
Fubini integral defining `S_time`.

The support half of that transport is checked in the same scratch file:

```lean
proofideas_partial_fubini_scalar_time_shell
proofideas_section43_partial_fubini_time_shell
proofideas_timeShellScalarFromCoordinateRepresentative
proofideas_section43_partial_fubini_timeShellScalar
proofideas_orderedPullback_rightFromTimeSpatial_apply
proofideas_osConjTensorProduct_rightFromTimeSpatial_apply
proofideas_fullA0_integrand_rightFromTimeSpatial_eq
proofideas_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM
proofideas_osiiA0_timeShell_tensor_supportsInOpen_right_timeSet
```

The measure-preserving coordinate-change bridge has now been promoted to the
small production companion
`OSToWightmanOSIIA0TimeShellCoordinateChange.lean`.  The key checked theorems
are:

```lean
osiiA0_fullProductTimeSpatialMeasurableEquiv_measurePreserving
osiiA0_fullCoordinateChange_to_productTimeShell
osiiA0_fullA0_timeShellScalar_identity_of_product_integrable
```

This proves the full spacetime A0 pairing is transported to the exact
`((left, spatial), time)` product measure used by the scalar time-shell
Fubini step.  The only remaining hypothesis in that bridge is the genuine
analytic integrability of the product-coordinate local representative.  The
live W4 file imports this companion, so the bridge is available on the direct
`exists_acrOne_productTensor_witness` path.

The remaining genuine mathematical content is not a Fubini or source-current
shortcut; it is proving the `RepresentsDistributionOn` statement above from
OS II `(A0)`/Lemma 5.1 local real analyticity of the Schwinger functions away
from the coincidence locus, together with the integrability supplied by that
same local A0 representative.

## 2026-05-25 General-d Lemma 5.1 Scratch

The existing production Lemma 5.1 coefficient file contains the paper's
physical four-vector calculation.  The live W4 theorem is still stated for
arbitrary spatial dimension `d`, so before the local A0 representative can be
made dimension-generic the Lemma 5.1 coordinate estimate must also be
dimension-generic.

Checked scratch:

```text
test/proofideas_osii_axis_pair_lemma51.lean
```

This implements the faithful Lemma 5.1 role with an axis-pair basis
`(T, plus/minus e_j)` for `j : Fin d`:

```lean
proofideas_osiiAxisPairCoeff_linear_identity
proofideas_osiiAxisPairCoeff_re_pos_of_small_perturbation
proofideas_osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
proofideas_osiiAxisPair_local_polydisc_extension_differentiableOn
```

The mathematical content is the OS-II `(5.11)`--`(5.14)` coefficient step in a
general-`d` basis: the constant coefficient part supplies half of the positive
time coordinate, the signed pair coefficients recover each spatial
perturbation, and a concrete radius keeps all coefficients in the right half
plane.  The next production move is to promote this checked scratch into a
small Lemma 5.1 companion and then connect it to the local A0 representative
producer, rather than relying on the `Fin 4` estimate in the all-`d` W4 path.

The promoted total-branch companion now also includes:

```lean
osiiAxisPair_totalLogSemigroupBranch_local_realSlice_continuous
osiiAxisPairTotalLogSemigroupBranch_real_edge_eq_total
osiiAxisPairTotalLogSemigroupBranch_log_real_edge_eq_total
osiiAxisPairTotalLogSemigroupBranch_single_real_edge_eq_schwinger_timeShift
osiiAxisPairTotalLogSemigroupBranch_single_log_real_edge_eq_schwinger_timeShift
osiiAxisPairCoeffMap_weighted_time_sum
osiiAxisPairCoeffMap_time_mul_sum
osiiAxisPairWeightedTotalLogSemigroupBranch_real_edge_eq_total
osiiAxisPairWeightedTotalLogSemigroupBranch_log_real_edge_eq_total
osiiAxisPairWeightedTotalLogSemigroupBranch_single_real_edge_eq_schwinger_timeShift
osiiAxisPairWeightedTotalLogSemigroupBranch_single_log_real_edge_eq_schwinger_timeShift
osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_schwinger_timeShift
osiiAxisPair_weightedTotalLogSemigroupBranch_local_realSlice_continuous
osiiAxisPair_weightedTotalLogSemigroupBranch_local_realSlice_bound
osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge
```

This is the direct handoff from the complex Lemma 5.1/MZ polydisc to the
real-slice continuity and real-edge Schwinger identities consumed by the
cutoff-support A0 bridge.  The two `log_real_edge` theorems are the Lean form of
the OS II sentence "going back to the variables `u`" after `(5.8)`: evaluating
the logarithmic branch at positive coefficient variables restricts to the
actual OS semigroup scalar, and in the single-test case to the Schwinger
functional of the OS-conjugated left test tensor the shifted right test.

The weighted branch is the route-correct normalization for the axis-pair chart:
the coefficients multiply directions whose time component is `T`, so the
physical semigroup time is `T * sum coeff`, not the bare coefficient sum.  The
coefficient-map theorem returns the branch directly to the physical shift
`xi^0 / 2 + zeta^0`, matching the Lemma 5.1 calculation before the A0
time-shell handoff.  The final local packet places holomorphy and the real-edge
identity on one common smaller polydisc, so the next A0 representation proof can
work with a single branch surface.

## 2026-05-25 A0 Time-Shell Carrier/Integrability Tightening

The abstract support and Fubini-integrability obligations in the full
coordinate-to-time-shell bridge have now been made concrete.  Checked scratch:

```text
test/proofideas_osii_a0_product_integrability.lean
```

Promoted production theorem surfaces:

```lean
osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM_of_compact
osiiA0_osConjTensorProduct_orderedPullback_supportsInOpen_rightTimeCylinder
osiiA0_productTimeShell_integrable_of_full_supportsInOpen
isOpen_osiiA0_rightTimeCylinder
osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep_rightTimeCylinder
osiiA0LocalCutoffTimeShell_representsDistributionOn_of_full_local_rep_rightTimeCylinder_of_continuousOn
osiiA0LocalCutoffTimeShell_representsDistributionOn_of_pointwise_full_local_rep_rightTimeCylinder
osiiA0LocalCutoffTimeShell_representsDistributionOn_of_pointwise_full_local_rep_rightTimeCylinder_open
osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_tsupport_local_reps
osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_full_local_rep_rightTimeCylinder_open
```

Mathematical content: a compactly supported right time test produces a full
two-block ordered-pullback current supported in the natural right-time
cylinder; that cylinder is open when the time carrier is open; and continuity
of the full A0 representative on the cylinder gives the exact product-coordinate
integrability required by the Section 4.3 partial-Fubini step.  Thus the
time-shell bridge no longer carries an opaque support/integrability hint.

The cutoff-support localization is important: Lemma 5.1/Malgrange-Zerner now
only has to supply local representatives on the actual cutoff support inside
the right-time cylinder.  On the complement of `tsupport chi`, the localized
Schwinger distribution is zero and the representative is required to vanish.

Remaining genuine producer: construct the OS-II `(A0)` full local coordinate
representative itself from Lemma 5.1/Malgrange-Zerner, with local continuity and
`RepresentsDistributionOn` only on the cutoff support.  Once supplied, the
checked time-shell bridge feeds the existing local `(A0)->(P0)` delta theorem.

## 2026-05-25 Local Chart Transport

Checked scratch:

```text
test/proofideas_osii_represents_distribution_chart_transport.lean
```

The theorem surfaces have now been promoted to production in
`OSReconstruction/SCV/DistributionalRepresentationGluing.lean`:

```lean
SCV.representsDistributionOn_pullback_measurePreservingCLE
SCV.representsDistributionOn_of_chart_rep_measurePreservingCLE
```

This records the coordinate step needed after OS II V.1: if the local
Malgrange-Zerner representative is proved in flattened/chart coordinates, then
a measure-preserving continuous-linear chart transports the
`SCV.RepresentsDistributionOn` statement back to the original OS configuration
variables.  The proof transports both topological support and the Lebesgue
pairing integral; it does not assume the missing A0 representative.

## 2026-05-25 Exact Remaining A0 Theorem Shape

The next production theorem should not be another time-shell wrapper.  It must
produce the local full-coordinate representation consumed by

```lean
osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_full_local_rep_rightTimeCylinder_open
```

The local pointwise obligation has the following shape, for each

```lean
x ∈ tsupport (χ : NPointDomain d (n + m) -> C)
```

inside the right-time cylinder:

```lean
∃ Ux : Set (NPointDomain d (n + m)), IsOpen Ux ∧ x ∈ Ux ∧
  ContinuousOn H_full Ux ∧
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj) H_full Ux
```

The classical source step is OS II V.1, equations `(5.7)`--`(5.8)`: rotate the
fixed coincidence-free real point into a positive cone, express nearby physical
coordinates by axis-pair coefficients, use the one-variable semigroup
continuations, and apply Malgrange-Zerner because the flat-tube branches
continue the same distribution.  In Lean terms the still-missing leaf is the
distributional equality, not the polydisc geometry:

```lean
-- schematic leaf, not a production statement yet
SCV.RepresentsDistributionOn
  ((osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj).comp chartPullback)
  H_chart V_chart
```

where `H_chart` is the MZ/log-semigroup branch already controlled by the
general-`d` axis-pair Lemma 5.1 geometry.  Once this chart-level representation
is proved, the checked chart-transport scratch turns it into the required
`H_full` local representative, and the already checked time-shell bridge turns
that into the `(A0)->(P0)` pointwise scalar identity.

## 2026-05-25 Distributional MZ Gluing Closed

The distributional half of the Malgrange-Zerner gluing step has now been checked
and promoted:

```lean
SCV.representsDistributionOn_glued_iUnion
osiiA0LocalCutoffTimeShell_representsDistributionOn_of_tsupport_glued_full_local_reps_rightTimeCylinder_open
```

The first theorem says that local kernels representing the same Schwartz
distribution and agreeing on overlaps glue to a kernel representing that
distribution on any covered carrier.  The second applies this exactly to the
OS-II cutoff-support time-shell handoff: if branch carriers cover the cutoff
support in the right-time cylinder, each branch represents
`osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj`, and the branches agree on
overlaps, then the glued full-coordinate representative feeds the existing
time-shell `RepresentsDistributionOn` theorem.

The remaining genuine leaf is therefore sharper than before:

```lean
∀ branch,
  SCV.RepresentsDistributionOn
    (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj)
    D_branch
    N_branch
```

for the actual OS-II V.1 semigroup/Malgrange-Zerner branch family.  This is the
"same distribution" assertion in OS II `(5.7)`--`(5.8)`; the carrier gluing and
time-shell transport no longer need to be reproved.

A further checked neutral bridge is:

```lean
SCV.representsDistributionOn_congr_on_subset
```

This is the handoff from local EOW recovery to branch representation: once a
recovered representative `H` represents the distribution on a chart and the
explicit semigroup branch agrees with `H` on a smaller side window, the branch
itself represents the distribution on that side window.

Checked scratch:

```lean
proofideas_regularizedEnvelope_sideRepresentations_from_oneChartScale
```

in

```text
test/proofideas_osii_branch_representation_from_local_eow.lean
```

This applies the existing local EOW one-chart recovery theorem and extracts
branch-level `RepresentsDistributionOnComplexDomain` statements for the plus
and minus side windows.  In the OS-II instantiation, the remaining hypotheses to
prove are now the concrete product-kernel facts for the semigroup branch family:
local covariance, branch holomorphy, and the product-test representation
identity.

## 2026-05-25 Fixed-Window Branch Representation Extraction

Promoted the fixed-window version of the same extraction:

```lean
SCV.regularizedLocalEOW_branchRepresentations_from_fixedWindowScale
```

in:

```text
OSReconstruction/SCV/LocalEOWBranchRepresentation.lean
```

This consumes the already checked fixed-window local EOW assembly theorem and
returns representation of the explicit plus/minus side branches on the strict
side balls.  The useful effect is that the local covariance, holomorphy,
descent kernel, product-test integral, and approximate-identity machinery no
longer have to be carried as separate OS-II obligations once the fixed-window
raw data is available.  The remaining genuine OS-specific leaf is sharper:
prove the raw OS-II boundary-value identities `(5.7)`--`(5.8)` for the actual
semigroup side branches against `osiiA0LocalCutoffSchwingerCLM`.

## 2026-05-25 Dense Boundary-Value Extension

Checked scratch:

```text
test/proofideas_osii_dense_boundary_extension.lean
test/proofideas_osii_dense_boundary_extension_topological.lean
test/proofideas_osii_section43_dense_boundary_adapter.lean
test/proofideas_section43_real_span_density.lean
```

Promoted production support:

```lean
SCV.tendsto_clm_apply_of_dense_of_eventually_bound
SCV.tendsto_clm_apply_of_dense_span_of_eventually_bound
SCV.tendsto_clm_apply_of_dense_of_eventually_equicontinuous
SCV.tendsto_clm_apply_of_dense_span_of_eventually_equicontinuous
SCV.tempered_eventually_equicontinuous_of_pointwise_bounded
section43NPointTimeSpatialTensor_compactLaplace_spatialFourier_generator_smul_mem
dense_section43NPointTimeSpatialTensor_real_span_compactLaplace_spatialFourier
section43_tendsto_schwartzNPoint_of_compactLaplace_spatialFourier_generators
section43_tendsto_schwartzNPoint_real_of_compactLaplace_spatialFourier_generators
section43_tendsto_schwartzNPoint_real_of_generators_of_pointwise_bounded
```

in:

```text
OSReconstruction/SCV/DenseBoundaryExtension.lean
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceSpatialDensity.lean
```

This is the functional-analytic upgrade needed after the book's product-source
boundary identities are proved.  The first version handles normed spaces with
an eventual uniform operator bound; the route-relevant version handles locally
convex Schwartz spaces with eventual equicontinuity at zero.  The Section 4.3
specialization proves that compact time-Laplace / compact spatial-Fourier
product-generator convergence extends to every `SchwartzNPoint` test, both in
the complex-linear form and in the real-linear form consumed by local EOW.  The
real-linear bridge uses the genuine algebraic fact that the generator set is
closed under complex scalar multiplication, so its real span is still dense.
The Banach-Steinhaus corollary reduces the equicontinuity hypothesis to the
pointwise boundedness estimate for the branch-difference family.

Thus the remaining OS-II `(5.7)`--`(5.8)` leaf is now precise: prove
product-source convergence for the actual semigroup/MZ branch family and a
pointwise boundedness estimate for the boundary slice CLM differences; then
Banach-Steinhaus plus dense extension supplies the all-test raw boundary-value
hypotheses consumed by local EOW.

The finite Borchers semigroup boundary generator has now been promoted:

```lean
tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_to_imagAxis_sum
tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_to_imagAxis
```

These are upstream of `bvt_F`: they use the OS semigroup spectral boundary
theorem termwise, then recombine the finite Borchers expansion inside the
Fourier/Laplace integral.  Together with the local weighted-branch compact bound
above, this supplies two concrete pieces of the remaining `(5.7)`--`(5.8)` raw
branch proof: the product-source generator limit and the local boundedness
ingredient needed for the Banach-Steinhaus extension.

## 2026-05-25 Raw Axis-Pair Selector Packet

The raw generator boundary theorem has now been specialized all the way to the
actual weighted Lemma 5.1 coefficient chart:

```lean
tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_coeffMap_real
tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real
osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge_selector
```

The first theorem identifies the one-sided rotated semigroup integral with the
weighted MZ branch value at the positive coefficient point.  The second uses the
single-test real-edge theorem to select the actual Schwinger scalar
`OS.S (n + r) (f.osConjTensorProduct (timeShiftSchwartzNPoint ... g))`.  The
third shrinks the Lemma 5.1 polydisc so the same local packet carries
holomorphy, real-edge Schwinger equality, coefficient positivity, positive
physical time, and the raw selector limit.

Also tightened:

```lean
osiiAxisPair_weightedTotalLogSemigroupBranch_local_realSlice_bound
```

so the compact real-slice bound now returns `0 <= C`, matching the
Banach-Steinhaus-facing pointwise-boundedness estimates.

Remaining genuine leaf: turn this selector packet plus the dense Section 4.3
generator theorem into the all-test boundary CLM limits required by
`SCV.regularizedLocalEOW_branchRepresentations_from_fixedWindowScale`, then use
the checked gluing/time-shell bridges to obtain the local A0 representative.

## 2026-05-25 Time-Shell Dense Boundary Adapter

Promoted the finite-time version of the dense boundary-value step:

```lean
section43_tendsto_timeSchwartz_real_of_iteratedLaplace_generators_of_pointwise_bounded
section43_timeSchwartz_generator_limit_of_compact_representatives
```

in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTimeProductDensity.lean
```

Mathematical content: the OS-II `(5.7)`--`(5.8)` all-test limit needed by
fixed-window local EOW can now be reduced exactly to compact one-sided Laplace
representative limits plus pointwise boundedness.  The second theorem handles
the nontrivial representative-choice step: if the boundary family and target
descend to the positive-time quotient, convergence on the explicit compact
Laplace representative transports to any time Schwartz test with the same
positive-time quotient.

Remaining genuine leaf: prove the actual compact-representative selector limits
and quotient-descent facts for the semigroup/MZ branch family, then combine this
time-shell adapter with the local EOW branch representation theorem.

## 2026-05-25 Glued Axis-Pair Time-Shell Representative

The no-shrink Malgrange-Zerner overlap packet has now been converted into an
actual representative, not only compatible local charts:

```lean
osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_mz_cover
osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_glued_schwinger_edge
osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_real_representative
osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_real_representative_pairing
```

Content: on any compact real support in the positive time half-space, the
selected Lemma 5.1 branches glue to one holomorphic scalar on a complex
neighborhood.  Its real restriction is continuous on an open real time-shell
neighborhood of the compact support, equals the shifted Schwinger shell on
the real edge, and has the corresponding compact-source pairing equality for
tests supported in the compact carrier.

Next genuine leaf: feed this real representative into the existing
`osiiA0LocalCutoffTimeShellCLM` representation surface.  Concretely, the next
proof must identify the glued representative with the local A0 cutoff
time-shell distribution on compact product sources, then use the existing
local `(A0)->(P0)` product-tensor consumer.

## 2026-05-25 A0 Cutoff Pairing/Descent Packet

Checked scratch:

```text
test/proofideas_osii_a0_uniform_cutoff_packet.lean
```

Promoted production theorem:

```lean
exists_osiiA0LocalCutoffSchwingerCLM_for_uniform_productSource_pairings_with_descent
```

Mathematical content: the uniform cutoff for a compact strict-positive
right-time carrier now carries both ingredients needed by the dense
time-shell boundary adapter: strict-positive support for quotient descent of
`osiiA0LocalCutoffTimeShellCLM`, and the compact BVT/A0 product-source pairing
identity for every right product source supported in the carrier.  The proof
uses the already-strengthened uniform right-time support theorem and only
downgrades strict positivity to closed positivity at the quotient-map call.

Remaining genuine leaf: prove the local A0 representative/kernel selection for
the actual MZ branch family.  The cutoff descent and compact BVT/A0 pairings no
longer need to be supplied separately once that representative is available.

## 2026-05-25 A0 Cutoff Time-Shell Quotient Descent

Checked scratch:

```text
test/proofideas_osii_a0_time_shell_descent.lean
```

Promoted production theorem surface:

```lean
osiiA0LocalCutoffTimeShellCLM_eq_of_timePositiveQuotient_eq
```

and strengthened:

```lean
exists_osiiA0LocalCutoffSchwingerCLM_for_uniform_right_time_support
```

so the uniform A0 cutoff now exposes its strict-positive right-time cylinder
support.  Mathematical content: positive-time quotient equality controls time
tests only on the closed positive orthant, so the localized time-shell
Schwinger functional descends to that quotient only after the cutoff support is
known to lie over the positive right-time cylinder.  The strengthened cutoff
construction proves exactly that from the same compact strict-positive
right-time carrier used in OS II `(A0)`.

This closes the target-distribution quotient-descent side of the finite
time-shell dense-boundary adapter for the actual A0 local cutoff.  The
remaining genuine leaf is now the semigroup/MZ side: prove the compact
Laplace-representative selector limits and the corresponding descent/boundedness
facts for the raw side branch family, then feed those into
`section43_timeSchwartz_generator_limit_of_compact_representatives` and
`SCV.regularizedLocalEOW_branchRepresentations_from_fixedWindowScale`.

## 2026-05-25 Axis-Pair Compact Packet

The direct global product-kernel shortcut was rejected: the OS II V.1 route needs
local side-cone boundary values for the actual Malgrange-Zerner branch, with
compact real-support uniformity.  The first compactness step is now checked in
scratch and promoted:

```text
test/proofideas_osii_axis_pair_compact_packet.lean
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIILemma51AxisPairTotalBranch.lean
```

```lean
osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_realSlice_packet
```

Mathematical content: for any compact real support contained in the positive
time half-space, the pointwise Lemma 5.1 branch-selector packets admit a finite
subcover by actual axis-pair centers.  The theorem keeps, for every selected
center, holomorphy, convergence of the raw positive-side selector to the MZ
branch, and a real-slice bound, and it extracts one finite bound over the
selected centers.

This is the compact-support uniformization needed before the all-test
side-boundary limit can be passed through local EOW.  The next genuine step is
to combine this finite packet with overlap equality/Malgrange-Zerner gluing and
the Section 4.3 compact-representative adapter to prove the raw side CLM limit
on a fixed local EOW window.

## 2026-05-25 Local-EOW Integral Boundary Handoff

Checked scratch:

```text
test/proofideas_osii_local_eow_boundary_from_section43_selectors.lean
```

Promoted production theorem:

```lean
section43_tendsto_localEOW_boundary_integral_of_productKernel_selectors
```

in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTimeProductDensity.lean
```

Mathematical content: the Section 4.3 product-kernel selector theorem already
gives convergence of the raw real-linear boundary CLMs on every finite-time
Schwartz test, provided quotient descent and Banach-Steinhaus boundedness are
known.  The new theorem converts that CLM convergence into the exact integral
boundary-value limit used by fixed-window local EOW, via the explicit side
branch integral identity.  This is the OS II `(5.7)`--`(5.8)` handoff from
selector distributions to side-branch boundary values; it does not assume the
remaining OS-specific selector/descent/boundedness hypotheses.

The next genuine leaf remains the actual weighted axis-pair/MZ instantiation:
construct the raw side CLMs for the selected branch family and prove their
quotient descent, product-kernel selector convergence, and pointwise boundedness.
Those inputs can then feed this handoff and
`SCV.regularizedLocalEOW_branchRepresentations_from_fixedWindowScale` to produce
the local branch `RepresentsDistributionOn` hypotheses.

## 2026-05-25 Axis-Pair Selector Filter Bridge

Checked scratch:

```text
test/proofideas_osii_axis_pair_selector_filter_bridge.lean
```

New checked theorem surfaces:

```lean
proofideas_tendsto_coord0_selector_of_positive_side_cone
proofideas_axisPair_single_selector_lifted_to_time_coordinate_side_cone
```

Mathematical content: the existing weighted axis-pair selector is a
one-parameter positive-side boundary value in the semigroup time variable.  The
fixed-window local EOW machinery is phrased as a vector side-height
`nhdsWithin` limit.  The scratch bridge proves the exact filter conversion
along the physical time coordinate: if the side cone keeps coordinate `0`
positive, then composing the one-parameter selector with `y ↦ y 0` gives the
required vector-side limit.  The second theorem applies this directly to
`tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real`.

This is not yet the full local A0 representative.  It removes the elementary
filter mismatch and leaves the genuine remaining leaf exposed: construct the
raw time-shell CLM family for the axis-pair/MZ branch, prove its quotient
descent and pointwise boundedness, and identify its product-kernel values with
the scalar selector without replacing the `Fin k` product shell by the
`Fin (d + 1)` axis-pair chart.

## 2026-05-25 Raw Axis-Pair CLM Side Family

Checked scratch:

```text
test/proofideas_osii_axis_pair_raw_clm_selector_bridge.lean
test/proofideas_osii_axis_pair_raw_clm_descent_bounded.lean
```

Promoted production companion:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIAxisPairRawCLMSelector.lean
```

New checked theorem surfaces:

```lean
osiiAxisPair_timeShell_regularizedCLM_selector_to_branch
osiiAxisPair_timeShell_regularizedCLM_selector_to_branch_sideCone
osiiAxisPair_rawCLMSide_descent_and_pointwise_bounded
```

Mathematical content: the raw positive-height side family is now the actual
`OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM`, not a bare
integral surrogate.  Expanding that CLM on the Section 4.3 Paley test gives the
axis-pair selector integral and hence the selected weighted MZ time-shell
branch.  The side-cone theorem converts the scalar height to the local-EOW
vector-side filter using the physical time coordinate.  The descent/boundedness
theorem supplies the one-sided quotient descent and Banach-Steinhaus pointwise
bound for the same side family and spectral boundary target.

The remaining genuine leaf is now narrower: extend this one-time raw CLM packet
through the spatial/time product generator layer.  In Lean terms, prove the
actual branch-side integral identity and product-kernel convergence needed by
`section43_tendsto_localEOW_boundary_integral_of_productKernel_selectors`, then
feed the resulting all-test side limits into
`SCV.regularizedLocalEOW_branchRepresentations_from_fixedWindowScale`.  This is
the real OS II `(5.7)`--`(5.8)` representation step; it should not be replaced
by a global product-kernel shortcut or by identifying the `Fin (d + 1)` chart
with the final `Fin k` product shell.

## 2026-05-25 Compact Branch-Integral Transport Adapter

Checked scratch:

```text
test/proofideas_osii_compact_branch_integral_transport.lean
```

Promoted production theorem surfaces:

```lean
section43_tendsto_iteratedLaplaceRepresentative_of_branch_integral_transport
section43_tendsto_timeSchwartz_real_of_branch_integral_compact_representatives
```

in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTimeProductDensity.lean
```

Mathematical content: this is the compact-source transport packet for OS II
`(5.7)`--`(5.8)`.  The DCT theorem already moves pointwise branch-selector
convergence under a compact strict-positive product source; the new adapter
adds the two source-current identities that are actually needed on the E->R
route:

```lean
TseqC a (section43IteratedLaplaceSchwartzRepresentative n g)
  = ∫ τ, Kseq a τ * g.f τ
TC (section43IteratedLaplaceSchwartzRepresentative n g)
  = ∫ τ, K τ * g.f τ
```

Together with compact real-slice bounds, quotient descent, and
Banach-Steinhaus pointwise boundedness, this now yields the all-test
real-linear side limit consumed by fixed-window local EOW.  The remaining
genuine leaf is correspondingly sharp: prove these two identities and the
compact support bounds for the actual axis-pair/MZ branch family through the
spatial/time product generator layer.

## 2026-05-25 Local-EOW Boundary from Compact Branch Integrals

Checked scratch:

```text
test/proofideas_osii_local_eow_boundary_from_compact_branch_integrals.lean
```

Promoted production theorem:

```lean
section43_tendsto_localEOW_boundary_integral_of_branch_integral_compact_representatives
```

in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTimeProductDensity.lean
```

Mathematical content: the compact branch-integral adapter now feeds the raw
boundary-value hypothesis required by local EOW.  If the actual MZ side CLMs
have compact branch-integral evaluations on the Laplace representatives, the
target CLM has the limiting branch integral evaluation, and the branch family
has pointwise selection plus compact bounds, then the explicit side integral

```lean
∫ x, Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) * φ x
```

tends to the target distribution value for every compactly supported local EOW
test.  This removes the need to force the axis-pair selector through the older
global product-kernel shortcut; the genuine remaining leaves are the concrete
source-current identities and compact bounds for the weighted axis-pair/MZ
branch family.

## 2026-05-25 Fixed-Window Slice CLMs from Compact Branch Integrals

Checked scratch:

```text
test/proofideas_osii_fixed_window_slice_clms_from_compact_branch_integrals.lean
```

Promoted production theorem:

```lean
osiiFixedWindow_sliceCLMs_from_branch_integral_compact_representatives
```

in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIFixedWindowSelectors.lean
```

Mathematical content: the local EOW slice-family constructor now consumes the
compact branch-integral boundary-value route directly.  The theorem first uses
`section43_tendsto_localEOW_boundary_integral_of_branch_integral_compact_representatives`
on the plus and minus sides, then feeds the resulting compact-test raw boundary
values into `SCV.localEOWSliceCLMs_from_preparedDomains`.

The remaining blocker is now sharper and more honest: instantiate the exposed
`Kseq/K` identities, compact convergence, compact bounds, quotient descent, and
side integral formulas for the actual weighted axis-pair/Malgrange-Zerner
branch family.

## 2026-05-26 Raw Axis-Pair Side CLM Fourier Formula

Checked scratch:

```text
test/proofideas_osii_axis_pair_side_clm_fourier_formula.lean
```

Promoted production theorem surfaces:

```lean
osiiAxisPairPositiveSideCLMR_apply_of_coord0_pos
osiiAxisPairLowerSideCLMR_apply_of_coord0_neg
osiiAxisPairPositiveSideCLMC_timeProductTensor_flattened
osiiAxisPairLowerSideCLMC_timeProductTensor_flattened
osiiAxisPair_positiveSide_timeProductTensor_tendsto_branchIntegral_sideCone
```

Mathematical content: the raw fixed-window axis-pair side CLMs have now been
expanded to the actual Section 4.3 formula:

```lean
∫ x : R,
  OSInnerProductTimeShiftHolomorphicValueExpandBoth ... (-I * (x + y0 * I)) *
    FourierTransform (osiiAxisPairHeadRestrictionCLM d phi) x
```

This exposes the next genuine gap precisely.  The raw CLM is a one-dimensional
head-restricted line current; it is not already a full `Fin (d + 1)` physical
slice density.  The remaining side-integral theorem must therefore use the
Section 4.3 Fourier/Laplace product-source factorization and the actual
Malgrange-Zerner branch family, rather than trying to satisfy the fixed-window
`realMollifyLocal` identity by unfolding the raw CLM alone.

The first product-source layer is also checked: the positive/lower raw side CLMs
evaluate on a product of one-sided Laplace representatives as the integral of
their imaginary-axis product-kernel values against the compact product source.
This supplies the moving-side analogue of the boundary source-current flattening;
the remaining nontrivial step is to identify those kernel values with the
selected MZ branch on a compact window and pass from product sources to the full
compact-representative side-integral theorem.

The positive-side product-source branch-integral limit is now promoted in:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanOSIIAxisPairProductSourceBranchLimit.lean
```

It combines the raw side all-test boundary convergence with
`osiiAxisPair_boundaryCLM_productTensor_eq_schwinger_timeShell_sideCone` and the
Lemma 5.1 real-edge identity.  Thus, for product one-sided Laplace sources
supported in a common time-shell window, the moving positive side CLM tends to
the integral of the selected MZ branch against that exact source.

## 2026-05-26 Lower Axis-Pair Branch Selector

Checked scratch:

```text
test/proofideas_osii_axis_pair_lower_branch_selector.lean
test/proofideas_osii_axis_pair_lower_product_source_branch_integral_limit.lean
```

Promoted production theorem surfaces:

```lean
osiiAxisPair_timeShell_regularizedCLM_selector_to_branch_lowerSideCone
osiiAxisPair_boundaryCLM_eq_timeShellBranch_lowerSideCone
osiiAxisPair_boundaryCLM_eq_schwinger_timeShell_lowerSideCone
osiiAxisPair_boundaryCLM_productTensor_eq_schwinger_timeShell_lowerSideCone
osiiAxisPair_lowerSide_timeProductTensor_tendsto_branchIntegral_sideCone
```

Mathematical content: the lower side now follows the same OS-II `(5.7)`--`(5.8)`
source-current route as the positive side.  The lower cone `y 0 < 0` is
transported to the positive semigroup height `-y 0`; the resulting raw selector
selects the actual weighted axis-pair MZ time-shell branch, hence the boundary
CLM selects the Schwinger time shell on a common Lemma 5.1 window.  The lower
product-source limit has been tightened so it depends only on the lower cone,
not on an auxiliary positive-side cone.

Remaining genuine gap: this still does not prove the finite-height side
integral formula

```lean
Tside y φ =
  ∫ τ, Fside (fun i => (τ i : C) + (y i : C) * I) * φ τ
```

for arbitrary compact local-EOW tests.  The next proof step is the actual
Section 4.3 Fourier/Laplace product-source-to-side-integral conversion for the
weighted axis-pair/MZ branch family.

## 2026-05-26 Finite-Height Axis-Pair Branch Normalization

Checked scratch:

```text
test/proofideas_osii_axis_pair_finite_height_time_shell_branch.lean
```

Promoted production theorem surfaces:

```lean
osiiAxisPairTimeShellPerturbationC_time
osiiAxisPairCoeffMap_time_mul_sum_timeShellC
osiiAxisPairWeightedTimeShellBranch_eq_semigroup_time
osiiAxisPairWeightedTimeShellBranch_realImag_eq_semigroup_time
```

Mathematical content: the corrected complex time-shell coordinate now formally
implements the OS-II return from Lemma 5.1 logarithmic variables to physical
time.  After exponentiating the principal logarithms on the coefficient carrier,
the weighted axis-pair MZ branch is exactly

```lean
OSInnerProductTimeShiftHolomorphicValueExpandBoth ... (τ 0)
```

and, on a side point `τ = x + i y`, exactly the semigroup branch at
`x 0 + i * y 0`.  Thus the remaining side-integral proof no longer has a
coefficient-normalization subgap; it must prove the genuine Fourier/Laplace
identity identifying the raw side CLM with the integral of this finite-height
semigroup branch against compact local-EOW tests.

Important discipline correction: the raw axis-pair side CLM is still a
head-restricted one-dimensional current.  It must not be identified directly
with a full arbitrary-`φ` side integral.  The next production proof must first
carry the current through the existing Section 4.3 spatial/time
product-generator transport; only after that transport has produced the correct
finite-height semigroup integrand should the new `realImag` theorem rewrite it
as the weighted axis-pair/MZ branch.

## 2026-05-26 Top ACR(1) Assembly Attempt

Checked scratch:

```text
test/proofideas_acr_one_product_witness_assembly_attempt.lean
```

This was a direct response to the assembly-mode concern.  The attempted
top-surface combination shows that the currently public flat total-time branch
facts provide:

```lean
DifferentiableOn C
  (fun z => osiiFlatTotalTimeBranch OS lgc F G (BHW.toDiffFlat k d z))
  (AnalyticContinuationRegion d k 1)
```

and common translation invariance only for translations with zero time
component:

```lean
a 0 = 0 ->
  osiiFlatTotalTimeBranch OS lgc F G
    (BHW.toDiffFlat k d (fun j μ => z j μ + a μ)) =
  osiiFlatTotalTimeBranch OS lgc F G (BHW.toDiffFlat k d z)
```

So the direct flat-branch assembly cannot close
`exists_acrOne_productTensor_witness`: that production theorem needs one
factorization-independent scalar `S_prod`, full common complex translation
invariance, permutation/reflection identities, product-tensor Schwinger
reproduction, and VI polynomial growth for the same witness.  The existing
local `(A0)->(P0)` bridge supplies pointwise Schwinger selection only after the
actual local A0 representative and `(5.2)` distributional equality are provided.

Conclusion for the next proof step: do not add another adapter around the top
`sorry`.  The missing theorem is still the general-`k` OS-II package that
constructs the actual local MZ/A0 representative family, proves its `(5.2)`
pairing equality on product one-sided Laplace sources, and then runs the
checked local `(A0)->(P0)` delta theorem to produce the pointwise scalar values
for the global ACR(1) witness.

## Same-Distribution Handoff Leaf

The route decision was checked against the books and a Gemini Deep Research
consult: a side-domain `RepresentsDistributionOnComplexDomain` statement is not
enough to identify the real A0 Schwinger distribution.  The faithful OS II
handoff must prove equality with the Schwinger cutoff CLM on dense
Laplace/Fourier generator classes and then extend by density.

Promoted production leaves:

```lean
section43_timeSchwartz_clm_eq_of_compactLaplace_product_sources
section43_schwartzNPoint_clm_eq_of_laplace_fourier_sources
osiiA0LocalCutoffTimeShellCLM_eq_of_compactLaplace_product_sources
```

The first theorem closes the finite-time version of OS II V.2 `(5.2)`: two
time-shell CLMs that descend to the positive-time quotient and agree on compact
one-sided Laplace product representatives are equal.  The second theorem is the
full `SchwartzNPoint` handoff: two n-point CLMs that descend to the
positive-energy quotient and agree on compact time-Laplace / spatial-Fourier
representatives are equal.  This is the exact density bridge needed before
using any local EOW/MZ branch as the A0 representative.

The third theorem specializes the time-shell leaf to the actual local A0
cutoff CLM: strict-positive support discharges the A0 target descent, so the
remaining inputs are exactly the branch-side descent and product-source
equality from OS II `(5.2)`.

Next assembly target: instantiate the same-distribution handoff for the actual
local MZ branch boundary CLM, proving the source equality on compact
Laplace/Fourier generators from OS II `(5.2)`.
