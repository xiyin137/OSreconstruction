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

The theorem-2 locality route also needs a local distributional
edge-of-the-wedge **envelope** theorem.  This is not a replacement for the
proved continuous `SCV.edge_of_the_wedge_theorem`, and it is not a new axiom.
It is a QFT-free SCV theorem built from the continuous EOW construction plus
the standard Streater-Wightman/Jost distributional regularization argument.
The already-developed real-translation, real-mollification, and compact-test
continuity machinery in `SCV/DistributionalUniqueness.lean` is part of this
route; the missing envelope step is the kernel/translation-covariance recovery
that converts the family of regularized continuous-EOW envelopes into one
holomorphic envelope.

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

### 2.4. Local distributional EOW envelope

Needed by theorem 2:

```lean
SCV.local_distributional_edge_of_the_wedge_envelope
```

This theorem should live in a pure SCV file and should not mention OS,
Wightman functions, Schwinger functions, `bvt_F`, `extendF`, or locality.  The
theorem-2 blueprint records the exact proposed statement: two holomorphic
functions on open opposite wedge neighborhoods of a real edge have a common
distributional boundary value on compactly supported Schwartz tests over that
edge; then they have a common local holomorphic envelope.  The output theorem
must also include uniqueness on the constructed open set: any holomorphic
function on that same `U` with the same plus and minus trace identities agrees
with the produced envelope.  This uniqueness is proved locally by the
continuous EOW identity theorem and then patched across the local chart cover;
it is part of the construction, not an additional downstream assumption.

The public proof package must distinguish checked API from remaining theorem
surfaces.  The following names are already checked and should be used exactly:
`localRealMollifySide_holomorphicOn_of_translate_margin`,
`realMollifyLocal_eq_sliceIntegral_translate`,
`realMollifyLocal_eq_sliceFunctional`,
`exists_cutoffSliceIntegral_clm_of_continuousOn`,
`realMollifyLocal_eq_cutoffSliceCLM`,
`tendsto_cutoffSliceCLM_of_boundaryValue`,
`tendsto_mollified_boundary_of_clm`,
`KernelSupportWithin.add`,
`KernelSupportWithin.smul`,
`KernelSupportWithin.smulLeftCLM`,
`KernelSupportWithin.smulLeftCLM_of_leftSupport`,
`KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall`,
`exists_schwartz_cutoff_eq_one_on_closedBall`,
`exists_closedBall_integral_clm_of_continuousOn`,
`exists_realMollifyLocal_valueCLM_of_closedBall`,
`exists_bound_realMollifyLocal_smulLeftCLM`,
`exists_bound_localRudinEnvelope_smulLeftCLM_of_side_bounds`,
`exists_schwartz_bound_normalized_intervalIntegral_clm_family`,
`exists_localRudinIntegrand_smulLeftCLM_clmFamily`,
`exists_schwartz_bound_localRudinEnvelope_smulLeftCLM_value`,
`regularizedEnvelope_valueCLM_of_cutoff`,
`localEOWRealLinearPart`,
`localEOWRealChart_eq_x0_add_linearPart`,
`localEOWRealChart_sub`,
`localEOWRealChart_add`,
`localEOWChart_sub_realEmbed`,
`localEOWChart_add_realEmbed`,
`localEOWRealLinearMatrix`,
`localEOWRealLinearMatrix_mulVec`,
`localEOWRealLinearCLE`,
`localEOWRealLinearCLE_apply`,
`localEOWRealLinearPullbackCLM`,
`localEOWRealLinearPullbackCLM_apply`,
`KernelSupportWithin.localEOWRealLinearPullbackCLM`,
`localEOWRealLinearPushforwardCLM`,
`localEOWRealLinearPushforwardCLM_apply`,
`KernelSupportWithin.localEOWRealLinearPushforwardCLM`,
`localEOWRealLinearKernelPushforwardCLM`,
`localEOWRealLinearKernelPushforwardCLM_apply`,
`KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM`,
`KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_translateSchwartz`,
`realMollifyLocal_localEOWRealLinearKernelPushforwardCLM`,
`realMollifyLocal_localEOWChart_kernelPushforwardCLM`,
`realMollifyLocal_localEOWChart_translate_kernelPushforwardCLM`,
`localEOWShiftedWindow`,
`isOpen_localEOWShiftedWindow`,
`convex_localEOWShiftedWindow`,
`isPreconnected_localEOWShiftedWindow`,
`integrable_realMollifyLocal_integrand_of_translate_margin`,
`localRealMollify_commonContinuousBoundary_of_clm`,
`realMollifyLocal_translateSchwartz`,
`realMollifyLocal_add_of_integrable`,
`realMollifyLocal_add_of_translate_margin`,
`realMollifyLocal_smul`,
`local_continuous_edge_of_the_wedge_envelope`,
`regularizedLocalEOW_fixedKernelEnvelope_from_clm`,
`regularizedLocalEOW_fixedWindowEnvelope_from_clm`,
`regularizedLocalEOW_family_from_fixedWindow`,
`regularizedLocalEOW_family_add`,
`regularizedLocalEOW_family_smul`,
`regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap`,
`exists_seminorm_bound_complexRealFiberIntegralRaw_zero`,
`basePrecompCLM`,
`baseFDerivSchwartzCLM`,
`exists_seminorm_bound_baseFDerivSchwartz`,
`exists_seminorm_bound_complexRealFiberIntegralRaw_deriv`,
`complexRealFiberIntegralCLM`,
`complexRealFiberIntegralCLM_apply`,
`boundaryProductKernel_from_fiberIntegralCLM`,
`boundaryProductKernel_from_complexRealFiberIntegralCLM`,
`regularizedEnvelope_productKernel_dbar_eq_zero`,
`translationCovariantKernel_distributionalHolomorphic`,
`regularizedEnvelope_holomorphicDistribution_from_productKernel`,
`regularizedEnvelope_pointwiseRepresentation_of_productKernel`,
`regularizedEnvelope_deltaLimit_agreesOnWedges`, and
`regularizedEnvelope_chartEnvelope_from_productKernel`.

The public local-descent proof package is split as the following theorem
surfaces plus the final envelope theorem.  Some entries are now checked; the
list is kept as the route ledger so the remaining Lean work consumes the same
interfaces documented below:

```lean
lemma sliceCLM_family_from_distributionalBoundary
theorem continuous_schwartzPartialEval₁CLM
theorem KernelSupportWithin.mono
theorem SchwartzMap.exists_schwartzCLM_finsetSeminormBound
theorem regularizedLocalEOW_chartKernelFamily_valueCLM
theorem continuous_chartKernelCutoffSlice
theorem continuous_chartKernelCutoffSlice_eval
theorem seminorm_translateSchwartz_uniformOn
theorem continuousOn_translateSchwartz_varyingKernel_of_fixedSupport
theorem continuousOn_realMollifyLocal_varyingKernel_of_fixedSupport
theorem localRudin_varyingKernel_boundaryData_of_clm
theorem continuousOn_localRudinBoundaryCLM_varyingKernel_of_fixedSupport
theorem tendsto_localRudinPlusBoundary_varyingKernel_of_clm
theorem tendsto_localRudinMinusBoundary_varyingKernel_of_clm
theorem exists_bound_localRudinIntegrand_varyingKernel
theorem continuousOn_localRudinEnvelope_varyingKernel_of_bound
theorem continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand
theorem regularizedLocalEOW_pairingCLM_of_fixedWindow
theorem norm_realEmbed_eq
theorem tsupport_subset_preimage_tsupport_complexTranslateSchwartz
theorem integral_mul_complexTranslateSchwartz_eq_shift_of_support
theorem regularizedLocalEOW_pairingCLM_localCovariant
theorem SupportsInOpen.complexTranslateSchwartz_of_image_subset
theorem schwartzTensorProduct₂CLMLeft
def schwartzPartialEval₂CLM
def mixedRealFiberIntegralCLM
def mixedBaseFiberTensor
theorem mixedBaseFiberProductTensorDense_all
def mixedRealFiberIntegralScalarCLM
theorem mixedRealFiberIntegralScalarCLM_apply
theorem mixedRealFiberIntegralScalarCLM_eq_comp_mixedRealFiberIntegralCLM
theorem continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral
def realParamKernelLeft
theorem realParamKernelLeft_apply
def realParamKernelRight
theorem realParamKernelRight_apply
def localDescentParamTestLeft
def localDescentParamTestRight
theorem mixedRealFiberIntegralCLM_localDescentParamTestLeft
theorem mixedRealFiberIntegralCLM_localDescentParamTestRight
theorem shearedProductKernelFunctional_localQuotient_of_productCovariant
theorem translationCovariantProductKernel_descends_local
theorem regularizedEnvelope_productKernel_dbar_eq_zero_local
theorem translationCovariantKernel_distributionalHolomorphic_local
theorem regularizedEnvelope_pointwiseRepresentation_of_localProductKernel
theorem regularizedEnvelope_chartEnvelope_from_localProductKernel
lemma chartDistributionalEOW_local_envelope
lemma distributionalEOW_extensions_compatible
lemma localDistributionalEOW_patch_extensions
theorem local_distributional_edge_of_the_wedge_envelope
```

The old one-shot surface
`regularizedLocalEOW_productKernel_from_continuousEOW` is retired in its
former global-covariance shape.  It may reappear only as a final assembly name
whose proof internally calls the four local theorems above; it must not assert
`ProductKernelRealTranslationCovariantGlobal K` for the cutoff-localized
mixed functional.

The longer list below gives the internal helper lemmas needed to prove those
surfaces.  Internal helper names are allowed when they carry real content
such as compactness, a change of variables, convolution holomorphy,
kernel extraction, or integration by parts; they should not be exported as
theorem-2 wrappers unless a later Lean file genuinely needs them.

The active Lean route is the **Streater-Wightman distributional EOW route**:

1. choose nested local real boxes and a support radius so all real
   translations used by a compactly supported smoothing kernel stay inside the
   larger box;
2. regularize both wedge-side holomorphic functions by real-direction
   convolution with a fixed compactly supported Schwartz kernel;
3. prove the regularized sides have the continuous common boundary value
   `x ↦ T (translateSchwartz (-x) ψ)`;
4. apply the local continuous EOW theorem to each regularized pair, with a
   domain chosen uniformly from the nested-box/support-radius data;
5. pass to chart-coordinate smoothing kernels by defining
   `Gchart ψ w = G (localEOWRealLinearKernelPushforwardCLM ys hli ψ) w`; this
   is the only family used in the covariance and recovery step;
6. build a genuine global mixed Schwartz CLM `K` by fixed cutoffs:
   multiply the complex-chart variable by a cutoff equal to one on the local
   covariance window and multiply each real slice by a cutoff equal to one on
   the kernel support ball.  This CLM represents
   `φ,ψ ↦ ∫ z, Gchart ψ z * φ z` only for tests whose supports lie in the
   declared local windows;
7. prove `ProductKernelRealTranslationCovariantLocal K Ucov rbig`, using the
   shifted-overlap covariance of `Gchart` and the two support hypotheses in
   the local covariance predicate.  No global covariance is claimed;
8. run a local fiber-descent theorem, with all fiber translations guarded by
   the support margin `Udesc + closedBall 0 (r + rη) ⊆ Ucov`, to obtain a
   local distribution `Hdist` satisfying the descent identity on product tests
   supported in `Udesc`;
9. prove `IsDistributionalHolomorphicOn Hdist Udesc` from the local descent
   identity, the product-kernel `∂bar` integral identity, and the checked
   approximate identity;
10. use `distributionalHolomorphic_regular`, the checked pointwise
   representation bridge restricted to `Ucore ⊂ Udesc`, and the checked
   delta-limit wedge agreement to recover one holomorphic envelope agreeing
   with the original wedge functions.

A naive "mollify and pass to the limit" route is not sufficient, because the
continuous-EOW neighborhood may shrink with the kernel if support margins are
not fixed and because a family of regularized envelopes must first be shown to
come from one translation-covariant kernel.  The kernel step is exactly the
mathematical content of Streater-Wightman Theorem 2-16.  The earlier
finite-order primitive draft is not the active route: separately normalized
holomorphic primitives in opposite wedges can differ by kernel terms after
taking boundary values, and the false shortcut
`D_1^M ... D_m^M h = 0 -> h is polynomial` is invalid in several variables.

Local reference check: `references/pct-spin-and-statistics-and-all-that-9781400884230_compress.pdf`,
Theorem 2-16 (printed pp. 81-83), gives exactly this regularization proof:
smear the two wedge functions by a compactly supported real test function,
apply continuous EOW to the resulting continuous-boundary functions, prove the
regularized extensions form a translation-covariant distributional kernel by
the Schwartz nuclear theorem, and recover the holomorphic extension by a delta
sequence.  Theorem 2-17 is the zero-boundary uniqueness corollary; it remains a
useful consumer but is not a substitute for constructing the full envelope.

Infrastructure audit after `agents_chat.md` #1291:

1. The first continuous-layer extraction slice is now checked:
   `SCV.local_eow_extension` and `SCV.local_extensions_consistent` are public
   theorems in `SCV/TubeDomainExtension.lean`.  Their global-tube hypotheses
   mean they still cannot be applied directly to OS45 local open sets
   `Ωplus/Ωminus`, but their local Cauchy-polydisc construction, patching, and
   overlap-consistency proof are now an accessible Lean substrate to reuse.
   The finite-dimensional local-wedge simplex support is also checked in
   `SCV/LocalContinuousEOW.lean`: `SCV.localEOWCoefficientSimplex`,
   `SCV.localEOWSimplexDirections`,
   `SCV.isCompact_localEOWCoefficientSimplex`,
   `SCV.isCompact_localEOWSimplexDirections`,
   `SCV.localEOWSimplexDirections_subset_cone`, and
   `SCV.localEOW_positive_imag_normalized_mem_simplex`.  The actual local
   chart-membership replacements for the global tube lemmas are now checked as
   `SCV.localEOW_chart_positive_polywedge_mem` and
   `SCV.localEOW_chart_negative_polywedge_mem`; the downstream-ready common
   radius package is `SCV.localEOW_chart_twoSided_polywedge_mem`.  The public
   chart layer is also checked as `SCV.localEOWRealChart`,
   `SCV.localEOWChart`, `SCV.continuous_localEOWRealChart`,
   `SCV.isCompact_localEOWRealChart_image`, `SCV.localEOWChart_real_imag`, and
   `SCV.localEOWChart_twoSided_polywedge_mem`.
2. `SCV/DistributionalUniqueness.lean` already supplies translation,
   compact-support stability, real-mollification holomorphy, approximate
   identity convergence, and zero-boundary uniqueness tools.  The local
   distributional EOW envelope should reuse these lemmas.  The downstream
   kernel-recovery and delta-limit half of the nonzero-envelope argument is
   now checked in `SCV/DistributionalEOWKernelRecovery.lean`, ending at
   `SCV.regularizedEnvelope_chartEnvelope_from_productKernel`.  What remains
   to add is the upstream regularized-family half of Streater-Wightman
   Theorem 2-16: continuous boundary values for each regularization, uniform
   local continuous-EOW domains, linearity/continuity in the smoothing kernel,
   real-translation covariance from uniqueness, and the exact
   product-kernel representation interface that supplies
   `K,G,hcov,hG_holo,hK_rep` to the checked chart assembly theorem.
3. Every new helper below is either an extraction of existing repo SCV code
   (`local_eow_extension`, `local_extensions_consistent`), a standard
   finite-dimensional chart/compactness lemma, an existing real-mollification
   theorem from `DistributionalUniqueness.lean`, or the standard
   Streater-Wightman/Jost kernel-theorem step used in the classical
   distributional EOW proof.

Source ledger for the internal helper list:

| Helper | Source / justification |
|---|---|
| `localWedge_truncated_maps_compact_subcone` | Direct compact-set use of the local wedge hypothesis. |
| `localEOW_choose_cone_basis` | Existing `open_set_contains_basis` in `SCV/TubeDomainExtension.lean`. |
| `localEOWCoefficientSimplex`, `localEOWSimplexDirections`, `isCompact_localEOWCoefficientSimplex`, `isCompact_localEOWSimplexDirections`, `localEOWSimplexDirections_subset_cone`, `localEOW_positive_imag_normalized_mem_simplex` | Checked in `SCV/LocalContinuousEOW.lean`: compact closed coefficient simplex, compact image under the finite-dimensional chart-direction map, convex-combination inclusion in the cone, and normalization of positive imaginary chart directions. |
| `localEOWRealChart`, `localEOWChart`, `continuous_localEOWRealChart`, `isCompact_localEOWRealChart_image`, `localEOWChart_real_imag`, `localEOWChart_twoSided_polywedge_mem` | Checked in `SCV/LocalContinuousEOW.lean`: public chart notation matching the private `Phi` shape in `TubeDomainExtension.lean`, compactness of real-chart images, decomposition of `localEOWChart x0 ys (u + i v)`, and the direct two-sided local wedge membership theorem in chart coordinates. |
| `localEOWRealLinearPart`, `localEOWRealChart_eq_x0_add_linearPart`, `localEOWRealChart_sub`, `localEOWRealChart_add`, `localEOWChart_sub_realEmbed`, `localEOWChart_add_realEmbed`, `localEOWRealLinearCLE`, `localEOWRealLinearCLE_apply`, `localEOWRealLinearPullbackCLM`, `localEOWRealLinearPullbackCLM_apply`, `KernelSupportWithin.localEOWRealLinearPullbackCLM`, `localEOWRealLinearPushforwardCLM`, `localEOWRealLinearPushforwardCLM_apply`, `KernelSupportWithin.localEOWRealLinearPushforwardCLM`, `localEOWRealLinearKernelPushforwardCLM`, `localEOWRealLinearKernelPushforwardCLM_apply`, `KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM`, `KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_translateSchwartz`, `localEOWAffineTestPushforwardCLM`, `localEOWAffineDistributionPullbackCLM` | Checked in `SCV/LocalEOWChartLinear.lean`: explicit affine/linear bookkeeping for the local EOW chart.  A coordinate displacement `v` in the Rudin chart moves the original real edge by `localEOWRealLinearPart ys v`, not by `v` unless `ys` is the standard basis.  If `ys` is linearly independent, `localEOWRealLinearCLE ys hli` is the corresponding continuous linear equivalence and `localEOWRealLinearPullbackCLM ys hli ψ u = ψ (localEOWRealLinearPart ys u)` is the checked Schwartz test-function pullback.  Pullback of `KernelSupportWithin ψ r` is supported in radius `‖(localEOWRealLinearCLE ys hli).symm.toContinuousLinearMap‖ * r`.  The chart-to-original pushforward has apply theorem `localEOWRealLinearPushforwardCLM ys hli φ y = φ ((localEOWRealLinearCLE ys hli).symm y)` and transports support to radius `‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * r`.  The Jacobian-normalized kernel pushforward has apply theorem `localEOWRealLinearKernelPushforwardCLM ys hli φ y = ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) * φ ((localEOWRealLinearCLE ys hli).symm y)`; the scalar determinant factor does not enlarge support, and a translated chart kernel has support radius `‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * (r + ‖a‖)`. |
| `localEOW_chart_real_box` | Finite-dimensional topology: open preimage under a linear equivalence contains a small axis box. |
| `localEOW_chart_positive_polywedge_mem`, `localEOW_chart_negative_polywedge_mem`, `localEOW_chart_twoSided_polywedge_mem` | Checked in `SCV/LocalContinuousEOW.lean`: local replacements for the existing `Phi_pos_in_tube` / `Phi_neg_in_tube` lemmas in `TubeDomainExtension.lean`, using `hlocal_wedge` on the compact real box and compact chart-direction simplex.  The two-sided theorem preserves the single radius supplied by `hlocal_wedge`. |
| `localEOW_pullback_boundary_value` | Standard distribution pullback under an affine real-linear equivalence with Jacobian. |
| `localEOW_uniform_slowGrowth_order` | Compactness plus maxima of the two local slow-growth orders. |
| `localEOW_nested_axis_boxes`, `localEOW_support_margin` | Finite-dimensional topology: choose `B0 ⋐ B1 ⋐ E` and kernel-support radius `r` so `B0 + supp ψ ⊆ B1`. |
| `continuousAt_localEOWSmp_param` | Next checked helper for `local_continuous_edge_of_the_wedge_envelope`: local public replacement for the private `scaledMoebiusProd_continuousAt` in `TubeDomainExtension.lean`.  It proves continuity in the Rudin parameter `w` of `w ↦ localEOWSmp δ w l` on the unit-radius denominator domain. |
| `exists_localRudin_coordinate_update_margin` | Next checked helper for `local_continuous_edge_of_the_wedge_envelope`: finite-dimensional metric margin used by the parametric-integral theorem.  If `z` is inside `ball 0 (δ / 2)`, it chooses `ε' > 0` so changing one coordinate by distance at most `2ε'`, and every Cauchy circle centered within `ε'` with radius `ε'`, stays inside the same ball. |
| `differentiableAt_localRudin_parametric_integral` | Next checked helper for `local_continuous_edge_of_the_wedge_envelope`: public replacement for the private Cauchy-estimate/Leibniz lemma `differentiableAt_parametric_integral`.  It proves holomorphy of one coordinate of the Rudin integral from a uniform bound, a local update margin, a.e. measurability, pointwise holomorphy away from the two circle-boundary angles, and vanishing on `sin θ = 0`. |
| `exists_localContinuousEOW_chart_window` | Next checked helper for `local_continuous_edge_of_the_wedge_envelope`: chooses the actual local Rudin chart data at a real edge point.  It combines `open_set_contains_basis`, `localEOWRealChart_closedBall_subset`, `localEOWChart_twoSided_polywedge_mem`, and `exists_localEOWChart_smp_delta` to return a cone basis, a real closed ball inside `E`, a two-sided local polywedge radius, and one `δ` whose Rudin arcs stay in `Ωplus`/`Ωminus`. |
| `localEOWChart_smp_upper_mem_of_delta_on_sphere`, `localEOWChart_smp_lower_mem_of_delta_on_sphere` | Next checked helpers for the local Rudin envelope integral: unlike `localEOWChart_smp_upper_mem_of_delta`, these allow a complex Rudin center `w`.  If `w ∈ closedBall 0 (δ/2)` and `‖l‖ = 1` with `Im l` positive/negative, then the scaled Möbius image maps into `Ωplus`/`Ωminus`.  This is the missing local replacement for the global `Phi_pos_in_tube`/`Phi_neg_in_tube` use in holomorphy of the Rudin integral. |
| `localRudinIntegrand`, `localRudinIntegral`, `localRudinEnvelope`, `aestronglyMeasurable_localRudinIntegrand`, `continuousAt_localRudinIntegrand_param`, `continuousAt_localRudinIntegral_of_bound`, `differentiableAt_localRudinIntegrand_update`, `localRudinIntegrand_zero_of_sin_eq_zero`, `differentiableAt_localRudinIntegral_of_bound`, `differentiableOn_localRudinIntegral_of_bound`, `differentiableOn_localRudinEnvelope_of_bound`, `exists_bound_localRudinIntegrand`, `differentiableOn_localRudinEnvelope`, `localRudinEnvelope_eq_boundary_of_real` | Checked in `SCV/LocalContinuousEOWEnvelope.lean`: the actual circle integrand used to define the local coordinate envelope, its integral and normalized envelope, its measurability on `[-π,π]`, pointwise continuity in the Rudin center, dominated continuity of the integral, coordinatewise holomorphy off the two boundary angles, its zero value at the boundary angles, coordinatewise holomorphy of the integral once a uniform compact bound is supplied, Osgood joint holomorphy on the coordinate ball, the compact-bound theorem itself, the final bound-free holomorphy theorem for the local Rudin envelope, and the real-boundary mean-value identity in terms of `localRudinEnvelope`.  The compact-bound proof is the local version of the `G_bound` block in `TubeDomainExtension.lean`, with boundary branch `bv` on the real edge. |
| `localEOWLine`, `localEOWLine_im`, `localEOWLine_I`, `localEOWLine_real_im_zero`, `differentiable_localEOWLine`, `localEOWLine_zero_mem_ball`, `localEOWLine_norm_le_delta_ten_of_norm_le_two`, `localEOWLine_re_closedBall_of_norm_le_two`, `localEOWChart_line_upper_mem_of_delta`, `localEOWChart_line_lower_mem_of_delta`, `localEOWChart_line_upper_mem_of_delta_of_negative`, `localEOWChart_line_lower_mem_of_delta_of_negative`, `localEOWLine_affine_real_combo`, `localEOWLine_chart_real`, `tendsto_localEOWLine_upper_to_boundaryValue`, `tendsto_localEOWLine_lower_to_boundaryValue`, `tendsto_localEOWLine_upper_to_boundaryValue_of_negative`, `tendsto_localEOWLine_lower_to_boundaryValue_of_negative`, `localRudinEnvelope_line_eq_boundary_of_real`, `localRudinEnvelope_eq_plus_on_positive_ball`, `localRudinEnvelope_eq_minus_on_negative_ball` | Checked across `SCV/LocalContinuousEOWEnvelope.lean` and `SCV/LocalContinuousEOWSideAgreement.lean`: the local line-geometry and one-variable identity-theorem package replacing the inline `L(z)` estimates in `rudin_orthant_extension`.  For `ζ ∈ ball 0 (δ/2)`, `L(z)_j = Re ζ_j + z Im ζ_j`; `L` is differentiable, affine over real convex combinations, and `L(0)` remains in the small Rudin ball.  If `‖z‖ ≤ 2`, every coordinate is bounded by `δ * 10` and the real part stays in the `ρ`-chart ball.  Positive `ζ` maps upper/lower half-planes to the plus/minus sides, negative `ζ` swaps the sides, and the Rudin envelope is now proved to agree with the corresponding side branch on the strict positive/negative coordinate balls. |
| `localEOWChart_ball_positive_mem_of_delta`, `localEOWChart_ball_negative_mem_of_delta` | Checked helpers for the side-agreement part of the local continuous EOW theorem: the small coordinate ball with strictly positive, respectively strictly negative, imaginary coordinates maps into `Ωplus`, respectively `Ωminus`.  These are the honest local side domains on which agreement is first proved; arbitrary extra components of an open `Ωplus/Ωminus` are not silently included. |
| `localRealMollifySide_holomorphicOn_of_translate_margin` | Checked in `SCV/LocalDistributionalEOW.lean`: local version of `differentiableOn_realMollify_tubeDomain`; real-direction convolution of a holomorphic wedge function is holomorphic on the shrunken wedge whenever the support margin keeps all translates of the real-kernel support inside the original local wedge. |
| `KernelSupportWithin.add`, `KernelSupportWithin.smul` | Checked in `SCV/DistributionalEOWSupport.lean`: the fixed-radius smoothing-kernel class is closed under addition and scalar multiplication.  These are the support-side inputs for proving linearity of the explicit fixed-window family on the supported-kernel class. |
| `KernelSupportWithin.smulLeftCLM`, `KernelSupportWithin.smulLeftCLM_of_leftSupport`, `KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall` | Checked in `SCV/DistributionalEOWSupport.lean`: multiplying by a Schwartz-side cutoff preserves support either from the original kernel or from the cutoff itself, and a cutoff equal to `1` on `closedBall 0 r` acts as the identity on kernels with `KernelSupportWithin ψ r`.  These are the cutoff support lemmas needed to extend supported-kernel identities to full Schwartz-space CLMs without introducing a `SmallKernelSpace` wrapper. |
| `exists_schwartz_cutoff_eq_one_on_closedBall` | Checked in `SCV/DistributionalEOWSupport.lean`: a direct `ContDiffBump` construction of a Schwartz cutoff equal to `1` on `closedBall 0 r` and topologically supported in `closedBall 0 rLarge`, for `0 < r < rLarge`.  This replaces the former blueprint-only `KernelCutoff`/`cutoffKernelCLM` placeholders. |
| `exists_complexChart_schwartz_cutoff_eq_one_on_closedBall`, `SupportsInOpen.smulLeftCLM_eq_of_eq_one_on` | Checked in `SCV/DistributionalEOWSupport.lean`: the complex-chart analogue of the closed-ball cutoff construction and the support-window cutoff-removal lemma.  These are the first helper layer for the local pairing CLM; the complex-chart cutoff makes the global mixed Schwartz CLM compactly supported in the chart variable, and the `SupportsInOpen` removal lemma proves the cutoff is invisible on product tests supported in `Ucov`. |
| `schwartzPartialEval₁CLM`, `schwartzPartialEval₁CLM_apply`, `schwartzPartialEval₁CLM_tensorProduct₂` | Checked in `SCV/DistributionalEOWKernel.lean`: fixed-chart partial evaluation `F ↦ (t ↦ F (z,t))` is a genuine continuous linear map on mixed Schwartz tests, built from `SchwartzMap.compCLM` along `t ↦ (z,t)`.  The apply and tensor-product specialization theorems are checked. |
| `iteratedFDeriv_partialEval₁_eq_compContinuousLinearMap_inr`, `norm_iteratedFDeriv_partialEval₁_le`, `schwartzPartialEval₁CLM_seminorm_le`, `schwartzPartialEval₁CLM_compactSeminormBound` | Checked in `SCV/SchwartzPartialEval.lean` and `SCV/DistributionalEOWKernel.lean`: first-variable partial evaluation has the expected derivative formula through `ContinuousLinearMap.inr`, each fixed partial evaluation is bounded by the corresponding mixed Schwartz seminorm, and the compact finite-seminorm bound is checked with exact witnesses `s' = s` and `C = 1`. |
| `exists_closedBall_integral_clm_of_continuousOn` | Checked in `SCV/DistributionalEOWSupport.lean`: integration over `Metric.closedBall 0 R` against a coefficient that is continuous on that closed ball is a continuous complex-linear functional on real-chart Schwartz kernels, with the explicit seminorm bound using `SchwartzMap.seminorm ℂ 0 0`.  This is the real-radius local replacement for the older natural-radius/global-continuity compact-ball integral CLM. |
| `exists_realMollifyLocal_valueCLM_of_closedBall` | Checked in `SCV/LocalDistributionalEOW.lean`: for a fixed chart point `z`, if `F` is continuous on a side domain containing all translates `z + realEmbed t` for `t ∈ closedBall 0 r`, then `ψ ↦ realMollifyLocal F ψ z` is represented on `KernelSupportWithin ψ r` by a continuous complex-linear functional.  The proof uses the compact-ball integral CLM plus the support condition to replace the full integral by the closed-ball integral. |
| `exists_bound_realMollifyLocal_smulLeftCLM` | Checked in `SCV/LocalDistributionalEOW.lean`: after multiplying kernels by a fixed Schwartz cutoff whose topological support is inside `closedBall 0 r`, each side mollifier value is bounded by `C * SchwartzMap.seminorm ℂ 0 0 ψ`.  This is the explicit seminorm estimate needed before integrating the side value CLMs through the local Rudin envelope. |
| `exists_bound_localRudinEnvelope_smulLeftCLM_of_side_bounds` | Checked in `SCV/LocalDistributionalEOW.lean`: the direct Rudin-circle integration estimate.  If the plus and minus arc values are already uniformly bounded by the zeroth Schwartz seminorm after a fixed cutoff, then the normalized local Rudin envelope value is also bounded by that seminorm.  This is useful away from the real-edge endpoints, but by itself is too strong for a general distributional boundary value. |
| `exists_schwartz_bound_normalized_intervalIntegral_clm_family` | Checked in `SCV/LocalDistributionalEOW.lean`: Banach-Steinhaus plus interval integration.  A pointwise bounded interval family of real-linear Schwartz CLMs has a single finite Schwartz-seminorm bound after normalized integration over `[-π,π]`.  This is the endpoint-facing quantitative theorem needed for the value-CLM construction. |
| `exists_localRudinIntegrand_smulLeftCLM_clmFamily` | Checked in `SCV/LocalDistributionalEOW.lean`: for fixed `w` and cutoff `χ`, constructs the real-linear CLM family in the Rudin circle parameter.  Positive angles use the plus side value CLM precomposed with cutoff multiplication, negative angles use the minus side value CLM, and boundary angles are zero.  Pointwise boundedness is obtained from the checked compact bound for the continuous local EOW integrand. |
| `exists_schwartz_bound_localRudinEnvelope_smulLeftCLM_value` | Checked in `SCV/LocalDistributionalEOW.lean`: for each coordinate-ball point `w`, the actual cutoff envelope value `ψ ↦ localRudinEnvelope ... (χ • ψ) w` is bounded by one finite Schwartz seminorm.  This is the quantitative endpoint estimate needed for `SchwartzMap.mkCLMtoNormedSpace`. |
| `regularizedEnvelope_valueCLM_of_cutoff` | Checked in `SCV/LocalDistributionalEOW.lean`: for each coordinate-ball point `w`, constructs the complex continuous linear functional `Lw` represented by `ψ ↦ localRudinEnvelope ... (χ • ψ) w`.  The proof uses the finite seminorm bound plus checked additivity and complex homogeneity of the fixed-window family. |
| `regularizedLocalEOW_originalFamily_compactValueCLM` | Checked in `SCV/LocalDistributionalEOW.lean`: chooses the checked per-point value CLMs over a compact chart window and proves one common finite Schwartz-seminorm bound by Banach-Steinhaus over the closed-ball subtype.  Pointwise boundedness comes from a single `exists_bound_localRudinIntegrand` application for each fixed cutoff test, uniformly over the full `δ / 2` Rudin ball. |
| `integrable_realMollifyLocal_integrand_of_translate_margin` | Checked in `SCV/LocalDistributionalEOW.lean`: compact kernel support plus local holomorphy/continuity on all real translates gives Bochner integrability of `t ↦ F (z + realEmbed t) * ψ t`.  This discharges the honest integrability hypothesis in `realMollifyLocal_add_of_integrable` on the side domains. |
| `localRealMollify_commonContinuousBoundary_of_clm` | Checked extraction step: if the plus/minus slice CLMs converge pointwise to the same chart distribution and correctly evaluate the translated kernels appearing in `realMollifyLocal`, then the regularized plus/minus sides have the same continuous boundary value `x ↦ T (translateSchwartz (-x) ψ)`.  The remaining hard input is constructing these slice CLMs from the OS-II distributional boundary-value hypotheses, not assuming common continuous boundary. |
| `realMollifyLocal_translateSchwartz` | Checked in `SCV/LocalDistributionalEOW.lean`: translating the real smoothing kernel by `a` is exactly the same as evaluating the original real mollifier at `z - realEmbed a`.  This is the change-of-variables input for the fixed-window family covariance proof. |
| `realMollifyLocal_localEOWRealLinearKernelPushforwardCLM` | Checked in `SCV/LocalDistributionalEOW.lean`: applying `realMollifyLocal` to the Jacobian-normalized chart-kernel pushforward equals the chart-coordinate integral `∫ u, F (z + realEmbed (localEOWRealLinearPart ys u)) * φ u`.  This is the chart-linear change-of-variables theorem needed before proving covariance for the regularized family. |
| `localEOWShiftedWindow`, `isOpen_localEOWShiftedWindow`, `convex_localEOWShiftedWindow`, `isPreconnected_localEOWShiftedWindow`, `exists_positive_imag_mem_localEOWShiftedWindow_of_norm_lt` | Checked in `SCV/LocalDistributionalEOW.lean`: the honest shifted-overlap domain for local covariance is `Metric.ball 0 (δ / 2) ∩ {w | w - realEmbed a ∈ Metric.ball 0 (δ / 2)}`.  It is open, convex, and preconnected, so the identity theorem can propagate equality from a positive-imaginary seed in the overlap.  The seed exists whenever `‖a‖ < δ / 4`, using the constant imaginary point with imaginary part `δ / 8` and `norm_realEmbed_le`. |
| `norm_realEmbed_eq` | Checked in `SCV/DistributionalEOWApproxIdentity.lean`: the finite sup norm of the complex-chart real embedding equals the original real sup norm.  The local covariance proof uses it to convert two support points `u` and `u - realEmbed a` in the covariance ball into the real shift bound `‖a‖ < δ / 4`. |
| `SupportsInOpen.complexTranslateSchwartz_of_image_subset` | Checked in `SCV/DistributionalEOWSupport.lean`: complex-chart translation transports compact support by inverse translation and maps the translated topological support into a target open set under an explicit image hypothesis.  This is the support half of the direct local descent averaging theorem. |
| `regularizedEnvelope_productKernel_dbar_eq_zero_local`, `translationCovariantKernel_distributionalHolomorphic_local` | Checked in `SCV/DistributionalEOWRepresentative.lean`: localized versions of the product-kernel `∂bar` annihilation theorem and the distributional-holomorphy passage.  They consume separated domains `Udesc ⊆ Ucov ⊆ U0`, local product-test descent, and approximate-identity convergence; they are not hidden hypotheses in the recovery consumer. |
| `regularizedLocalEOW_fixedKernelEnvelope_from_clm` | Checked in `SCV/LocalDistributionalEOW.lean`: for one compactly supported smoothing kernel, combines the local real-mollifier holomorphy margins, the CLM common-boundary extraction, and the checked coordinate local continuous EOW theorem to produce the local coordinate envelope with strict positive/negative side agreements and uniqueness.  This is the fixed-kernel bridge; it does not yet prove linearity/continuity in the kernel or construct the product kernel `K`. |
| `regularizedLocalEOW_fixedWindowEnvelope_from_clm` | Checked in `SCV/LocalDistributionalEOW.lean`: the same fixed-kernel bridge, but with the Rudin chart data `ys, ρ, r, δ` supplied once instead of existentially chosen.  Its output is the explicit function `localRudinEnvelope δ x0 ys (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)` with holomorphy, strict side agreements, real-edge identity, and uniqueness.  This is required before building a coherent family `G ψ`; otherwise Lean could choose different local charts for different kernels. |
| `regularizedLocalEOW_family_from_fixedWindow` | Checked in `SCV/LocalDistributionalEOW.lean`: packages the explicit fixed-window family `G ψ w = localRudinEnvelope δ x0 ys (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ) w` for every supported smoothing kernel.  It gives the exact family-level holomorphy, strict side-agreement, real-edge identity, and uniqueness facts needed before proving linearity, covariance, and the product-kernel construction. |
| `regularizedLocalEOW_family_add` | Checked in `SCV/LocalDistributionalEOW.lean`: additivity of the explicit fixed-window family on the supported-kernel class.  The proof uses `KernelSupportWithin.add`, side-domain additivity of `realMollifyLocal`, and the fixed-window uniqueness clause; it does not use real-linear slice CLMs as a substitute for complex-linearity. |
| `regularizedLocalEOW_family_smul` | Checked in `SCV/LocalDistributionalEOW.lean`: complex homogeneity of the explicit fixed-window family on the supported-kernel class.  The proof uses `KernelSupportWithin.smul`, `realMollifyLocal_smul`, and the same fixed-window uniqueness clause. |
| `realMollifyLocal_add_of_integrable`, `realMollifyLocal_smul` | Checked in `SCV/LocalDistributionalEOW.lean`: additivity and complex homogeneity of the real-direction mollifier in the smoothing kernel.  Additivity carries the honest Bochner-integrability hypotheses; complex homogeneity follows from `integral_smul`.  These lemmas avoid faking complex linearity through the currently real-linear slice functionals `Tplus/Tminus`. |
| `realMollifyLocal_add_of_translate_margin` | Checked in `SCV/LocalDistributionalEOW.lean`: side-domain additivity of the real mollifier, with the integrability hypotheses discharged by compact kernel support and translate-margin membership in the side holomorphy domain. |
| `exists_seminorm_bound_complexRealFiberIntegralRaw_zero` | Checked in `SCV/DistributionalEOWBoundaryProductKernel.lean`: the generic zeroth-derivative finite-seminorm bound for `complexRealFiberIntegralRaw`, uniform in the mixed Schwartz function.  The codomain is allowed to be any complete complex normed space with the compatible real scalar structure; this is necessary because the derivative induction passes through continuous-linear-map-valued Schwartz functions. |
| `basePrecompCLM`, `baseFDerivSchwartzCLM`, `exists_seminorm_bound_baseFDerivSchwartz` | Checked in `SCV/DistributionalEOWBoundaryProductKernel.lean`: the base-coordinate derivative field is now a genuine continuous complex-linear map on mixed Schwartz space, and every finite supremum of target Schwartz seminorms of `baseFDerivSchwartz F` is controlled by finitely many source seminorms of `F`. |
| `exists_seminorm_bound_complexRealFiberIntegralRaw_deriv` | Checked in `SCV/DistributionalEOWBoundaryProductKernel.lean`: the full derivative-induction finite-seminorm estimate for the raw real-fiber integral.  The proof uses the generic zeroth-order bound, the checked `fderiv_complexRealFiberIntegralRaw_eq`, and the finite-seminorm continuity of `baseFDerivSchwartzCLM`. |
| `complexRealFiberIntegralCLM`, `complexRealFiberIntegralCLM_apply` | Checked in `SCV/DistributionalEOWBoundaryProductKernel.lean`: real-fiber integration is now a continuous complex-linear map `SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] SchwartzMap (ComplexChartSpace m) ℂ`, with pointwise formula `∫ t, F (z,t)`.  Additivity and scalar compatibility are Bochner-integral linearity; smoothness is `contDiff_complexRealFiberIntegralRaw`; the `SchwartzMap.mkCLM` bound is `exists_seminorm_bound_complexRealFiberIntegralRaw_deriv`. |
| `boundaryProductKernel_from_fiberIntegralCLM` | Checked in `SCV/DistributionalEOWBoundaryProductKernel.lean`: the algebraic product-kernel construction.  Given a real-fiber integration operator as a genuine continuous linear map with pointwise formula, composing it with the real-convolution shear and `Tchart` gives a product kernel `K` with `ProductKernelRealTranslationCovariantGlobal K` and `K (schwartzTensorProduct₂ φ ψ) = Tchart (realConvolutionTest φ ψ)`. |
| `boundaryProductKernel_from_complexRealFiberIntegralCLM` | Checked in `SCV/DistributionalEOWBoundaryProductKernel.lean`: the previous conditional product-kernel algebra instantiated with the now-checked `complexRealFiberIntegralCLM`.  Given a complex-chart distribution `Tchart : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ`, it constructs the associated mixed product kernel with product-test representation and real-translation covariance.  It does **not** itself construct `Tchart` from the real-edge distributional boundary data; theorem 2 still needs the regularized-family/product-bilinear step that produces the `K,G,hK_rep` data consumed by `regularizedEnvelope_chartEnvelope_from_productKernel`. |
| `regularizedLocalEOW_productKernel_from_continuousEOW` | Retired as a one-shot target under its old global-covariance shape.  The local fixed-window family can supply linearity, value CLMs, and shifted-overlap covariance, but a local pairing extended by cutoff does not honestly give `ProductKernelRealTranslationCovariantGlobal K`.  For the pure-SCV local distributional EOW theorem, the route is now the local descent package: construct a localized mixed CLM, prove `ProductKernelRealTranslationCovariantLocal` under explicit support/margin hypotheses, descend locally to `Hdist`, and feed a local recovery consumer.  A genuinely global covariant `K` may still be sourced later from OS/Wightman translation-invariant data, but that is not the proof of the QFT-free SCV theorem. |
| `regularizedEnvelope_deltaLimit_agreesOnWedges` | Approximate-identity recovery: once kernel recovery has produced a holomorphic `H`, compactly supported approximate identities show `H` agrees with the original plus/minus wedge functions on the shrunken wedge pieces. |
| `local_continuous_edge_of_the_wedge_envelope` | Checked in `SCV/LocalContinuousEOWSideAgreement.lean`: local coordinate-ball continuous EOW extraction.  It packages the chart window, the Rudin envelope, holomorphy on `ball 0 (δ/2)`, agreement on the explicit strict positive/negative side balls, and real-boundary agreement on the coordinate real slice.  It intentionally does not claim agreement on arbitrary extra components of `Ωplus` or `Ωminus`. |
| `chartDistributionalEOW_local_envelope` | Local distributional EOW envelope on one chart, obtained from the regularized-envelope family and delta-limit recovery. |
| `distributionalEOW_extensions_compatible`, `localDistributionalEOW_patch_extensions` | Reuse the now-public `SCV.local_extensions_consistent` identity-theorem pattern and the global patching pattern in `edge_of_the_wedge_theorem`. |

Do not write this as "apply `SCV.edge_of_the_wedge_theorem`" without further
work.  The checked theorem `SCV.edge_of_the_wedge_theorem` is stated for global
tubes `TubeDomain C` and `TubeDomain (-C)`, while the OS45 data are local wedge
neighborhoods inside open sets `Ωplus/Ωminus`.  Important side-component
discipline: `hlocal_wedge` only says that the explicit truncated positive and
negative wedge pieces lie inside `Ωplus` and `Ωminus`; it does **not** imply
that every possible extra component of `U ∩ Ωplus` or `U ∩ Ωminus` is attached
to the edge.  Therefore the implementation must first prove agreement on the
constructed small side domains, such as
`{w ∈ ball 0 (δ / 2) | ∀ j, 0 < (w j).im}` and its negative companion,
transported by `localEOWChart`.  A theorem claiming agreement on all of
`U ∩ Ωplus` or `U ∩ Ωminus` needs an additional side-connectedness hypothesis
or an OS45-specific connected-component restriction.  The theorem-2 route only
needs the explicit side-domain agreement for the regularized kernels and the
later BHW common-chart connectedness step.

Coordinate discipline for the product-kernel stage: the checked fixed-window
family is written in the Rudin coordinate `w`, but the side mollifier
`realMollifyLocal Fplus ψ (localEOWChart x0 ys w)` still uses the original
real-edge variable unless the boundary distribution and smoothing kernels have
already been pulled back by the real affine chart.  The checked identities in
`SCV/LocalEOWChartLinear.lean` make the obstruction explicit:

```lean
localEOWChart x0 ys (w - realEmbed v) =
  localEOWChart x0 ys w - realEmbed (localEOWRealLinearPart ys v)
```

Thus the product-kernel theorem must not claim covariance under
`translateSchwartz v` on the original real-edge kernels merely from translating
the Rudin coordinate by `v`.  The checked map
`localEOWRealLinearPullbackCLM ys hli` supplies the test-function composition
part of the chart pullback, and
`KernelSupportWithin.localEOWRealLinearPullbackCLM` supplies the induced
support-radius transport.  In the other direction,
`localEOWRealLinearPushforwardCLM` and
`localEOWRealLinearKernelPushforwardCLM` push chart-coordinate kernels to the
original real edge; the latter includes the inverse absolute determinant factor
needed for the change of variables and preserves the same operator-norm support
radius as the unnormalized pushforward.  The corresponding mollifier
change-of-variables theorem is now checked as
`realMollifyLocal_localEOWRealLinearKernelPushforwardCLM`, giving the exact
chart-coordinate integral after this Jacobian-normalized transport.  The
remaining implementation stage is to use this identity in the fixed-window
regularized family and product-kernel construction.  Only after that coordinate
conversion does the covariance hypothesis in
`regularizedEnvelope_chartEnvelope_from_productKernel` have the correct
meaning.

The local theorem must first extract a local continuous EOW lemma from the
Cauchy-polydisc proof pattern in `SCV/TubeDomainExtension.lean`:

```lean
theorem local_continuous_edge_of_the_wedge_envelope
    {m : ℕ} (hm : 0 < m)
    (Ωplus Ωminus : Set (Fin m -> ℂ))
    (E C : Set (Fin m -> ℝ))
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hE_open : IsOpen E)
    (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C)
    (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ E ->
        ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (hFplus : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus : DifferentiableOn ℂ Fminus Ωminus)
    (bv : (Fin m -> ℝ) -> ℂ)
    (hbv_cont : ContinuousOn bv E)
    (hplus_bv :
      ∀ x ∈ E,
        Tendsto Fplus (nhdsWithin (realEmbed x) Ωplus) (nhds (bv x)))
    (hminus_bv :
      ∀ x ∈ E,
        Tendsto Fminus (nhdsWithin (realEmbed x) Ωminus) (nhds (bv x))) :
    (x0 : Fin m -> ℝ) (hx0 : x0 ∈ E) :
    ∃ ys : Fin m -> Fin m -> ℝ,
      (∀ j, ys j ∈ C) ∧ LinearIndependent ℝ ys ∧
      ∃ ρ : ℝ, 0 < ρ ∧
      ∃ r : ℝ, 0 < r ∧
      ∃ δ : ℝ, 0 < δ ∧
        δ * 10 ≤ ρ ∧
        (Fintype.card (Fin m) : ℝ) * (δ * 10) < r ∧
        (∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
          localEOWRealChart x0 ys u ∈ E) ∧
        (∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
          ∀ v : Fin m -> ℝ,
            (∀ j, 0 ≤ v j) ->
            0 < ∑ j, v j ->
            (∑ j, v j) < r ->
              localEOWChart x0 ys
                (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus) ∧
        (∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
          ∀ v : Fin m -> ℝ,
            (∀ j, v j ≤ 0) ->
            0 < ∑ j, -v j ->
            (∑ j, -v j) < r ->
              localEOWChart x0 ys
                (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) ∧
        ∃ F0 : (Fin m -> ℂ) -> ℂ,
          DifferentiableOn ℂ F0 (Metric.ball (0 : Fin m -> ℂ) (δ / 2)) ∧
          (∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2),
            (∀ j, 0 < (w j).im) ->
              localEOWChart x0 ys w ∈ Ωplus ∧
              F0 w = Fplus (localEOWChart x0 ys w)) ∧
          (∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2),
            (∀ j, (w j).im < 0) ->
              localEOWChart x0 ys w ∈ Ωminus ∧
              F0 w = Fminus (localEOWChart x0 ys w)) ∧
          (∀ u : Fin m -> ℝ,
            (fun j => (u j : ℂ)) ∈
              Metric.ball (0 : Fin m -> ℂ) (δ / 2) ->
              F0 (fun j => (u j : ℂ)) =
                bv (localEOWRealChart x0 ys u)) ∧
          (∀ G : (Fin m -> ℂ) -> ℂ,
            DifferentiableOn ℂ G (Metric.ball (0 : Fin m -> ℂ) (δ / 2)) ->
            (∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2),
              (∀ j, 0 < (w j).im) ->
                G w = Fplus (localEOWChart x0 ys w)) ->
            ∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2), G w = F0 w)
```

This is deliberately the coordinate-ball local theorem, not a claim of
agreement on all of `U ∩ Ωplus` or `U ∩ Ωminus`.  Agreement on larger side
components requires a separate connected-component/identity-theorem argument.

Its proof is now short from the checked Rudin substrate:

1. Apply `exists_localContinuousEOW_chart_window` to obtain
   `ys, ρ, r, δ, hE_mem, hplus, hminus` and the corresponding Rudin-arc
   side-membership facts.
2. Set
   `F0 = localRudinEnvelope δ x0 ys Fplus Fminus`.
3. Holomorphy of `F0` on `ball 0 (δ/2)` is exactly
   `differentiableOn_localRudinEnvelope`.
4. Positive side membership is
   `localEOWChart_ball_positive_mem_of_delta`; positive side agreement is
   `localRudinEnvelope_eq_plus_on_positive_ball`.
5. Negative side membership is
   `localEOWChart_ball_negative_mem_of_delta`; negative side agreement is
   `localRudinEnvelope_eq_minus_on_negative_ball`.
6. Real boundary agreement follows from `localRudinEnvelope_eq_boundary_of_real`
   with `w = fun j => (u j : ℂ)`.  The path condition is supplied by
   `localEOWSmp_re_mem_closedBall hδ hδρ` and `hE_mem`.
7. The uniqueness clause uses the ordinary identity theorem on the convex ball
   `ball 0 (δ/2)`.  The comparison function and `F0` are analytic by
   `differentiableOn_analyticAt`; they agree on a neighborhood of the explicit
   point `z0_j = (δ/4) I` inside the strict positive side ball.
   - lower chart membership when `Im l < 0`;
   - the finite sum bound needed by the local polywedge radius.
7. Use the checked Rudin transcript lemmas
   `localEOWSmp_zero`, `continuous_localEOWSmp_theta`,
   `localEOWSmp_im_zero_of_unit_real`,
   `localEOWChart_smp_realEdge_eq_of_unit_real`,
   `localEOWSmp_im_zero_of_real`,
   `localEOWChart_smp_realEdge_eq_of_real`,
   `continuousAt_localEOWSmp_of_norm_lt_two`, and
   `continuousAt_localEOWChart_smp_of_norm_lt_two`, together with the
   upper/lower half-plane differentiability lemmas
   `differentiableOn_localEOWChart_smp_upperHalfPlane_of_real` and
   `differentiableOn_localEOWChart_smp_lowerHalfPlane_of_real`, and the
   upper/lower boundary-filter lemmas
   `tendsto_localEOWChart_smp_upperHalfPlane_to_realEdge` and
   `tendsto_localEOWChart_smp_lowerHalfPlane_to_realEdge`, in the
   Cauchy/mean-value construction.  The unit-real lemmas handle the circle
   boundary in the Cauchy integral; the arbitrary-real and `‖l‖ < 2` lemmas
   handle the real interval in the one-variable boundary-value identity; the
   half-plane differentiability lemmas supply the holomorphic one-variable
   branches; and the boundary-filter lemmas transport the local wedge
   boundary hypotheses to the real edge.  Together they are the local
   replacements for the corresponding
   private `smp_zero`, `smp_theta_continuous`, `hsmp_ca_real`,
   `hgp_diff`/`hgm_diff`, `hgp_bv`/`hgm_bv`, and real-boundary facts inside
   `rudin_orthant_extension` and `rudin_mean_value_real`.  The real-line
   branch continuity needed by the `hbv_real` input is checked separately as
   `continuousAt_localEOWRealChart_smp_re_of_norm_lt_two` and
   `continuousAt_localEOWBoundaryValue_smp`.  The branch-level hypotheses for
   applying the local one-variable EOW theorem are checked as
   `differentiableOn_localEOWUpperBranch_smp_of_real`,
   `differentiableOn_localEOWLowerBranch_smp_of_real`,
   `tendsto_localEOWUpperBranch_smp_to_boundaryValue`, and
   `tendsto_localEOWLowerBranch_smp_to_boundaryValue`.
8. Reuse the checked Cauchy-polydisc construction and patching pattern from
   `local_eow_extension`, but with these local membership lemmas and the
   two `nhdsWithin (realEmbed x)` boundary hypotheses for `Ωplus` and
   `Ωminus`.

Implementation notes:

The extraction should start by copying the *shape* of the two private checked
lemmas in `SCV/TubeDomainExtension.lean`, not by inventing a new local EOW
wrapper.  The local analogue of `local_eow_extension` must return exactly the
same seven geometric/analytic fields:

```lean
∃ (P : Set (ComplexChartSpace m)) (F_loc : ComplexChartSpace m -> ℂ),
  IsOpen P ∧ Convex ℝ P ∧
  (∀ z ∈ P, (fun i => starRingEnd ℂ (z i)) ∈ P) ∧
  realEmbed x0 ∈ P ∧
  DifferentiableOn ℂ F_loc P ∧
  (∀ z ∈ P ∩ Ωplus, F_loc z = Fplus z) ∧
  (∀ z ∈ P ∩ Ωminus, F_loc z = Fminus z)
```

The existing global `edge_of_the_wedge_1d` theorem is not by itself the right
one-variable input for this local extraction: it assumes differentiability on
the full upper and lower half-planes, whereas the local Rudin map is controlled
only inside the disk
`Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2)`.  The next checked
one-variable theorem must therefore be local on that ball, while keeping the
same boundary-value hypotheses on `(a,b)`.  Its production surface is:

```lean
theorem local_edge_of_the_wedge_1d
    (a b : ℝ) (hab : a < b)
    (f_plus f_minus : ℂ -> ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus
      (Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2) ∩
        EOW.UpperHalfPlane))
    (hf_minus : DifferentiableOn ℂ f_minus
      (Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2) ∩
        EOW.LowerHalfPlane))
    (hcont_plus : ∀ x : ℝ, a < x -> x < b ->
      Filter.Tendsto f_plus
        (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (f_plus x)))
    (hcont_minus : ∀ x : ℝ, a < x -> x < b ->
      Filter.Tendsto f_minus
        (nhdsWithin (x : ℂ) EOW.LowerHalfPlane) (nhds (f_minus x)))
    (hmatch : ∀ x : ℝ, a < x -> x < b -> f_plus x = f_minus x)
    (hbv_cont : ∀ x0 : ℝ, a < x0 -> x0 < b ->
      Filter.Tendsto f_plus
        (nhdsWithin (x0 : ℂ) {c : ℂ | c.im = 0}) (nhds (f_plus x0))) :
    ∃ (U : Set ℂ) (F : ℂ -> ℂ),
      IsOpen U ∧ Convex ℝ U ∧
      (∀ z ∈ U, starRingEnd ℂ z ∈ U) ∧
      (∀ x : ℝ, a < x -> x < b -> (x : ℂ) ∈ U) ∧
      DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ EOW.UpperHalfPlane, F z = f_plus z) ∧
      (∀ z ∈ U ∩ EOW.LowerHalfPlane, F z = f_minus z) ∧
      Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2) ⊆ U
```

Lean proof transcript: define the glued function
`F z = if z.im > 0 then f_plus z else if z.im < 0 then f_minus z else f_plus z`
on the ball.  Continuity on real boundary points is exactly the same filter
decomposition as in `edge_of_the_wedge_1d`, using `hcont_plus`,
`hcont_minus`, `hmatch`, and `hbv_cont`; continuity off the real line uses the
local differentiability hypotheses on
`ball ∩ EOW.UpperHalfPlane` / `ball ∩ EOW.LowerHalfPlane`.  Holomorphy on the
ball minus the real line is immediate from the same local differentiability
hypotheses and eventual equality with the glued branch.  Then apply the
already checked `differentiableOn_of_continuous_off_real_1d` theorem from
`SeparatelyAnalytic.lean` to obtain holomorphy on the whole ball.  The output
sets `U` to the same ball, so openness, convexity, conjugation stability,
interval containment, and ball containment are direct.

The local analogue of `local_extensions_consistent` should keep the same
identity-theorem proof: if two local patches have a nonempty overlap, convexity
and conjugation invariance put a real midpoint in the overlap, and
`hlocal_wedge` supplies nearby plus-wedge points in the overlap.  Therefore the
two local extensions agree on a nonempty open plus-wedge subset, and analytic
continuation across the convex overlap gives equality everywhere on the
overlap.  This is the exact replacement for the current global
`nonempty_open_real_inter_tubeDomain` call; it is not an additional axiom.

1. `localWedge_truncated_maps_compact_subcone` is the uniform
   compact-real-support / compact-direction-set consequence of the local wedge
   hypothesis.  It supplies a radius `r > 0` for all `x ∈ K`, all directions
   `η ∈ Kη`, and all `0 < ε < r`.
2. `localEOW_choose_cone_basis` chooses a real basis
   `ys : Fin m -> Fin m -> ℝ` with every `ys j ∈ C`.  Convexity and the cone
   property imply that every nonzero positive linear combination of the `ys j`
   lies in `C`.  This is the chart used by both local continuous EOW and the
   Streater-Wightman regularization construction.
3. `localEOWRealChart_closedBall_subset` localizes the real edge.  For each
   `x0 ∈ E` and basis `ys`, pull `E` back by
   `u ↦ x0 + Σ j, u j • ys j`; because `E` is open, choose
   `ρ > 0` such that the closed ball `closedBall 0 ρ` maps into `E`.
   No global convexity of `E` is needed; all integration is done in this
   local closed-ball window.
4. `localEOW_chart_positive_polywedge_mem` proves that the chart
   `Phi x0 ys w = realEmbed x0 + Σ j, w j • complexify (ys j)` maps a small
   positive polywedge over `B` into `Ωplus` and the reflected negative
   polywedge into `Ωminus`.  The proof normalizes the imaginary direction
   `Σ j, v j • ys j` with `0 < v j`, places it in the compact simplex image
   inside `C`, and applies `hlocal_wedge`.

   The Lean proof must make this normalization explicit.  For a fixed cone
   basis `ys : Fin m -> Fin m -> ℝ`, the checked chart-direction simplex is:

   ```lean
   def localEOWCoefficientSimplex (m : ℕ) : Set (Fin m -> ℝ) :=
     {a | (∀ j, a j ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ j, a j = 1}

   def localEOWSimplexDirections (ys : Fin m -> Fin m -> ℝ) :
       Set (Fin m -> ℝ) :=
     (fun a : Fin m -> ℝ => ∑ j, a j • ys j) ''
       localEOWCoefficientSimplex m
   ```

   The checked support lemmas are:

   ```lean
   theorem isCompact_localEOWCoefficientSimplex (m : ℕ) :
       IsCompact (localEOWCoefficientSimplex m)

   theorem isCompact_localEOWSimplexDirections
       (ys : Fin m -> Fin m -> ℝ) :
       IsCompact (localEOWSimplexDirections ys)

   theorem localEOWSimplexDirections_subset_cone
       (C : Set (Fin m -> ℝ))
       (hC_conv : Convex ℝ C)
       (ys : Fin m -> Fin m -> ℝ)
       (hys : ∀ j, ys j ∈ C) :
       localEOWSimplexDirections ys ⊆ C

   theorem localEOW_positive_imag_normalized_mem_simplex
       {ys : Fin m -> Fin m -> ℝ}
       {v : Fin m -> ℝ}
       (hv_nonneg : ∀ j, 0 ≤ v j)
       (hv_sum_pos : 0 < ∑ j, v j) :
       ((∑ j, v j)⁻¹) • (∑ j, v j • ys j) ∈
         localEOWSimplexDirections ys
   ```

   The local replacements for `Phi_pos_in_tube` and `Phi_neg_in_tube` are now
   checked.  The positive theorem has this exact shape:

   ```lean
   theorem localEOW_chart_positive_polywedge_mem
       (Ωplus : Set (ComplexChartSpace m))
       (E C : Set (Fin m -> ℝ))
       (hlocal_wedge :
         ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ E ->
           ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
             ∃ r : ℝ, 0 < r ∧
               ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
                 (fun a => (x a : ℂ) +
                   (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus)
       (hC_conv : Convex ℝ C)
       (ys : Fin m -> Fin m -> ℝ)
       (hys_C : ∀ j, ys j ∈ C)
       (B : Set (Fin m -> ℝ))
       (hB_compact : IsCompact B)
       (hB_E : B ⊆ E) :
       ∃ r : ℝ, 0 < r ∧
         ∀ u ∈ B, ∀ v : Fin m -> ℝ,
           (∀ j, 0 ≤ v j) -> 0 < ∑ j, v j -> (∑ j, v j) < r ->
             (fun a =>
               (u a : ℂ) +
                 (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωplus
   ```

   The proof applies `hlocal_wedge` to
   `K = B` and `Kη = localEOWSimplexDirections ys`.  For `v` with all entries
   positive, set `ε = ∑ j, v j` and
   `η = ε⁻¹ • ∑ j, v j • ys j`.  Then `η ∈ Kη`, `0 < ε`, and
   `ε • η = ∑ j, v j • ys j`, so the chart point is exactly
   `realEmbed u + I * εη`.  The checked negative theorem uses `v j ≤ 0`,
   `0 < ∑ j, -v j`, `ε = ∑ j, -v j`, and the `Ωminus` membership supplied by
   the minus half of `hlocal_wedge`.

   The common-radius two-sided version is also checked as
   `localEOW_chart_twoSided_polywedge_mem`.  This finite-dimensional geometry is
   now checked; it is not a wrapper around the global tube theorem.  The next
   continuous-EOW step can use these membership lemmas while extracting/adapting
   the `local_eow_extension` proof pattern.

   The public affine-chart layer is checked under the following exact names:

   ```lean
   def localEOWRealChart
       (x0 : Fin m -> ℝ)
       (ys : Fin m -> Fin m -> ℝ) :
       (Fin m -> ℝ) -> (Fin m -> ℝ)

   def localEOWChart
       (x0 : Fin m -> ℝ)
       (ys : Fin m -> Fin m -> ℝ) :
       (Fin m -> ℂ) -> (Fin m -> ℂ)

   theorem continuous_localEOWRealChart
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ) :
       Continuous (localEOWRealChart x0 ys)

   theorem localEOWChart_zero
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ) :
       localEOWChart x0 ys 0 = realEmbed x0

   theorem differentiable_localEOWChart
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ) :
       Differentiable ℂ (localEOWChart x0 ys)

   theorem continuous_localEOWChart
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ) :
       Continuous (localEOWChart x0 ys)

   theorem localEOWChart_im
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (w : Fin m -> ℂ) (i : Fin m) :
       (localEOWChart x0 ys w i).im = ∑ j, (w j).im * ys j i

   theorem localEOWChart_real
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (t : Fin m -> ℝ) :
       localEOWChart x0 ys (fun j => (t j : ℂ)) =
         realEmbed (localEOWRealChart x0 ys t)

   theorem localEOWChart_conj
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (w : Fin m -> ℂ) :
       localEOWChart x0 ys (fun j => starRingEnd ℂ (w j)) =
         fun i => starRingEnd ℂ (localEOWChart x0 ys w i)

   theorem localEOWChart_affine_real_combo
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (w1 w2 : Fin m -> ℂ) (a b : ℝ) (hab : a + b = 1) :
       localEOWChart x0 ys (a • w1 + b • w2) =
         a • localEOWChart x0 ys w1 + b • localEOWChart x0 ys w2

   theorem localEOWChart_inverse_conj
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (Φinv : (Fin m -> ℂ) -> (Fin m -> ℂ))
       (hleft : ∀ w, Φinv (localEOWChart x0 ys w) = w)
       (hright : ∀ z, localEOWChart x0 ys (Φinv z) = z)
       (z : Fin m -> ℂ) :
       Φinv (fun i => starRingEnd ℂ (z i)) =
         fun j => starRingEnd ℂ (Φinv z j)

   theorem localEOWChart_equiv
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hli : LinearIndependent ℝ ys) :
       ∃ (Φinv : (Fin m -> ℂ) -> (Fin m -> ℂ)),
         Differentiable ℂ Φinv ∧
         (∀ w, Φinv (localEOWChart x0 ys w) = w) ∧
         (∀ z, localEOWChart x0 ys (Φinv z) = z)

   theorem localEOWChart_inverse_ball_geometry
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hρ : 0 < ρ)
       (Φinv : (Fin m -> ℂ) -> (Fin m -> ℂ))
       (hΦinv_diff : Differentiable ℂ Φinv)
       (hleft : ∀ w, Φinv (localEOWChart x0 ys w) = w)
       (hright : ∀ z, localEOWChart x0 ys (Φinv z) = z) :
       IsOpen (Φinv ⁻¹' Metric.ball (0 : Fin m -> ℂ) ρ) ∧
       Convex ℝ (Φinv ⁻¹' Metric.ball (0 : Fin m -> ℂ) ρ) ∧
       (∀ z ∈ Φinv ⁻¹' Metric.ball (0 : Fin m -> ℂ) ρ,
         (fun i => starRingEnd ℂ (z i)) ∈
           Φinv ⁻¹' Metric.ball (0 : Fin m -> ℂ) ρ) ∧
       realEmbed x0 ∈ Φinv ⁻¹' Metric.ball (0 : Fin m -> ℂ) ρ

   theorem localEOWChart_real_imag
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (u v : Fin m -> ℝ) :
       localEOWChart x0 ys
         (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) =
         fun a => (localEOWRealChart x0 ys u a : ℂ) +
           (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I

   theorem localEOWChart_twoSided_polywedge_mem
       ... :
       ∃ r : ℝ, 0 < r ∧
         (∀ u ∈ B, ∀ v : Fin m -> ℝ,
           (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j -> (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus) ∧
         (∀ u ∈ B, ∀ v : Fin m -> ℝ,
           (∀ j, v j ≤ 0) ->
           0 < ∑ j, -v j -> (∑ j, -v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
   ```

   The next local-neighborhood geometry must not require linear independence:
   continuity of `localEOWRealChart x0 ys` alone gives the real closed-ball
   domain needed for local compactness.  Linear independence is used only
   later, through `localEOWChart_equiv`, to push the orthant-coordinate
   extension back to the original local complex coordinates and to prove the
   resulting patch is convex and conjugation symmetric.  The checked
   `localEOWChart_inverse_ball_geometry` theorem packages exactly that patch
   geometry for the inverse-chart ball used by the local extension proof:
   openness from differentiability of the inverse, convexity from
   `localEOWChart_affine_real_combo`, conjugation stability from
   `localEOWChart_inverse_conj`, and real-point membership from
   `localEOWChart_zero`.  The production real-neighborhood theorem is now
   checked as:

   ```lean
   theorem localEOWRealChart_closedBall_subset
       {E : Set (Fin m -> ℝ)}
       (hE_open : IsOpen E)
       (x0 : Fin m -> ℝ) (hx0 : x0 ∈ E)
       (ys : Fin m -> Fin m -> ℝ) :
       ∃ ρ : ℝ, 0 < ρ ∧
         ∀ u : Fin m -> ℝ,
           u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ ->
             localEOWRealChart x0 ys u ∈ E
   ```

   Lean proof transcript: take the open preimage
   `(localEOWRealChart x0 ys) ⁻¹' E`, use
   `continuous_localEOWRealChart x0 ys`, prove `0` lies in this preimage by
   `simp [localEOWRealChart]`, choose an open ball `Metric.ball 0 ε` from
   `Metric.isOpen_iff`, and return `ρ = ε / 2`; closed-ball membership gives
   `dist u 0 ≤ ε/2 < ε`.

   The real-translation margin used by mollifier supports should also be a
   checked closed-ball theorem, not an opaque `BoxMargin` package:

   ```lean
   theorem localEOW_closedBall_support_margin
       {ρ : ℝ} (hρ : 0 < ρ) :
       ∃ r : ℝ, 0 < r ∧
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) (ρ / 2),
         ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r,
           u + t ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ
   ```

   Lean proof transcript: choose `r = ρ / 2`; after rewriting
   `Metric.mem_closedBall` and `dist_zero_right`, the goal is
   `‖u + t‖ ≤ ρ`, which follows from
   `norm_add_le u t`, `‖u‖ ≤ ρ/2`, and `‖t‖ ≤ ρ/2`.

   The local Rudin/Möbius map used inside the continuous EOW proof is now
   exposed as checked finite-dimensional geometry:

   ```lean
   def localEOWSmp
       (δ : ℝ) (w : Fin m -> ℂ) (l : ℂ) : Fin m -> ℂ :=
     fun j => (δ : ℂ) * moebiusProd (fun k => w k / (δ : ℂ)) l j

   theorem localEOWSmp_zero
       (hδ : δ ≠ 0) (w : Fin m -> ℂ) :
       localEOWSmp δ w 0 = w

   theorem localEOWSmp_im_pos_of_real
       (hδ : 0 < δ)
       (hw_real : ∀ j, (w j).im = 0)
       (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1)
       (hl_pos : 0 < l.im) :
       ∀ j, 0 < (localEOWSmp δ w l j).im

   theorem localEOWSmp_im_neg_of_real
       (hδ : 0 < δ)
       (hw_real : ∀ j, (w j).im = 0)
       (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1)
       (hl_neg : l.im < 0) :
       ∀ j, (localEOWSmp δ w l j).im < 0

   theorem localEOWSmp_norm_le_extended
       (hδ : 0 < δ)
       (hw_half : ∀ j, ‖w j / (δ : ℂ)‖ ≤ 1 / 2)
       (hl : ‖l‖ ≤ 2) :
       ∀ j, ‖localEOWSmp δ w l j‖ ≤ δ * 10

   theorem localEOWSmp_norm_le_extended_of_closedBall
       (hδ : 0 < δ)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hl : ‖l‖ ≤ 2) :
       ∀ j, ‖localEOWSmp δ w l j‖ ≤ δ * 10

   theorem localEOWSmp_div_norm_lt_one_of_closedBall
       (hδ : 0 < δ)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2)) :
       ∀ j, ‖w j / (δ : ℂ)‖ < 1

   theorem localEOWSmp_im_zero_of_unit_real
       (hl_norm : Complex.normSq l = 1) (hl_im : l.im = 0) :
       ∀ j, (localEOWSmp δ w l j).im = 0

   theorem localEOWSmp_im_zero_of_real
       (hw_real : ∀ j, (w j).im = 0) (hl_im : l.im = 0) :
       ∀ j, (localEOWSmp δ w l j).im = 0

   theorem localEOWChart_smp_realEdge_eq_of_unit_real
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hl_norm : Complex.normSq l = 1) (hl_im : l.im = 0) :
       localEOWChart x0 ys (localEOWSmp δ w l) =
         realEmbed
           (localEOWRealChart x0 ys
             (fun j => (localEOWSmp δ w l j).re))

   theorem localEOWChart_smp_realEdge_eq_of_real
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_real : ∀ j, (w j).im = 0) (hl_im : l.im = 0) :
       localEOWChart x0 ys (localEOWSmp δ w l) =
         realEmbed
           (localEOWRealChart x0 ys
             (fun j => (localEOWSmp δ w l j).re))

   theorem continuous_localEOWSmp_theta
       (hδ : 0 < δ)
       (hw : w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2)) :
       Continuous (fun θ : ℝ =>
         localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I)))

   theorem continuousAt_localEOWSmp_of_norm_lt_two
       (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1)
       (hl : ‖l‖ < 2) :
       ContinuousAt (fun l' : ℂ => localEOWSmp δ w l') l

   theorem continuousAt_localEOWChart_smp_of_norm_lt_two
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1)
       (hl : ‖l‖ < 2) :
       ContinuousAt
         (fun l' : ℂ => localEOWChart x0 ys (localEOWSmp δ w l')) l

   theorem differentiableAt_localEOWSmp_of_real
       (hw_real : ∀ j, (w j).im = 0)
       (hl_ne : l.im ≠ 0) :
       DifferentiableAt ℂ (fun l' : ℂ => localEOWSmp δ w l') l

   theorem differentiableAt_localEOWChart_smp_of_real
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_real : ∀ j, (w j).im = 0)
       (hl_ne : l.im ≠ 0) :
       DifferentiableAt ℂ
         (fun l' : ℂ => localEOWChart x0 ys (localEOWSmp δ w l')) l

   theorem differentiableOn_localEOWChart_smp_upperHalfPlane_of_real
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_real : ∀ j, (w j).im = 0) :
       DifferentiableOn ℂ
         (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
         EOW.UpperHalfPlane

   theorem differentiableOn_localEOWChart_smp_lowerHalfPlane_of_real
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_real : ∀ j, (w j).im = 0) :
       DifferentiableOn ℂ
         (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
         EOW.LowerHalfPlane

   theorem tendsto_localEOWChart_smp_upperHalfPlane_to_realEdge
       (hm : 0 < m)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j ->
           (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hw_real : ∀ j, (w j).im = 0)
       (hx : |x| < 2) :
       Filter.Tendsto
         (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
         (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
         (nhdsWithin
           (realEmbed (localEOWRealChart x0 ys
             (fun j => (localEOWSmp δ w (x : ℂ) j).re))) Ωplus)

   theorem tendsto_localEOWChart_smp_lowerHalfPlane_to_realEdge
       (hm : 0 < m)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hminus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, v j ≤ 0) ->
           0 < ∑ j, -v j ->
           (∑ j, -v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hw_real : ∀ j, (w j).im = 0)
       (hx : |x| < 2) :
       Filter.Tendsto
         (fun l : ℂ => localEOWChart x0 ys (localEOWSmp δ w l))
         (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
         (nhdsWithin
           (realEmbed (localEOWRealChart x0 ys
             (fun j => (localEOWSmp δ w (x : ℂ) j).re))) Ωminus)

   theorem continuousAt_localEOWRealChart_smp_re_of_norm_lt_two
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1)
       (ht : |t| < 2) :
       ContinuousAt
         (fun s : ℝ =>
           localEOWRealChart x0 ys
             (fun j => (localEOWSmp δ w (s : ℂ) j).re)) t

   theorem continuousAt_localEOWBoundaryValue_smp
       (hE_open : IsOpen E)
       (bv : (Fin m -> ℝ) -> ℂ) (hbv_cont : ContinuousOn bv E)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_norm : ∀ j, ‖w j / (δ : ℂ)‖ < 1)
       (ht : |t| < 2)
       (hmem : ∀ s : ℝ, |s| < 2 ->
         localEOWRealChart x0 ys
           (fun j => (localEOWSmp δ w (s : ℂ) j).re) ∈ E) :
       ContinuousAt
         (fun s : ℝ =>
           bv (localEOWRealChart x0 ys
             (fun j => (localEOWSmp δ w (s : ℂ) j).re))) t

   theorem differentiableOn_localEOWUpperBranch_smp_of_real
       (Ωplus : Set (Fin m -> ℂ)) (hΩplus_open : IsOpen Ωplus)
       (Fplus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_real : ∀ j, (w j).im = 0)
       (hmem : ∀ l ∈ Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane,
         localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus) :
       DifferentiableOn ℂ
         (fun l : ℂ => Fplus (localEOWChart x0 ys (localEOWSmp δ w l)))
         (Metric.ball (0 : ℂ) 2 ∩ EOW.UpperHalfPlane)

   theorem differentiableOn_localEOWLowerBranch_smp_of_real
       (Ωminus : Set (Fin m -> ℂ)) (hΩminus_open : IsOpen Ωminus)
       (Fminus : (Fin m -> ℂ) -> ℂ)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hw_real : ∀ j, (w j).im = 0)
       (hmem : ∀ l ∈ Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane,
         localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus) :
       DifferentiableOn ℂ
         (fun l : ℂ => Fminus (localEOWChart x0 ys (localEOWSmp δ w l)))
         (Metric.ball (0 : ℂ) 2 ∩ EOW.LowerHalfPlane)

   theorem tendsto_localEOWUpperBranch_smp_to_boundaryValue
       (hm : 0 < m)
       (Ωplus : Set (Fin m -> ℂ))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (Fplus : (Fin m -> ℂ) -> ℂ) (bv : (Fin m -> ℝ) -> ℂ)
       (hFplus_bv : ∀ y ∈ E,
         Filter.Tendsto Fplus
           (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j ->
           (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hw_real : ∀ j, (w j).im = 0)
       (hx : |x| < 2)
       (hE_mem : localEOWRealChart x0 ys
         (fun j => (localEOWSmp δ w (x : ℂ) j).re) ∈ E) :
       Filter.Tendsto
         (fun l : ℂ => Fplus (localEOWChart x0 ys (localEOWSmp δ w l)))
         (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
         (nhds (bv (localEOWRealChart x0 ys
           (fun j => (localEOWSmp δ w (x : ℂ) j).re))))

   theorem tendsto_localEOWLowerBranch_smp_to_boundaryValue
       (hm : 0 < m)
       (Ωminus : Set (Fin m -> ℂ))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (Fminus : (Fin m -> ℂ) -> ℂ) (bv : (Fin m -> ℝ) -> ℂ)
       (hFminus_bv : ∀ y ∈ E,
         Filter.Tendsto Fminus
           (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hminus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, v j ≤ 0) ->
           0 < ∑ j, -v j ->
           (∑ j, -v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hw_real : ∀ j, (w j).im = 0)
       (hx : |x| < 2)
       (hE_mem : localEOWRealChart x0 ys
         (fun j => (localEOWSmp δ w (x : ℂ) j).re) ∈ E) :
       Filter.Tendsto
         (fun l : ℂ => Fminus (localEOWChart x0 ys (localEOWSmp δ w l)))
       (nhdsWithin (x : ℂ) EOW.LowerHalfPlane)
       (nhds (bv (localEOWRealChart x0 ys
         (fun j => (localEOWSmp δ w (x : ℂ) j).re))))

   theorem local_rudin_mean_value_real
       (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (hE_open : IsOpen E)
       (bv : (Fin m -> ℝ) -> ℂ) (hbv_cont : ContinuousOn bv E)
       (hFplus_bv : ∀ y ∈ E,
         Filter.Tendsto Fplus
           (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
       (hFminus_bv : ∀ y ∈ E,
         Filter.Tendsto Fminus
           (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j ->
           (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
       (hminus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, v j ≤ 0) ->
           0 < ∑ j, -v j ->
           (∑ j, -v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hw_real : ∀ j, (w j).im = 0)
       (hE_mem : ∀ s : ℝ, |s| < 2 ->
         localEOWRealChart x0 ys
           (fun j => (localEOWSmp δ w (s : ℂ) j).re) ∈ E) :
       let G : ℝ -> ℂ := fun θ =>
         if 0 < Real.sin θ then
           Fplus (localEOWChart x0 ys
             (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))
         else if Real.sin θ < 0 then
           Fminus (localEOWChart x0 ys
             (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))
         else 0
       (2 * ↑Real.pi)⁻¹ • ∫ θ in (-Real.pi)..Real.pi, G θ =
         bv (localEOWRealChart x0 ys (fun j => (w j).re))

   theorem localEOWSmp_re_mem_closedBall
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hl : ‖l‖ ≤ 2) :
       (fun j => (localEOWSmp δ w l j).re) ∈
         Metric.closedBall (0 : Fin m -> ℝ) ρ

   theorem localEOWChart_smp_upper_mem_of_delta
       (hm : 0 < m)
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j ->
           (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hw_real : ∀ j, (w j).im = 0)
       (hl_pos : 0 < l.im) (hl_norm : ‖l‖ ≤ 2) :
       localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus

   theorem localEOWChart_smp_lower_mem_of_delta
       (hm : 0 < m)
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hminus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, v j ≤ 0) ->
           0 < ∑ j, -v j ->
           (∑ j, -v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus)
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hw_real : ∀ j, (w j).im = 0)
       (hl_neg : l.im < 0) (hl_norm : ‖l‖ ≤ 2) :
       localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus

   theorem exists_localEOWSmp_delta
       (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
       ∃ δ : ℝ, 0 < δ ∧ δ * 10 ≤ ρ ∧
         (Fintype.card (Fin m) : ℝ) * (δ * 10) < r

   theorem exists_localEOWChart_smp_delta
       (hm : 0 < m)
       (hρ : 0 < ρ) (hr : 0 < r)
       (hplus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j ->
           (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
       (hminus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, v j ≤ 0) ->
           0 < ∑ j, -v j ->
           (∑ j, -v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) :
       ∃ δ : ℝ, 0 < δ ∧
         (∀ {w : Fin m -> ℂ} {l : ℂ},
           w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2) ->
           (∀ j, (w j).im = 0) ->
           0 < l.im ->
           ‖l‖ ≤ 2 ->
             localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus) ∧
         (∀ {w : Fin m -> ℂ} {l : ℂ},
           w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2) ->
           (∀ j, (w j).im = 0) ->
           l.im < 0 ->
           ‖l‖ ≤ 2 ->
             localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus)
   ```

   These lemmas are the local version of the sign and size estimates used in
   `rudin_orthant_extension`: real starting points preserve the sign of
   `Im l`, and the real part of the scaled Möbius product stays inside the
   selected real edge ball when `δ * 10 ≤ ρ`.  The closed-ball helpers package
   the denominator estimate `‖w j / δ‖ < 1` directly from
   `w ∈ closedBall 0 (δ / 2)`.  The zero, real-boundary, and continuity lemmas
   expose the remaining Rudin transcript used by the Cauchy integral and
   real-line mean-value proofs.  The unit-real lemmas are for the compact
   circle boundary.  The arbitrary-real lemmas are for the interval
   `-2 < l.re < 2` in the one-variable EOW identity, where real starting
   points must stay on the real edge without assuming `Complex.normSq l = 1`.
   `continuousAt_localEOWSmp_of_norm_lt_two` is the local version of the
   private `hsmp_ca_real` block in `rudin_mean_value_real`; its denominator
   estimate uses `rudinC_lt_half` to prove
   `‖rudinC * l * (w j / δ)‖ < 1` whenever `‖l‖ < 2` and
   `‖w j / δ‖ < 1`.  The chart continuity theorem is just composition with
   `continuous_localEOWChart`, but it is a checked theorem because this is the
   exact map used in the boundary-value trace.

   The half-plane differentiability lemmas expose the local analogue of the
   private `hgp_diff`/`hgm_diff` setup in `rudin_mean_value_real`.  Their proof
   is not an assumption: for real starting coordinates, division by the real
   scale `δ` remains real, and `moebiusRudin_differentiableAt_of_real` gives
   differentiability whenever `l.im ≠ 0`; composing with
   `differentiable_localEOWChart` gives the chart version.  Restricting to
   `EOW.UpperHalfPlane` and `EOW.LowerHalfPlane` is then just
   `DifferentiableAt.differentiableWithinAt`.

   The boundary-filter lemmas package the corresponding local
   `hgp_bv`/`hgm_bv` input.  For `|x| < 2`, the `‖l‖ < 2` condition is
   eventually true in `nhdsWithin (x : ℂ)` by openness of the norm ball.
   Combining this eventual norm bound with the upper/lower chart-membership
   theorems gives eventual membership in `Ωplus` or `Ωminus`; combining that
   with `continuousAt_localEOWChart_smp_of_norm_lt_two` and the real-edge
   identity gives the target `nhdsWithin` convergence.  This is the exact
   filter shape needed to compose with the local continuous boundary-value
   hypotheses.

   The real-line continuity lemmas package the remaining `hbv_real` input for
   the local one-variable EOW theorem.  First, continuity of
   `l ↦ localEOWSmp δ w l` on `‖l‖ < 2`, composed with the real embedding
   `s ↦ (s : ℂ)`, coordinatewise real part, and
   `continuous_localEOWRealChart`, gives continuity of the real chart path.
   Second, if this path stays in the real-edge set `E` for `|s| < 2`, then
   `ContinuousOn bv E` composes with the chart path to give continuity of the
   scalar boundary function.  This is not an additional boundary-value
   assumption; it is the continuity of the already supplied real boundary
   function along the Rudin real slice.

   The branch-level lemmas package the remaining local hypotheses for
   `local_edge_of_the_wedge_1d`.  The differentiability lemmas compose
   `DifferentiableOn ℂ Fplus Ωplus` / `DifferentiableOn ℂ Fminus Ωminus`
   with the checked differentiability of the local Rudin chart, using
   openness of the plus/minus wedge and the local chart-membership hypothesis
   on the disk half.  The boundary-value lemmas compose the local
   `nhdsWithin realEdge Ωplus/Ωminus` convergence with the supplied
   boundary-value hypotheses for `Fplus` and `Fminus`.  These four facts are
   exactly the local `hgp_diff`, `hgm_diff`, `hgp_bv`, and `hgm_bv` blocks
   needed before the mean-value/circle-average identity.

   The checked `local_rudin_mean_value_real` theorem completes the local
   analogue of the private `rudin_mean_value_real` block in
   `TubeDomainExtension.lean`.  The proof transcript is now Lean-ready:

   - define the one-variable branches
     `gp l = if 0 < l.im then Fplus (localEOWChart x0 ys (localEOWSmp δ w l))
       else bv_smp l.re` and
     `gm l = if l.im < 0 then Fminus (localEOWChart x0 ys (localEOWSmp δ w l))
       else bv_smp l.re`;
   - prove disk-half membership in `Ωplus` and `Ωminus` from
     `localEOWChart_smp_upper_mem_of_delta` and
     `localEOWChart_smp_lower_mem_of_delta`;
   - obtain `DifferentiableOn ℂ gp` and `DifferentiableOn ℂ gm` on the
     upper/lower half-disks by `DifferentiableOn.congr` from the checked
     branch differentiability lemmas;
   - obtain the upper/lower boundary filters for `gp` and `gm` by composing
     `tendsto_localEOWUpperBranch_smp_to_boundaryValue` and
     `tendsto_localEOWLowerBranch_smp_to_boundaryValue` with the eventual
     equalities `gp = Fplus ∘ chart` and `gm = Fminus ∘ chart`;
   - obtain the real-line boundary filter for `gp` from
     `continuousAt_localEOWBoundaryValue_smp` and the equality
     `gp l = bv_smp l.re` on `{l | l.im = 0}`;
   - apply `local_edge_of_the_wedge_1d (-2) 2` to get a holomorphic
     `F_disc` on the disk `Metric.ball 0 2`;
   - use `DiffContOnCl.circleAverage` on `closedBall 0 1`, and prove
     `F_disc 0 = bv (localEOWRealChart x0 ys (fun j => (w j).re))` from
     `localEOWSmp_zero` and uniqueness of limits from the upper half-plane;
   - identify the circle integral with the stated piecewise integrand by
     `circleMap_zero`, excluding only `{0, Real.pi}`, a measure-zero set, and
     then shift the interval by the period `2 * Real.pi`.

   Thus the mean-value identity is a proved consequence of local wedge
   holomorphy, common continuous boundary values, and the checked Rudin
   Möbius geometry.  It introduces no new analytic assumption and no new
   source theorem.

   The next local-envelope implementation should not grow
   `SCV/LocalContinuousEOW.lean` further.  That file is now the checked local
   Rudin substrate; the envelope proof belongs in a small companion module
   `SCV/LocalContinuousEOWEnvelope.lean` importing it.  The first two public
   helper surfaces in that module are:

   ```lean
   theorem continuousAt_localEOWSmp_param
       {m : ℕ} (δ : ℝ) (l : ℂ) (hl : ‖l‖ ≤ 1)
       (w0 : Fin m -> ℂ)
       (hw0 : ∀ j, ‖w0 j / (δ : ℂ)‖ < 1) :
       ContinuousAt (fun w : Fin m -> ℂ => localEOWSmp δ w l) w0

   theorem differentiableAt_localRudin_parametric_integral
       {m : ℕ} (G : (Fin m -> ℂ) -> ℝ -> ℂ)
       {z : Fin m -> ℂ} {j : Fin m} {δ : ℝ}
       (hz : z ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (hε' : 0 < ε')
       (h_upd : ∀ ζ, dist ζ (z j) ≤ 2 * ε' ->
         Function.update z j ζ ∈
           Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (h_upd_t : ∀ t ∈ Metric.ball (z j) ε',
         ∀ ζ ∈ Metric.closedBall t ε',
           Function.update z j ζ ∈
             Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (h_G_meas : ∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2),
         AEStronglyMeasurable (G w)
           (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)))
       (M : ℝ)
       (hM : ∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2),
         ∀ θ, ‖G w θ‖ ≤ M)
       (h_G_diffAt : ∀ θ, Real.sin θ ≠ 0 -> ∀ t,
         Function.update z j t ∈
           Metric.ball (0 : Fin m -> ℂ) (δ / 2) ->
         DifferentiableAt ℂ
           (fun ζ => G (Function.update z j ζ) θ) t)
       (hG_zero : ∀ w θ, Real.sin θ = 0 -> G w θ = 0) :
       DifferentiableAt ℂ
         (fun ζ => ∫ θ in (-Real.pi)..Real.pi,
           G (Function.update z j ζ) θ) (z j)

   theorem exists_localRudin_coordinate_update_margin
       {m : ℕ} {δ : ℝ} {z : Fin m -> ℂ}
       (hz : z ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (j : Fin m) :
       ∃ ε' : ℝ, 0 < ε' ∧
         (∀ ζ, dist ζ (z j) ≤ 2 * ε' ->
           Function.update z j ζ ∈
             Metric.ball (0 : Fin m -> ℂ) (δ / 2)) ∧
         (∀ t ∈ Metric.ball (z j) ε',
           ∀ ζ ∈ Metric.closedBall t ε',
             Function.update z j ζ ∈
               Metric.ball (0 : Fin m -> ℂ) (δ / 2))

   theorem exists_localContinuousEOW_chart_window
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (E C : Set (Fin m -> ℝ))
       (hE_open : IsOpen E) (hC_open : IsOpen C)
       (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
       (hlocal_wedge :
         ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ E ->
           ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
             ∃ r : ℝ, 0 < r ∧
               ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
                 (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) *
                   Complex.I) ∈ Ωplus ∧
                 (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) *
                   Complex.I) ∈ Ωminus)
       (x0 : Fin m -> ℝ) (hx0 : x0 ∈ E) :
       ∃ ys : Fin m -> Fin m -> ℝ,
         (∀ j, ys j ∈ C) ∧ LinearIndependent ℝ ys ∧
         ∃ ρ : ℝ, 0 < ρ ∧
         ∃ r : ℝ, 0 < r ∧
         ∃ δ : ℝ, 0 < δ ∧
           δ * 10 ≤ ρ ∧
           (Fintype.card (Fin m) : ℝ) * (δ * 10) < r ∧
           (∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
             localEOWRealChart x0 ys u ∈ E) ∧
           (∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
             ∀ v : Fin m -> ℝ, (∀ j, 0 ≤ v j) ->
             0 < ∑ j, v j -> (∑ j, v j) < r ->
               localEOWChart x0 ys
                 (fun j => (u j : ℂ) + (v j : ℂ) *
                   Complex.I) ∈ Ωplus) ∧
           (∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
             ∀ v : Fin m -> ℝ, (∀ j, v j ≤ 0) ->
             0 < ∑ j, -v j -> (∑ j, -v j) < r ->
               localEOWChart x0 ys
                 (fun j => (u j : ℂ) + (v j : ℂ) *
                   Complex.I) ∈ Ωminus) ∧
           (∀ {w : Fin m -> ℂ} {l : ℂ},
             w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2) ->
             (∀ j, (w j).im = 0) -> 0 < l.im -> ‖l‖ ≤ 2 ->
               localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus) ∧
           (∀ {w : Fin m -> ℂ} {l : ℂ},
             w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2) ->
             (∀ j, (w j).im = 0) -> l.im < 0 -> ‖l‖ ≤ 2 ->
               localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωminus)

   theorem localEOWChart_ball_positive_mem_of_delta
       {m : ℕ} (hm : 0 < m)
       (Ωplus : Set (Fin m -> ℂ))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ, (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j -> (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
       {w : Fin m -> ℂ}
       (hw : w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (hw_pos : ∀ j, 0 < (w j).im) :
       localEOWChart x0 ys w ∈ Ωplus

   theorem localEOWChart_ball_negative_mem_of_delta
       -- same statement, with target `Ωminus`, hypotheses `(w j).im < 0`,
       -- and the negative polywedge membership input.

   theorem localEOWChart_smp_upper_mem_of_delta_on_sphere
       {m : ℕ} (hm : 0 < m)
       (Ωplus : Set (Fin m -> ℂ))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ, (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j -> (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus)
       {w : Fin m -> ℂ} {l : ℂ}
       (hw : w ∈ Metric.closedBall (0 : Fin m -> ℂ) (δ / 2))
       (hl_norm : ‖l‖ = 1) (hl_pos : 0 < l.im) :
       localEOWChart x0 ys (localEOWSmp δ w l) ∈ Ωplus

   theorem localEOWChart_smp_lower_mem_of_delta_on_sphere
       -- same statement, with target `Ωminus` and `l.im < 0`.

   def localRudinIntegrand
       {m : ℕ} (δ : ℝ) (x0 : Fin m -> ℝ)
       (ys : Fin m -> Fin m -> ℝ)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (w : Fin m -> ℂ) (θ : ℝ) : ℂ :=
     if 0 < Real.sin θ then
       Fplus (localEOWChart x0 ys
         (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))
     else if Real.sin θ < 0 then
       Fminus (localEOWChart x0 ys
         (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))
     else 0

   def localRudinIntegral
       {m : ℕ} (δ : ℝ) (x0 : Fin m -> ℝ)
       (ys : Fin m -> Fin m -> ℝ)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (w : Fin m -> ℂ) : ℂ :=
     ∫ θ in (-Real.pi)..Real.pi,
       localRudinIntegrand δ x0 ys Fplus Fminus w θ

   def localRudinEnvelope
       {m : ℕ} (δ : ℝ) (x0 : Fin m -> ℝ)
       (ys : Fin m -> Fin m -> ℝ)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (w : Fin m -> ℂ) : ℂ :=
     ((2 * Real.pi)⁻¹ : ℝ) •
       localRudinIntegral δ x0 ys Fplus Fminus w

   theorem aestronglyMeasurable_localRudinIntegrand
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus : ...positive chart polywedge membership...)
       (hminus : ...negative chart polywedge membership...)
       {w : Fin m -> ℂ}
       (hw : w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2)) :
       AEStronglyMeasurable
         (localRudinIntegrand δ x0 ys Fplus Fminus w)
         (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi))

   theorem continuousAt_localRudinIntegrand_param
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus : ...positive chart polywedge membership...)
       (hminus : ...negative chart polywedge membership...)
       {w0 : Fin m -> ℂ}
       (hw0 : w0 ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (θ : ℝ) :
       ContinuousAt
         (fun w => localRudinIntegrand δ x0 ys Fplus Fminus w θ) w0

   theorem continuousAt_localRudinIntegral_of_bound
       -- same local hypotheses, plus a bound
       (M : ℝ)
       (hM : ∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2),
         ∀ θ, ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ ≤ M)
       {w0 : Fin m -> ℂ}
       (hw0 : w0 ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2)) :
       ContinuousAt
         (localRudinIntegral δ x0 ys Fplus Fminus) w0

   theorem localRudinIntegrand_zero_of_sin_eq_zero
       (hsin : Real.sin θ = 0) :
       localRudinIntegrand δ x0 ys Fplus Fminus w θ = 0

   theorem differentiableAt_localRudinIntegrand_update
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus : ...positive chart polywedge membership...)
       (hminus : ...negative chart polywedge membership...)
       {z : Fin m -> ℂ} {j : Fin m} {t : ℂ} {θ : ℝ}
       (hsin : Real.sin θ ≠ 0)
       (ht : Function.update z j t ∈
         Metric.ball (0 : Fin m -> ℂ) (δ / 2)) :
       DifferentiableAt ℂ
         (fun ζ =>
           localRudinIntegrand δ x0 ys Fplus Fminus
             (Function.update z j ζ) θ) t

   theorem differentiableAt_localRudinIntegral_of_bound
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus : ...positive chart polywedge membership...)
       (hminus : ...negative chart polywedge membership...)
       {z : Fin m -> ℂ} (hz : z ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (j : Fin m)
       (M : ℝ)
       (hM : ∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2),
         ∀ θ, ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ ≤ M) :
       DifferentiableAt ℂ
         (fun ζ => ∫ θ in (-Real.pi)..Real.pi,
           localRudinIntegrand δ x0 ys Fplus Fminus
             (Function.update z j ζ) θ) (z j)

   theorem differentiableOn_localRudinIntegral_of_bound
       -- same local hypotheses, plus `M` and `hM`
       DifferentiableOn ℂ
         (localRudinIntegral δ x0 ys Fplus Fminus)
         (Metric.ball (0 : Fin m -> ℂ) (δ / 2))

   theorem differentiableOn_localRudinEnvelope_of_bound
       -- same local hypotheses, plus `M` and `hM`
       DifferentiableOn ℂ
         (localRudinEnvelope δ x0 ys Fplus Fminus)
         (Metric.ball (0 : Fin m -> ℂ) (δ / 2))

   theorem differentiableOn_localRudinEnvelope
       -- same local hypotheses as `exists_bound_localRudinIntegrand`
       DifferentiableOn ℂ
         (localRudinEnvelope δ x0 ys Fplus Fminus)
         (Metric.ball (0 : Fin m -> ℂ) (δ / 2))

   theorem exists_bound_localRudinIntegrand
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (E : Set (Fin m -> ℝ))
       (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (bv : (Fin m -> ℝ) -> ℂ)
       (hbv_cont : ContinuousOn bv E)
       (hFplus_bv :
         ∀ y ∈ E, Filter.Tendsto Fplus
           (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
       (hFminus_bv :
         ∀ y ∈ E, Filter.Tendsto Fminus
           (nhdsWithin (realEmbed y) Ωminus) (nhds (bv y)))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hE_mem :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
           localEOWRealChart x0 ys u ∈ E)
       (hplus : ...positive chart polywedge membership...)
       (hminus : ...negative chart polywedge membership...) :
       ∃ M : ℝ, ∀ w ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2),
         ∀ θ, ‖localRudinIntegrand δ x0 ys Fplus Fminus w θ‖ ≤ M
   ```

   Proof transcript for `continuousAt_localEOWSmp_param`: first prove
   continuity of `w ↦ fun k => w k / δ` at `w0`; use
   `pi_norm_lt_iff` and `hw0` to put `w0 / δ` in the unit polydisc; apply
   `moebiusProd_differentiable_w l hl` to get continuity of
   `moebiusProd · l`; compose and multiply each coordinate by the constant
   `(δ : ℂ)`.  This is exactly the public local form of the private checked
   `scaledMoebiusProd_continuousAt`.

   Proof transcript for `differentiableAt_localRudin_parametric_integral`:
   use the local update-margin hypotheses to keep every Cauchy circle in the
   ball `Metric.ball 0 (δ / 2)`; use
   `norm_deriv_le_of_forall_mem_sphere_norm_le` and the uniform bound `hM` to
   get `‖deriv (fun ζ => G (update z j ζ) θ) t‖ ≤ M / ε'` for `sin θ ≠ 0`;
   define `F' t θ` to be that derivative off `sin θ = 0` and `0` on the
   two boundary angles; prove `HasDerivAt` pointwise by `h_G_diffAt` and the
   `hG_zero` constant-function case; prove measurability of `F'(z j, ·)` as
   the a.e. limit of difference quotients along
   `z j + ε'/(n+2)`; prove integrability of the base integrand from
   `h_G_meas` and `hM`; then apply
   `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
   This is genuine Cauchy-estimate/Leibniz content needed to prove the Rudin
   integral holomorphic in the envelope theorem.

   Proof transcript for `exists_localRudin_coordinate_update_margin`: write
   `R = δ / 2` and use `hz` to get `‖z‖ < R`; set
   `ε' = (R - ‖z‖) / 4`.  If `dist ζ (z j) ≤ 2ε'`, then every unchanged
   coordinate has norm at most `‖z‖`, while the changed coordinate has norm
   at most `‖z j‖ + dist ζ (z j) ≤ ‖z‖ + 2ε' < R`.  The Pi norm criterion
   gives `Function.update z j ζ ∈ ball 0 R`.  The Cauchy-circle version
   follows by the triangle inequality:
   `dist ζ (z j) ≤ dist ζ t + dist t (z j) ≤ ε' + ε'`.

   Proof transcript for `exists_localContinuousEOW_chart_window`: choose
   `ys` by `open_set_contains_basis hm C hC_open hC_ne`; use
   `localEOWRealChart_closedBall_subset hE_open x0 hx0 ys` to choose
   `ρ > 0` with the whole real chart closed ball inside `E`; apply
   `localEOWChart_twoSided_polywedge_mem` to the compact closed ball
   `Metric.closedBall 0 ρ`, using the image-in-`E` result as the `hB_E`
   hypothesis, to obtain one radius `r > 0` and plus/minus polywedge
   membership on the chart; finally apply `exists_localEOWSmp_delta` to obtain
   one `δ > 0` together with the numeric shrink inequalities
   `δ * 10 ≤ ρ` and `card * (δ * 10) < r`, then derive the plus/minus
   Rudin-arc membership by `localEOWChart_smp_upper_mem_of_delta` and
   `localEOWChart_smp_lower_mem_of_delta`.  This is the exact local
   replacement for the global
   "choose a cone basis and shrink the Rudin polydisc into the tube" step in
   `TubeDomainExtension.lean`; it introduces no boundary-value or
   holomorphy assumption.

   Proof transcript for `localEOWChart_ball_positive_mem_of_delta`: write
   `u j = (w j).re` and `v j = (w j).im`.  From
   `w ∈ ball 0 (δ / 2)` get `‖u‖ ≤ δ / 2 ≤ ρ`, so
   `u ∈ closedBall 0 ρ`; positivity of every `v j` gives `0 ≤ v j` and,
   because `Fin m` is nonempty from `hm`, `0 < ∑ j, v j`; and
   `∑ j, v j ≤ card * ‖w‖ < card * (δ / 2) < card * (δ * 10) < r`.
   Applying `hplus u v` and rewriting by `localEOWChart_real_imag` gives the
   result.  The negative theorem uses the same `u`, the same `v j = (w j).im`,
   the hypotheses `v j < 0`, the positive sum `0 < ∑ j, -v j`, and the
   analogous sum bound.  These lemmas are the precise side domains used for
   identity-theorem propagation; without an additional side-connectedness
   hypothesis, the proof must not claim agreement on arbitrary extra
   components of `U ∩ Ωplus` or `U ∩ Ωminus`.

   Proof transcript for
   `localEOWChart_smp_upper_mem_of_delta_on_sphere`: the proof is the same
   chart-polywedge decomposition as `localEOWChart_smp_upper_mem_of_delta`,
   except that the imaginary-sign input comes from the full unit-circle
   Möbius theorem `moebiusProd_im_pos`, not from the real-center theorem
   `moebiusProd_im_pos_of_real`.  Use
   `localEOWSmp_div_norm_lt_one_of_closedBall hδ hw` and `hl_norm` to prove
   `0 < (localEOWSmp δ w l j).im` for every coordinate; the real-part and
   finite-sum bounds are still supplied by
   `localEOWSmp_re_mem_closedBall` and
   `localEOWSmp_norm_le_extended_of_closedBall`.  The lower theorem uses
   `moebiusProd_im_neg`.  These two lemmas are essential for holomorphy of the
   Rudin integral as a function of the complex parameter `w`; the older real
   center lemmas are only enough for the boundary mean-value identity.

   Proof transcript for `aestronglyMeasurable_localRudinIntegrand`: split
   `ℝ` into the measurable sets `{θ | 0 < sin θ}` and `{θ | sin θ < 0}`.
   The map
   `θ ↦ localEOWChart x0 ys (localEOWSmp δ w (exp (θ I)))` is continuous by
   `continuous_localEOWSmp_theta` and `continuous_localEOWChart`.  On the
   positive sine set, membership in `Ωplus` is exactly
   `localEOWChart_smp_upper_mem_of_delta_on_sphere`, using
   `‖exp (θ I)‖ = 1`; on the negative sine set, use the lower theorem.
   Compose the continuous chart map with `hFplus_diff.continuousOn` and
   `hFminus_diff.continuousOn`, then combine the two branches by
   `AEStronglyMeasurable.piecewise`.  The zero-on-boundary theorem is a direct
   definitional reduction from `sin θ = 0` and supplies the `hG_zero` input
   for `differentiableAt_localRudin_parametric_integral`.

   Proof transcript for `continuousAt_localRudinIntegrand_param`: fix `θ` and
   set `l = exp (θ I)`, so `‖l‖ = 1`.  From
   `w0 ∈ ball 0 (δ / 2)`, use
   `localEOWSmp_div_norm_lt_one_of_closedBall hδ` to put `w0 / δ` in the
   unit polydisc, then apply `continuousAt_localEOWSmp_param δ l` and compose
   with `continuous_localEOWChart`.  If `0 < sin θ`, the integrand is locally
   the plus branch; the base point lies in `Ωplus` by
   `localEOWChart_smp_upper_mem_of_delta_on_sphere`, so
   `hFplus_diff.continuousOn.continuousAt` applies.  If `sin θ < 0`, use the
   lower theorem and `Fminus`.  If `sin θ = 0`, the integrand is the constant
   zero function.

   Proof transcript for `continuousAt_localRudinIntegral_of_bound`: apply
   `intervalIntegral.continuousAt_of_dominated_interval` with constant bound
   `M`.  Near `w0`, the ball is preserved by `Metric.isOpen_ball.mem_nhds`;
   measurability is `aestronglyMeasurable_localRudinIntegrand`; the uniform
   norm bound is `hM`; the bound is interval-integrable because it is constant;
   and pointwise continuity in `w` is
   `continuousAt_localRudinIntegrand_param`.

   Proof transcript for `differentiableAt_localRudinIntegrand_update`: set
   `l = exp (θ I)`, so `‖l‖ = 1`.  The map
   `ζ ↦ localEOWSmp δ (Function.update z j ζ) l` is holomorphic at `t`:
   divide by `δ`, use the coordinate update map into the unit polydisc at
   `t`, apply `moebiusProd_differentiable_w l`, and multiply each component
   by the constant `(δ : ℂ)`.  Composing with `localEOWChart` gives a
   holomorphic chart map.  If `0 < sin θ`, use
   `localEOWChart_smp_upper_mem_of_delta_on_sphere` to put the base point in
   `Ωplus`, then compose with `hFplus_diff.differentiableAt`; if
   `sin θ < 0`, use the lower theorem and `hFminus_diff`.  The impossible
   `sin θ = 0` case is excluded by `hsin`.

   Proof transcript for `differentiableAt_localRudinIntegral_of_bound`:
   choose `ε'` by `exists_localRudin_coordinate_update_margin hz j`, then
   apply `differentiableAt_localRudin_parametric_integral` with
   `G = localRudinIntegrand δ x0 ys Fplus Fminus`.  The measurability input is
   `aestronglyMeasurable_localRudinIntegrand`; the pointwise derivative input
   is `differentiableAt_localRudinIntegrand_update`; the zero-boundary input
   is `localRudinIntegrand_zero_of_sin_eq_zero`; and the only remaining
   external hypothesis is exactly the uniform bound `hM`.  Thus after this
   theorem the live analytic blocker for the coordinate envelope is only
   `exists_bound_localRudinIntegrand`.

   Proof transcript for `differentiableOn_localRudinIntegral_of_bound`: apply
   `osgood_lemma` on the open coordinate ball.  The continuity input at every
   point is `continuousAt_localRudinIntegral_of_bound`; the separately
   holomorphic input in coordinate `j` is
   `differentiableAt_localRudinIntegral_of_bound`.  The normalized envelope
   theorem follows by `DifferentiableOn.const_smul`, since
   `localRudinEnvelope` is the real scalar multiple
   `((2 * Real.pi)⁻¹ : ℝ)` of `localRudinIntegral`.

   Proof transcript for `differentiableOn_localRudinEnvelope`: obtain
   `⟨M,hM⟩` from `exists_bound_localRudinIntegrand`, then apply
   `differentiableOn_localRudinEnvelope_of_bound`.  This is the bound-free
   holomorphy theorem that the local continuous EOW envelope proof consumes.

   The next side-agreement block should be split before porting the full
   identity-theorem argument.  Define the line through a point in the positive
   or negative orthant:

   ```lean
   def localEOWLine {m : ℕ} (ζ : Fin m -> ℂ) (z : ℂ) : Fin m -> ℂ :=
     fun j => ((ζ j).re : ℂ) + z * ((ζ j).im : ℂ)

   theorem localEOWLine_I :
       localEOWLine ζ Complex.I = ζ

   theorem localEOWLine_im :
       (localEOWLine ζ z j).im = z.im * (ζ j).im

   theorem localEOWLine_real_im_zero :
       (localEOWLine ζ (t : ℂ) j).im = 0

   theorem localEOWLine_affine_real_combo
       (ζ : Fin m -> ℂ) (z1 z2 : ℂ) (a b : ℝ) (hab : a + b = 1) :
       localEOWLine ζ (a • z1 + b • z2) =
         a • localEOWLine ζ z1 + b • localEOWLine ζ z2

   theorem localEOWLine_chart_real
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (ζ : Fin m -> ℂ) (t : ℝ) :
       localEOWChart x0 ys (localEOWLine ζ (t : ℂ)) =
         realEmbed (localEOWRealChart x0 ys
           (fun j => (localEOWLine ζ (t : ℂ) j).re))

   theorem localEOWLine_re_closedBall_of_norm_le_two
       {m : ℕ} {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       {ζ : Fin m -> ℂ}
       (hζ : ζ ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       {z : ℂ} (hz : ‖z‖ ≤ 2) :
       (fun j => (localEOWLine ζ z j).re) ∈
         Metric.closedBall (0 : Fin m -> ℝ) ρ

   theorem localEOWChart_line_upper_mem_of_delta
       {m : ℕ} (hm : 0 < m)
       (Ωplus : Set (Fin m -> ℂ))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {ρ δ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus : ...positive chart polywedge membership...)
       {ζ : Fin m -> ℂ}
       (hζ : ζ ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (hζ_pos : ∀ j, 0 < (ζ j).im)
       {z : ℂ} (hz_norm : ‖z‖ ≤ 2) (hz_pos : 0 < z.im) :
       localEOWChart x0 ys (localEOWLine ζ z) ∈ Ωplus

   theorem localEOWChart_line_lower_mem_of_delta
       -- same statement with target `Ωminus`, `hminus`, and `z.im < 0`
       -- when `hζ_pos : ∀ j, 0 < (ζ j).im`.
   ```

   Proof transcript for the line-geometry lemmas:

   - `localEOWLine_I`, `localEOWLine_im`, and
     `localEOWLine_real_im_zero` are coordinatewise `Complex.ext`/`simp`
     calculations.
   - For the real-part bound, use
     `|(localEOWLine ζ z j).re| = |(ζ j).re + z.re * (ζ j).im|`.
     Bound this by `|(ζ j).re| + |z.re| * |(ζ j).im|`, then by
     `(1 + ‖z‖) * ‖ζ j‖`, hence by `3 * ‖ζ‖ < 3 * (δ/2)`.  Since
     `3 * (δ/2) ≤ δ * 10 ≤ ρ`, the Pi norm criterion gives membership in
     `closedBall 0 ρ`.
   - For upper line membership, set
     `u j = (localEOWLine ζ z j).re` and
     `v j = (localEOWLine ζ z j).im`.  The real-part lemma gives
     `u ∈ closedBall 0 ρ`; `localEOWLine_im`, `hz_pos`, and `hζ_pos` give
     `0 < v j` for every coordinate; the sum is positive because `0 < m`;
     and `v j ≤ |v j| ≤ ‖localEOWLine ζ z j‖ ≤ δ * 10`, using
     `‖localEOWLine ζ z j‖ ≤ ‖ζ j‖ + ‖z‖ * ‖ζ j‖ ≤ 3 * ‖ζ‖ < δ * 10`.
     Apply `hplus u hu v`.  The lower theorem is identical with
     `z.im < 0`, so every `v j < 0`, and applies `hminus`.
   - `localEOWLine_affine_real_combo` is the coordinatewise identity
     `Re ζ_j + (a z1 + b z2) Im ζ_j =
      a (Re ζ_j + z1 Im ζ_j) + b (Re ζ_j + z2 Im ζ_j)`, using
     `a + b = 1`.  This is the only convexity input needed for
     `L ⁻¹' ball 0 (δ/2)`.
   - `localEOWLine_chart_real` rewrites the chart on a real parameter line
     to `realEmbed` by first proving
     `localEOWLine ζ (t : ℂ) =
      fun j => ((localEOWLine ζ (t : ℂ) j).re : ℂ)` from
     `localEOWLine_real_im_zero`, then applying `localEOWChart_real`.

   The checked boundary-tendsto helpers used by the side-agreement theorem are
   written directly, not as abstract wrappers:

   ```lean
   theorem tendsto_localEOWLine_upper_to_boundaryValue
       {m : ℕ} (hm : 0 < m)
       (Ωplus : Set (Fin m -> ℂ))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {E : Set (Fin m -> ℝ)}
       (Fplus : (Fin m -> ℂ) -> ℂ) (bv : (Fin m -> ℝ) -> ℂ)
       (hFplus_bv :
         ∀ y ∈ E, Filter.Tendsto Fplus
           (nhdsWithin (realEmbed y) Ωplus) (nhds (bv y)))
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hplus : ...positive chart polywedge membership...)
       {ζ : Fin m -> ℂ}
       (hζ : ζ ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (hζ_pos : ∀ j, 0 < (ζ j).im)
       {x : ℝ} (hx : |x| < 2)
       (hE_mem :
         localEOWRealChart x0 ys
           (fun j => (localEOWLine ζ (x : ℂ) j).re) ∈ E) :
       Filter.Tendsto
         (fun z : ℂ => Fplus (localEOWChart x0 ys (localEOWLine ζ z)))
         (nhdsWithin (x : ℂ) EOW.UpperHalfPlane)
         (nhds (bv (localEOWRealChart x0 ys
           (fun j => (localEOWLine ζ (x : ℂ) j).re))))

   theorem tendsto_localEOWLine_lower_to_boundaryValue
       -- same statement with `Ωminus`, `Fminus`, `hFminus_bv`,
       -- `hminus`, and `nhdsWithin (x : ℂ) EOW.LowerHalfPlane`.

   theorem tendsto_localEOWLine_upper_to_boundaryValue_of_negative
       -- reflected statement: if `∀ j, (ζ j).im < 0`, the upper half-plane
       -- maps into `Ωminus`, so the branch is `Fminus`.

   theorem tendsto_localEOWLine_lower_to_boundaryValue_of_negative
       -- reflected statement: if `∀ j, (ζ j).im < 0`, the lower half-plane
       -- maps into `Ωplus`, so the branch is `Fplus`.
   ```

   Proof transcript for these tendsto helpers: compose `hFplus_bv` (or
   `hFminus_bv`) with
   `z ↦ localEOWChart x0 ys (localEOWLine ζ z)`.  The `nhds` component is
   continuity of `localEOWChart` composed with
   `differentiable_localEOWLine`, rewritten on the real point by
   `localEOWLine_chart_real`.  The principal-set component is eventual
   membership in `Ωplus`/`Ωminus`: from `|x| < 2`, a neighborhood of `x`
   inside the relevant half-plane also satisfies `‖z‖ < 2`; then apply
   `localEOWChart_line_upper_mem_of_delta` or
   `localEOWChart_line_lower_mem_of_delta`.

   The checked real-line Rudin boundary identity used in the identity theorem
   has the following exact inputs:

   ```lean
   theorem localRudinEnvelope_line_eq_boundary_of_real
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (E : Set (Fin m -> ℝ))
       (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (hE_open : IsOpen E)
       (bv : (Fin m -> ℝ) -> ℂ) (hbv_cont : ContinuousOn bv E)
       (hFplus_bv : ...)
       (hFminus_bv : ...)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hE_mem :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
           localEOWRealChart x0 ys u ∈ E)
       (hplus : ...positive chart polywedge membership...)
       (hminus : ...negative chart polywedge membership...)
       {ζ : Fin m -> ℂ} {t : ℝ}
       (hLt : localEOWLine ζ (t : ℂ) ∈
         Metric.ball (0 : Fin m -> ℂ) (δ / 2)) :
       localRudinEnvelope δ x0 ys Fplus Fminus
           (localEOWLine ζ (t : ℂ)) =
         bv (localEOWRealChart x0 ys
           (fun j => (localEOWLine ζ (t : ℂ) j).re))
   ```

   Proof transcript: apply `localRudinEnvelope_eq_boundary_of_real` to
   `w = localEOWLine ζ (t : ℂ)`.  The realness hypothesis is
   `localEOWLine_real_im_zero`; the closed-ball hypothesis is
   `Metric.ball_subset_closedBall hLt`; and the path condition required by
   `local_rudin_mean_value_real` is
   `hE_mem _ (localEOWSmp_re_mem_closedBall hδ hδρ
     (Metric.ball_subset_closedBall hLt) hs_norm)`.

   The helper and positive/negative side-agreement declarations in this block
   are now checked in
   `OSReconstruction/SCV/LocalContinuousEOWSideAgreement.lean`.
   With these line-geometry lemmas, the side-agreement theorem has the
   following surface:

   ```lean
   theorem localRudinEnvelope_eq_plus_on_positive_ball
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (E : Set (Fin m -> ℝ))
       (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (hE_open : IsOpen E)
       (bv : (Fin m -> ℝ) -> ℂ)
       (hbv_cont : ContinuousOn bv E)
       (hFplus_bv : ...)
       (hFminus_bv : ...)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hE_mem :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
           localEOWRealChart x0 ys u ∈ E)
       (hplus : ...positive chart polywedge membership...)
       (hminus : ...negative chart polywedge membership...)
       {ζ : Fin m -> ℂ}
       (hζ : ζ ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (hζ_pos : ∀ j, 0 < (ζ j).im) :
       localRudinEnvelope δ x0 ys Fplus Fminus ζ =
         Fplus (localEOWChart x0 ys ζ)
   ```

   Proof transcript for `localRudinEnvelope_eq_plus_on_positive_ball`:

   1. Define `L z = localEOWLine ζ z`; then `L I = ζ`, `L` is
      differentiable, and `L(t)` is real for real `t`.
   2. Define `bv_line t = bv (localEOWRealChart x0 ys
      (fun j => (L (t : ℂ) j).re))`.  Continuity of `bv_line` follows from
      `hbv_cont` and `localEOWLine_re_closedBall_of_norm_le_two`.
   3. Define
      `gp z = if z.im > 0 then Fplus (localEOWChart x0 ys (L z))
              else bv_line z.re`
      and
      `gm z = if z.im < 0 then Fminus (localEOWChart x0 ys (L z))
              else bv_line z.re`.
      The upper/lower branch holomorphy inputs for `local_edge_of_the_wedge_1d`
      come from `hFplus_diff`/`hFminus_diff` composed with
      `localEOWChart` and `L`; side-domain membership is exactly
      `localEOWChart_line_upper_mem_of_delta`/`lower_mem`.
   4. The boundary convergence inputs for `gp` and `gm` are
      `hFplus_bv`/`hFminus_bv` composed with the chart line tendsto, using
      `localEOWChart_line_*_mem_of_delta` as the eventual membership.  The
      real-axis continuity input is `bv_line` continuity.
   5. Apply `local_edge_of_the_wedge_1d (-2) 2` to obtain `F_1d` on a disk
      containing `I`; on the upper half-plane, `F_1d I =
      Fplus (localEOWChart x0 ys ζ)` by `L I = ζ`.
   6. For real `t` near `0`, `L(t)` lies in `ball 0 (δ/2)` by continuity of
      `L` and `L(0) = Re ζ`; apply `local_rudin_mean_value_real` to prove
      `localRudinEnvelope δ x0 ys Fplus Fminus (L(t)) = bv_line t`.
      The required real-edge path condition is supplied by
      `localEOWSmp_re_mem_closedBall hδ hδρ` and `hE_mem`.
   7. On
      `V = L ⁻¹' Metric.ball 0 (δ/2) ∩ U_L`, both
      `localRudinEnvelope ∘ L` and `F_1d` are analytic.  The first analytic
      statement uses `differentiableOn_localRudinEnvelope`; the second uses the
      holomorphy output of `local_edge_of_the_wedge_1d`.  They agree on real
      points accumulating at `0`, so
      `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` gives
      equality throughout `V`, in particular at `I`.

   Its Lean surface is:

   ```lean
   theorem localRudinEnvelope_eq_minus_on_negative_ball
       {m : ℕ} (hm : 0 < m)
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (E : Set (Fin m -> ℝ))
       (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (hE_open : IsOpen E)
       (bv : (Fin m -> ℝ) -> ℂ)
       (hbv_cont : ContinuousOn bv E)
       (hFplus_bv : ...)
       (hFminus_bv : ...)
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       {δ ρ r : ℝ} (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hE_mem :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
           localEOWRealChart x0 ys u ∈ E)
       (hplus : ...positive chart polywedge membership...)
       (hminus : ...negative chart polywedge membership...)
       {ζ : Fin m -> ℂ}
       (hζ : ζ ∈ Metric.ball (0 : Fin m -> ℂ) (δ / 2))
       (hζ_neg : ∀ j, (ζ j).im < 0) :
       localRudinEnvelope δ x0 ys Fplus Fminus ζ =
         Fminus (localEOWChart x0 ys ζ)
   ```

   Proof transcript for `localRudinEnvelope_eq_minus_on_negative_ball`:

   1. Define the same line `L z = localEOWLine ζ z`; then `L I = ζ`,
      `L` is differentiable, `L(t)` is real for real `t`, and `L(0)` remains
      in the small Rudin ball.  The only sign change is geometric: if
      `∀ j, (ζ j).im < 0`, then increasing the one-variable imaginary
      parameter moves the local EOW chart into the negative side, while
      decreasing it moves the chart into the positive side.
   2. Define
      `bv_line t = bv (localEOWRealChart x0 ys
      (fun j => (L (t : ℂ) j).re))`.  Continuity is identical to the positive
      theorem's continuity proof: restrict `localEOWLine_re_closedBall_of_norm_le_two`
      through `hE_mem` and compose `hbv_cont` with the real chart line.
   3. Define the one-variable upper/lower branches with the swapped side
      functions:
      `gp z = if z.im > 0 then Fminus (localEOWChart x0 ys (L z))
              else bv_line z.re`
      and
      `gm z = if z.im < 0 then Fplus (localEOWChart x0 ys (L z))
              else bv_line z.re`.
      Holomorphy of the upper branch now uses `hFminus_diff` and
      `localEOWChart_line_upper_mem_of_delta_of_negative`; holomorphy of the
      lower branch uses `hFplus_diff` and
      `localEOWChart_line_lower_mem_of_delta_of_negative`.
   4. The boundary convergence inputs are also side-swapped.  As `z` approaches
      the real axis from the upper half-plane, use
      `tendsto_localEOWLine_upper_to_boundaryValue_of_negative` and
      `hFminus_bv`; from the lower half-plane, use
      `tendsto_localEOWLine_lower_to_boundaryValue_of_negative` and
      `hFplus_bv`.  Both limits have the same real-edge value `bv_line t`.
   5. Apply `local_edge_of_the_wedge_1d (-2) 2` to these `gp` and `gm`.
      Since `I.im > 0` and `L I = ζ`, the one-variable extension evaluates at
      `I` as `Fminus (localEOWChart x0 ys ζ)`.
   6. For real `t` near `0`, the proof that
      `localRudinEnvelope δ x0 ys Fplus Fminus (L(t)) = bv_line t` is the
      same real-axis mean-value calculation as in the positive theorem:
      `L(t)` is real, remains in `ball 0 (δ/2)`, and the required real-edge
      path condition is supplied by `localEOWSmp_re_mem_closedBall hδ hδρ`
      and `hE_mem`.
   7. On the same preconnected neighborhood
      `V = L ⁻¹' Metric.ball 0 (δ/2) ∩ U_L`, the analytic functions
      `localRudinEnvelope ∘ L` and the one-variable EOW extension agree on
      real points accumulating at `0`; the identity theorem gives equality
      throughout `V`, and in particular at `I`, proving the displayed
      negative-side equality.

   Proof transcript for `exists_bound_localRudinIntegrand`: reproduce the
   checked `G_bound` block in `TubeDomainExtension.lean` with the local chart
   names and no source/QFT objects.  Let

   `S = closedBall (0 : Fin m -> ℂ) (δ / 2) ×ˢ sphere (0 : ℂ) 1`

   and define the continuous extension on `S` by

   ```lean
   h (w,l) =
     if 0 < l.im then
       Fplus (localEOWChart x0 ys (localEOWSmp δ w l))
     else if l.im < 0 then
       Fminus (localEOWChart x0 ys (localEOWSmp δ w l))
     else
       bv (localEOWRealChart x0 ys
         (fun j => (localEOWSmp δ w l j).re))
   ```

   The compactness input is
   `IsCompact.prod (isCompact_closedBall ...) (isCompact_sphere ...)`.
   Continuity of `p ↦ localEOWChart x0 ys (localEOWSmp δ p.1 p.2)` on
   `closedBall × closedBall` is proved coordinatewise from
   `moebiusRudin_continuousOn`, using
   `‖w j / δ‖ < 1` on the closed half-radius ball.  The real-coordinate map
   `p ↦ localEOWRealChart x0 ys (fun j => (localEOWSmp δ p.1 p.2 j).re)` is
   then continuous by composing with `continuous_re` and
   `continuous_localEOWRealChart`.

   For a point `(w0,l0) ∈ S`, split by `l0.im > 0`, `< 0`, or `= 0`.
   In the positive case, `h` locally agrees with the `Fplus` branch and
   `localEOWChart_smp_upper_mem_of_delta_on_sphere` puts the base point in
   `Ωplus`; `hFplus_diff.differentiableAt` gives continuity.  The negative
   case is identical with
   `localEOWChart_smp_lower_mem_of_delta_on_sphere` and `Fminus`.
   In the boundary case, set
   `x' = localEOWRealChart x0 ys (fun j => (localEOWSmp δ w0 l0 j).re)`.
   `localEOWChart_smp_realEdge_eq_of_unit_real` identifies the chart point
   with `realEmbed x'`, while `localEOWSmp_re_mem_closedBall hδ hδρ` and
   `hE_mem` prove `x' ∈ E`.  On the positive and negative pieces of a
   neighborhood in `S`, compose the chart tendsto with
   `hFplus_bv x'` and `hFminus_bv x'`; on the real piece, use
   `hbv_cont.continuousWithinAt` composed with the real-coordinate map.
   The three closed pieces `{Im l > 0}`, `{Im l < 0}`, `{Im l = 0}` cover
   `S`, so `ContinuousWithinAt.union` combines the three tendsto statements.

   With `ContinuousOn h S`, `hS_cpt.exists_bound_of_continuousOn h_cont`
   gives `M` such that `‖h (w,l)‖ ≤ M` on `S`.  For any
   `w ∈ ball 0 (δ / 2)` and real `θ`, put `l = exp (θ I)`, so
   `l ∈ sphere 0 1` and `l.im = sin θ`.  If `sin θ > 0` or `< 0`, both
   `localRudinIntegrand ... w θ` and `h (w,l)` choose the same side branch;
   if `sin θ = 0`, the integrand is zero and the bound follows from
   nonnegativity of the compact bound.  This proves the uniform bound needed
   by `differentiableAt_localRudinIntegral_of_bound`.

   The two `localEOWChart_smp_*_mem_of_delta`
   theorems then prove the actual Rudin arc membership in the upper and lower
   local chart wedges: the real part is controlled by
   `localEOWSmp_re_mem_closedBall`, the imaginary coordinates have the correct
   sign by `localEOWSmp_im_pos_of_real`/`localEOWSmp_im_neg_of_real`, and
   `∑ |Im| < r` follows from the finite-cardinality bound
   `(Fintype.card (Fin m) : ℝ) * (δ * 10) < r`.  Finally
   `exists_localEOWChart_smp_delta` chooses a single small `δ`, explicitly
   `min (ρ / 20) (r / (card * 20))` up to definitional unfolding, that works
   for both sides.  This is the Lean-ready replacement for the informal
   "shrink the local Rudin map into the polywedge" step.
5. `localEOW_pullback_boundary_value` transports the distributional boundary
   value to the chart.  If `L : (Fin m -> ℝ) ≃L[ℝ] (Fin m -> ℝ)` sends the
   standard basis to `ys`, then
   `Tchart ψ = T (chartPushTest L x0 ψ)` where `chartPushTest` includes the
   absolute determinant/Jacobian factor.  This is a structured change of
   variables, not ad hoc manipulation of integrals.
6. `localEOW_uniform_slowGrowth_order` combines `hslow_plus` and `hslow_minus`
   on the chosen compact real box and compact simplex of chart directions.
   It returns one order `N0` and one radius `r0` valid for both signs after
   pullback.  These estimates justify Fubini, dominated convergence, and
   continuity of the regularized boundary traces.
7. Choose nested boxes `B0 ⋐ B1 ⋐ Echart` and a support radius `rψ > 0` so
   `u ∈ B0` and `t ∈ closedBall 0 rψ` imply `u + t ∈ B1`.  Shrink the plus and
   minus polywedges over `B0` so every real translate by `t` in the same support
   ball remains in the corresponding plus/minus local wedge over `B1`.
8. For every compactly supported Schwartz kernel `ψ` with
   `tsupport ψ ⊆ closedBall 0 rψ`, define
   `Fplusψ z = ∫ t, FplusChart (z + realEmbed t) * ψ t` and similarly for the
   minus side.  The checked theorem
   `localRealMollifySide_holomorphicOn_of_translate_margin` proves these are
   holomorphic on the shrunken polywedges from the explicit support-margin
   hypothesis.
9. Define the continuous boundary function
   `bvψ u = Tchart (translateSchwartz (-u) ψ)` on `B0`.
   `localRealMollify_commonContinuousBoundary_of_clm` proves continuity of
   `bvψ` and the plus/minus boundary convergence after
   `sliceCLM_family_from_distributionalBoundary` constructs the plus/minus
   slice functionals and their convergence to `Tchart`.  This is exactly the
   Streater-Wightman `T(f_x)` boundary-value step; it is not an assumption of
   common continuous boundary.
10. Apply `localContinuousEOW_envelope` to `Fplusψ`, `Fminusψ`, and `bvψ`,
    producing a regularized envelope `Gψ` on a fixed local complex
    neighborhood `U0` determined by `B0`, `B1`, and `rψ`, not by the individual
    values of `ψ`.
11. Transport the smoothing kernel through the real linear part of the local
    EOW chart:
    `Gchart ψ w = G (localEOWRealLinearKernelPushforwardCLM ys hli ψ) w`.
    The inverse-determinant factor in this pushforward is mandatory; otherwise
    the side real-mollifier integral is in the wrong coordinates.
12. Build the localized mixed CLM `K` by the four helper layers recorded below:
    complex-chart cutoff, SCV-local partial evaluation, compact uniform
    value-CLM bound, and the cutoff/slice integral.  On supported product
    tests this `K` represents `∫ z, Gchart ψ z * φ z`; outside the support
    windows it is only a localization device.
13. Prove `ProductKernelRealTranslationCovariantLocal K Ucov r`, not global
    covariance.  The proof expands the supported product-test representation,
    changes variables in the complex-chart integral, and applies
    `regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap` on
    the support of `φ`.
14. Descend locally to a chart distribution `Hdist` by the product-test
    sheared-fiber argument with margin
    `Udesc + closedBall 0 (r + rη) ⊆ Ucov`; then prove local distributional
    holomorphy of `Hdist` and recover the holomorphic representative by
    `distributionalHolomorphic_regular`, the checked pointwise representation
    bridge, and the checked delta-limit wedge-agreement theorem.  This replaces
    the obsolete "global kernel by cutoff" shortcut.
15. Let `ψρ` be a compactly supported approximate identity in chart-kernel
    coordinates with eventual support in `closedBall 0 r`.  On the plus/minus
    wedge pieces, the side identities for `Gchart ψρ` reduce through
    `realMollifyLocal_localEOWRealLinearKernelPushforwardCLM` to the
    chart-coordinate real mollifiers, and the existing approximate-identity
    theorem gives convergence to `FplusChart`/`FminusChart`.  Therefore the
    recovered representative is the desired chart envelope.
16. `distributionalEOW_extensions_compatible` proves agreement of two local
   chart envelopes on overlaps by the ordinary identity theorem: on every
   nonempty overlap the extensions agree with `Fplus` on a positive wedge
   subset, or with `Fminus` on a negative wedge subset.  The already-proved
   distributional uniqueness theorem can still be used as a fallback on tube
   shaped overlap charts, but it is not the envelope-construction step.
17. `localDistributionalEOW_patch_extensions` follows the existing patching
   pattern in `SCV.edge_of_the_wedge_theorem`: define the extension by local
   representatives and use compatibility to prove well-definedness and
   holomorphy.

This package is substantial SCV mathematics.  Do not replace it by a record of
boundary-limit fields, and do not introduce it as an axiom.

Lean pseudocode for the core reductions:

Regularization notation that must be instantiated before theorem proving:

1. `KernelSupportWithin ψ r` is the checked production predicate
   `tsupport (ψ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 r`.
   It does **not** duplicate compact support as a second field.  Compact
   support is a derived theorem in finite-dimensional real space:

   ```lean
   theorem KernelSupportWithin_hasCompactSupport
       {m : ℕ} {ψ : SchwartzMap (Fin m -> ℝ) ℂ} {r : ℝ}
       (hψ : KernelSupportWithin ψ r) :
       HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ) := by
     exact IsCompact.of_isClosed_subset
       (isCompact_closedBall 0 r) (isClosed_tsupport _) hψ
   ```

   All regularization lemmas that need compact support must consume this
   theorem explicitly.  Do not change the predicate into a bundled record; the
   current closed-ball support statement is the right local margin hypothesis.
2. `BoxMargin B0 B1 r` means
   `∀ u ∈ B0, ∀ t ∈ Metric.closedBall 0 r, u + t ∈ B1`.
3. `LocalTranslateMargin Dsmall Dlarge r` means
   `∀ z ∈ Dsmall, ∀ t ∈ Metric.closedBall 0 r,
     z + realEmbed t ∈ Dlarge`.
   This name is only a short abbreviation for the displayed support-margin
   fact.  Production proofs should unfold it or use a theorem whose statement
   exposes exactly this closed-ball real-translation condition; it must not be
   treated as an opaque boundary-value predicate.
4. `realMollifyLocal F ψ z` is
   `∫ t : Fin m -> ℝ, F (z + realEmbed t) * ψ t`.
   This is the same convention already used by
   `differentiableOn_realMollify_tubeDomain`.
5. `mollifiedBoundary T ψ u` is
   `T (translateSchwartz (-u) ψ)`.  With the convention
   `translateSchwartz a ψ x = ψ (x + a)`, this is the boundary value of
   `realMollifyLocal F ψ` at the real point `u` after the checked
   change-of-variables identity rewrites the mollifier as the slice functional
   at imaginary part `im z` evaluated on the translated test kernel.
6. `SmallKernelSpace r` is the test-kernel space used by the kernel theorem:
   in production Lean this should be implemented by a fixed smooth cutoff
   `χr` rather than by introducing a new LF-space wrapper.  Choose
   `χr = 1` on `closedBall 0 r` and `tsupport χr ⊆ closedBall 0 rLarge`.
   Then `ψ ↦ χr • ψ` is a continuous linear map on `SchwartzMap`, and it
   agrees with the identity on all kernels whose support is contained in
   `closedBall 0 r`.  This gives an honest
   `SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ` substrate for the kernel theorem.
7. `CompactSupportedApproxIdentity ψι l` is only a documentation shorthand for
   the concrete data used by the proof: every `ψι i` is a compactly supported
   Schwartz kernel, eventually `tsupport ψι i ⊆ Metric.closedBall 0 r` for the
   fixed radius in the local construction, `∫ t, ψι i t = 1`, and convolution
   against `ψι i` tends to the identity in the Schwartz topology.  Do not
   introduce it as an opaque production structure unless the fields are exactly
   these analytic obligations.

```lean
lemma localWedge_truncated_maps_compact_subcone
    {m : ℕ} {Ωplus Ωminus : Set (Fin m -> ℂ)}
    {E C : Set (Fin m -> ℝ)}
    (hlocal_wedge :
      ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ E ->
        ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (φ : SchwartzMap (Fin m -> ℝ) ℂ)
    (hφ_compact : HasCompactSupport (φ : (Fin m -> ℝ) -> ℂ))
    (hφ_supp : tsupport (φ : (Fin m -> ℝ) -> ℂ) ⊆ E)
    (Kη : Set (Fin m -> ℝ)) (hKη_compact : IsCompact Kη) (hKη_sub : Kη ⊆ C) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ tsupport (φ : (Fin m -> ℝ) -> ℂ),
        ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
          (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
          (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus

lemma localEOW_choose_cone_basis
    {m : ℕ}
    (C : Set (Fin m -> ℝ))
    (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C)
    (hC_ne : C.Nonempty)
    (hC_cone : ∀ (t : ℝ), 0 < t -> ∀ y ∈ C, t • y ∈ C) :
    ∃ (ys : Fin m -> Fin m -> ℝ),
      LinearIndependent ℝ ys ∧
      (∀ j, ys j ∈ C) ∧
      (∀ a : Fin m -> ℝ,
        (∀ j, 0 < a j) ->
          (∑ j, a j • ys j) ∈ C)

-- Checked in `SCV/LocalContinuousEOW.lean`; shown here as the active API:
def localEOWRealChart
    {m : ℕ}
    (x0 : Fin m -> ℝ)
    (ys : Fin m -> Fin m -> ℝ) :
    (Fin m -> ℝ) -> (Fin m -> ℝ)

def localEOWChart
    {m : ℕ}
    (x0 : Fin m -> ℝ)
    (ys : Fin m -> Fin m -> ℝ) :
    (Fin m -> ℂ) -> (Fin m -> ℂ)

def IsOpenAxisBox {m : ℕ} (B : Set (Fin m -> ℝ)) : Prop :=
  ∃ a b : Fin m -> ℝ,
    (∀ j, a j < b j) ∧ B = {u | ∀ j, a j < u j ∧ u j < b j}

def PositivePolywedge {m : ℕ} (B : Set (Fin m -> ℝ)) (δ : ℝ) :
    Set (Fin m -> ℂ) :=
  {z | (fun j => (z j).re) ∈ B ∧ ∀ j, 0 < (z j).im ∧ (z j).im < δ}

def NegativePolywedge {m : ℕ} (B : Set (Fin m -> ℝ)) (δ : ℝ) :
    Set (Fin m -> ℂ) :=
  {z | (fun j => (z j).re) ∈ B ∧ ∀ j, -δ < (z j).im ∧ (z j).im < 0}

lemma localEOWRealChart_closedBall_subset
    {m : ℕ} {E : Set (Fin m -> ℝ)}
    (hE_open : IsOpen E)
    (x0 : Fin m -> ℝ)
    (hx0 : x0 ∈ E)
    (ys : Fin m -> Fin m -> ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : Fin m -> ℝ,
        u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ ->
          localEOWRealChart x0 ys u ∈ E)

lemma localEOW_closedBall_support_margin
    {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) (ρ / 2),
      ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r,
        u + t ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ

lemma localEOW_nested_closed_balls
    {m : ℕ} {E : Set (Fin m -> ℝ)}
    (hE_open : IsOpen E)
    (x0 : Fin m -> ℝ)
    (hx0 : x0 ∈ E)
    (ys : Fin m -> Fin m -> ℝ) :
    ∃ ρ r : ℝ, 0 < r ∧
      0 < ρ ∧
      (∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E) ∧
      (∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) (ρ / 2),
        ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r,
          u + t ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ)

def KernelSupportWithin
    {m : ℕ}
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (r : ℝ) : Prop :=
  tsupport (ψ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 r

theorem KernelSupportWithin_hasCompactSupport
    {m : ℕ} {ψ : SchwartzMap (Fin m -> ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ)

theorem KernelSupportWithin.smulLeftCLM
    {m : ℕ}
    (χ : (Fin m -> ℝ) -> ℂ)
    {ψ : SchwartzMap (Fin m -> ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    KernelSupportWithin (SchwartzMap.smulLeftCLM ℂ χ ψ) r

theorem KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall
    {m : ℕ}
    (χ : SchwartzMap (Fin m -> ℝ) ℂ)
    {ψ : SchwartzMap (Fin m -> ℝ) ℂ} {r : ℝ}
    (hχ_one :
      ∀ x : Fin m -> ℝ, x ∈ Metric.closedBall (0 : Fin m -> ℝ) r ->
        χ x = 1)
    (hψ : KernelSupportWithin ψ r) :
    SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ = ψ

-- Checked cutoff existence used in the product-kernel step.  Do not cite the
-- old `KernelCutoff` or `cutoffKernelCLM` placeholders as declarations.
theorem exists_schwartz_cutoff_eq_one_on_closedBall
    {m : ℕ} {r rLarge : ℝ} (hr : 0 < r) (hrLarge : r < rLarge) :
    ∃ χ : SchwartzMap (Fin m -> ℝ) ℂ,
      (∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r, χ t = 1) ∧
      tsupport (χ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 rLarge

theorem exists_closedBall_integral_clm_of_continuousOn
    {m : ℕ} {R : ℝ} {g : (Fin m -> ℝ) -> ℂ}
    (hg_cont : ContinuousOn g (Metric.closedBall (0 : Fin m -> ℝ) R)) :
    ∃ T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        T ψ = ∫ x in Metric.closedBall (0 : Fin m -> ℝ) R, g x * ψ x

def BoxMargin
    {m : ℕ}
    (B0 B1 : Set (Fin m -> ℝ))
    (r : ℝ) : Prop :=
  ∀ u ∈ B0, ∀ t ∈ Metric.closedBall 0 r, u + t ∈ B1

def LocalTranslateMargin
    {m : ℕ}
    (Dsmall Dlarge : Set (Fin m -> ℂ))
    (r : ℝ) : Prop :=
  ∀ z ∈ Dsmall, ∀ t ∈ Metric.closedBall 0 r, z + realEmbed t ∈ Dlarge

noncomputable def realMollifyLocal
    {m : ℕ}
    (F : (Fin m -> ℂ) -> ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
    (Fin m -> ℂ) -> ℂ :=
  fun z => ∫ t : Fin m -> ℝ, F (z + realEmbed t) * ψ t

noncomputable def mollifiedBoundary
    {m : ℕ}
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
    (Fin m -> ℝ) -> ℂ :=
  fun u => T (translateSchwartz (-u) ψ)

theorem localRealMollifySide_holomorphicOn_of_translate_margin
    {m : ℕ}
    (F : ComplexChartSpace m -> ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (Ω D : Set (ComplexChartSpace m))
    (hΩ_open : IsOpen Ω)
    (hD_open : IsOpen D)
    (hF_holo : DifferentiableOn ℂ F Ω)
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ))
    (hmargin :
      ∀ z ∈ D, ∀ t ∈ tsupport (ψ : (Fin m -> ℝ) -> ℂ),
        z + realEmbed t ∈ Ω) :
    DifferentiableOn ℂ (realMollifyLocal F ψ) D

theorem regularizedBoundaryValue_continuousOn
    {m : ℕ}
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (E : Set (Fin m -> ℝ))
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ)) :
    ContinuousOn (fun x : Fin m -> ℝ =>
      T (translateSchwartz (-x) ψ)) E

theorem localRealMollify_commonContinuousBoundary_of_clm
    {m : ℕ}
    (Ωplus Ωminus : Set (ComplexChartSpace m))
    {Cplus Cminus : Set (Fin m -> ℝ)}
    (Fplus Fminus : ComplexChartSpace m -> ℂ)
    (Tplus Tminus :
      (Fin m -> ℝ) -> SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (B : Set (Fin m -> ℝ))
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ))
    (hΩplus_sub : Ωplus ⊆ TubeDomain Cplus)
    (hΩminus_sub : Ωminus ⊆ TubeDomain Cminus)
    (hplus_eval :
      ∀ w ∈ Ωplus,
        realMollifyLocal Fplus ψ w =
          Tplus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ w ∈ Ωminus,
        realMollifyLocal Fminus ψ w =
          Tminus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f))) :
    ContinuousOn (fun x : Fin m -> ℝ =>
      Tchart (translateSchwartz (-x) ψ)) B ∧
    (∀ x ∈ B,
      Tendsto (realMollifyLocal Fplus ψ)
        (nhdsWithin (realEmbed x) Ωplus)
        (nhds (Tchart (translateSchwartz (-x) ψ)))) ∧
    (∀ x ∈ B,
      Tendsto (realMollifyLocal Fminus ψ)
        (nhdsWithin (realEmbed x) Ωminus)
        (nhds (Tchart (translateSchwartz (-x) ψ))))

lemma regularizedLocalEOW_window_from_continuousEOW
    {m : ℕ}
    (DplusSmall DminusSmall : Set (Fin m -> ℂ))
    (B C : Set (Fin m -> ℝ))
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (r : ℝ) :
    ∃ (U0 : Set (Fin m -> ℂ)),
      IsOpen U0 ∧
      (∀ u ∈ B, realEmbed u ∈ U0) ∧
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        KernelSupportWithin ψ r ->
          ∃ Gψ : (Fin m -> ℂ) -> ℂ,
            DifferentiableOn ℂ Gψ U0 ∧
            (∀ z ∈ U0 ∩ DplusSmall,
              Gψ z = realMollifyLocal Fplus ψ z) ∧
            (∀ z ∈ U0 ∩ DminusSmall,
              Gψ z = realMollifyLocal Fminus ψ z) ∧
            (∀ Hψ : (Fin m -> ℂ) -> ℂ,
              DifferentiableOn ℂ Hψ U0 ->
              (∀ z ∈ U0 ∩ DplusSmall,
                Hψ z = realMollifyLocal Fplus ψ z) ->
              ∀ z ∈ U0, Hψ z = Gψ z)

The old schematic `regularizedEnvelope_valueCLM_of_cutoff` surface with an
abstract `G` and only a supported-kernel conclusion has been superseded by the
checked theorem of the same mathematical role below.  The checked theorem
works with the explicit fixed-window Rudin formula, constructs `Lw` on all
Schwartz kernels after cutoff, and leaves cutoff removal for the smaller
supported-kernel class as a separate identity step.

This value-CLM theorem is **not** available from additivity/homogeneity alone.
The next proof must supply the actual seminorm bound for the explicit local
Rudin envelope value.  The checked first estimate is:

```lean
theorem exists_bound_realMollifyLocal_smulLeftCLM
    {m : ℕ}
    (F : ComplexChartSpace m -> ℂ)
    (Ω : Set (ComplexChartSpace m))
    (z : ComplexChartSpace m)
    (r : ℝ)
    (χ : SchwartzMap (Fin m -> ℝ) ℂ)
    (hF_cont : ContinuousOn F Ω)
    (hmargin :
      ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r, z + realEmbed t ∈ Ω)
    (hχ_support :
      tsupport (χ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        ‖realMollifyLocal F
            (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ) z‖ ≤
          C * SchwartzMap.seminorm ℂ 0 0 ψ
```

The first direct Rudin-envelope estimate is now checked:

```lean
theorem exists_bound_localRudinEnvelope_smulLeftCLM_of_side_bounds
    (δ : ℝ)
    (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
    (Fplus Fminus : ComplexChartSpace m -> ℂ)
    (χ : SchwartzMap (Fin m -> ℝ) ℂ)
    (w : ComplexChartSpace m)
    (Cplus Cminus : ℝ)
    (hplus_bound :
      ∀ θ : ℝ, 0 < Real.sin θ ->
        ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
          ‖realMollifyLocal Fplus
              (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ)
              (localEOWChart x0 ys
                (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))‖ ≤
            Cplus * SchwartzMap.seminorm ℂ 0 0 ψ)
    (hminus_bound :
      ∀ θ : ℝ, Real.sin θ < 0 ->
        ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
          ‖realMollifyLocal Fminus
              (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ)
              (localEOWChart x0 ys
                (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))‖ ≤
            Cminus * SchwartzMap.seminorm ℂ 0 0 ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        ‖localRudinEnvelope δ x0 ys
            (fun z =>
              realMollifyLocal Fplus
                (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ) z)
            (fun z =>
              realMollifyLocal Fminus
                (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ) z)
            w‖ ≤
          C * SchwartzMap.seminorm ℂ 0 0 ψ
```

This theorem is **not** the full endpoint estimate.  It only applies once a
uniform zeroth-seminorm side bound is already available.  Near the real edge,
the OS-II distributional boundary value can require higher Schwartz seminorms;
the correct endpoint-facing estimate uses Banach-Steinhaus:

```lean
theorem exists_schwartz_bound_normalized_intervalIntegral_clm_family
    (T : ℝ -> SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
    (hT_bound :
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        ∃ C : ℝ, ∀ θ ∈ Set.uIoc (-Real.pi) Real.pi, ‖T θ ψ‖ ≤ C) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        ‖((2 * Real.pi)⁻¹ : ℝ) •
            ∫ θ in (-Real.pi)..Real.pi, T θ ψ‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ) ψ
```

The endpoint value estimate is now checked with a finite Schwartz-seminorm
bound, not with the false stronger `seminorm ℂ 0 0` bound:

```lean
theorem exists_schwartz_bound_localRudinEnvelope_smulLeftCLM_value
    -- same fixed window hypotheses as
    -- `regularizedLocalEOW_family_from_fixedWindow`, instantiated at the
    -- larger cutoff support radius `rLarge`
    (χ : SchwartzMap (Fin m -> ℝ) ℂ)
    (hχ_support :
      tsupport (χ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 rLarge) :
    ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
          ‖localRudinEnvelope δ x0 ys
              (realMollifyLocal Fplus
                (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ))
              (realMollifyLocal Fminus
                (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ))
              w‖ ≤
            C * s.sup (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ) ψ
```

The checked proof factors through:

1. For fixed `w`, define an interval family of real-linear CLMs `Tθ` on all
   Schwartz kernels:
   - if `0 < sin θ`, `Tθ` is the side value CLM for the plus sample point
     `localEOWChart x0 ys (localEOWSmp δ w (exp (θ * I)))`;
   - if `sin θ < 0`, `Tθ` is the analogous minus side value CLM;
   - if `sin θ = 0`, `Tθ = 0`, matching `localRudinIntegrand`.
2. The side value CLMs are constructed by
   `exists_realMollifyLocal_valueCLM_of_closedBall`, using the closed-ball
   translate-margin hypotheses for the larger cutoff radius `rLarge`.
3. Prove the exact evaluation identity
   `Tθ ψ = localRudinIntegrand δ x0 ys (realMollifyLocal Fplus (χ • ψ))
     (realMollifyLocal Fminus (χ • ψ)) w θ` on `Set.uIoc (-π) π`.
4. For each fixed `ψ`, apply the already checked local continuous EOW compact
   bound to the regularized pair with kernel `χ • ψ`.  This gives pointwise
   boundedness of `θ ↦ Tθ ψ`; it uses the real-edge boundary value and is the
   endpoint step that prevents false zeroth-seminorm compactness assumptions.
5. Apply `exists_schwartz_bound_normalized_intervalIntegral_clm_family` to get
   one finite Schwartz-seminorm bound for the normalized Rudin integral.

The value-CLM construction is now checked:

```lean
theorem regularizedEnvelope_valueCLM_of_cutoff
    -- fixed-window hypotheses instantiated at `rLarge`
    (χ : SchwartzMap (Fin m -> ℝ) ℂ)
    (hχ_support :
      tsupport (χ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 rLarge) :
    ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
      ∃ Lw : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
        ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
          Lw ψ =
            localRudinEnvelope δ x0 ys
              (fun z => realMollifyLocal Fplus
                (SchwartzMap.smulLeftCLM ℂ
                  (χ : (Fin m -> ℝ) -> ℂ) ψ) z)
              (fun z => realMollifyLocal Fminus
                (SchwartzMap.smulLeftCLM ℂ
                  (χ : (Fin m -> ℝ) -> ℂ) ψ) z)
              w
```

Its checked proof:

1. Use `exists_schwartz_bound_localRudinEnvelope_smulLeftCLM_value` for the
   finite seminorm bound.
2. Prove additivity of `ψ ↦ G (χ • ψ) w` from the checked
   `regularizedLocalEOW_family_add`, the larger-radius support theorem
   `KernelSupportWithin.smulLeftCLM_of_leftSupport`, and linearity of
   `SchwartzMap.smulLeftCLM`.
3. Prove complex homogeneity the same way using
   `regularizedLocalEOW_family_smul`.
4. Feed additivity, homogeneity, and the finite seminorm bound into
   `SchwartzMap.mkCLMtoNormedSpace`.
5. For the downstream supported-kernel statement, use
   `KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall` to remove the
   cutoff on kernels supported in the smaller ball `closedBall 0 r`.

The next genuine theorem-2 target is therefore not the global product-kernel
supplier.  The local fixed-window family must first be converted to a
chart-kernel family and then localized by honest cutoffs.  In chart
coordinates the family used downstream is

```lean
def Gchart (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (w : ComplexChartSpace m) : ℂ :=
  localRudinEnvelope δ x0 ys
    (realMollifyLocal Fplus
      (localEOWRealLinearKernelPushforwardCLM ys hli ψ))
    (realMollifyLocal Fminus
      (localEOWRealLinearKernelPushforwardCLM ys hli ψ)) w
```

For a chart-kernel radius `rχ`, choose the original-edge fixed-window radius
`rψ` so that

```lean
∀ ψ, KernelSupportWithin ψ rχ ->
  KernelSupportWithin
    (localEOWRealLinearKernelPushforwardCLM ys hli ψ) rψ
```

is discharged by
`KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM`.  For translated
kernels the caller either assumes
`KernelSupportWithin (translateSchwartz a ψ) rχ` or derives the larger-radius
bound from
`KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_translateSchwartz`.
The product-test representation to be constructed is local:

```lean
∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
  (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
  SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucov ->
  KernelSupportWithin ψ rχ ->
    K (schwartzTensorProduct₂ φ ψ) =
      ∫ z : ComplexChartSpace m, Gchart ψ z * φ z
```

The resulting covariance target is
`ProductKernelRealTranslationCovariantLocal K Ucov rχ`, not
`ProductKernelRealTranslationCovariantGlobal K`.  The fixed complex cutoff
used to make `K` a global mixed Schwartz CLM is only a localization device; it
is invisible on tests supported in `Ucov`, and it is never used as evidence for
global translation covariance.

The checked covariance mini-layer supplying this route is:

```lean
theorem realMollifyLocal_localEOWChart_kernelPushforwardCLM
    (F : ComplexChartSpace m -> ℂ)
    (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m -> ℝ) ℂ)
    (w : ComplexChartSpace m) :
    realMollifyLocal F (localEOWRealLinearKernelPushforwardCLM ys hli φ)
        (localEOWChart x0 ys w) =
      ∫ u : Fin m -> ℝ,
        F (localEOWChart x0 ys (w + realEmbed u)) * φ u

theorem realMollifyLocal_localEOWChart_translate_kernelPushforwardCLM
    (F : ComplexChartSpace m -> ℂ)
    (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m -> ℝ) ℂ)
    (a : Fin m -> ℝ)
    (w : ComplexChartSpace m) :
    realMollifyLocal F
        (localEOWRealLinearKernelPushforwardCLM ys hli
          (translateSchwartz a φ))
        (localEOWChart x0 ys w) =
      realMollifyLocal F
        (localEOWRealLinearKernelPushforwardCLM ys hli φ)
        (localEOWChart x0 ys (w - realEmbed a))
```

The first theorem is just the checked Jacobian-normalized
`realMollifyLocal_localEOWRealLinearKernelPushforwardCLM` plus
`localEOWChart_add_realEmbed`.  The second theorem changes variables
`u ↦ u + a` in the chart-coordinate integral.  This is the exact side-branch
identity needed by fixed-window uniqueness to prove covariance of the
regularized family.  It avoids the invalid shortcut
`localEOWChart (w - realEmbed a) = localEOWChart w - realEmbed a`; the actual
original-edge displacement remains `localEOWRealLinearPart ys a`.

The next support-radius facts are also Lean-ready:

```lean
theorem KernelSupportWithin.translateSchwartz
    (a : Fin m -> ℝ) {ψ : SchwartzMap (Fin m -> ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    KernelSupportWithin (SCV.translateSchwartz a ψ) (r + ‖a‖)

theorem KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_translateSchwartz
    (ys : Fin m -> Fin m -> ℝ) (hli : LinearIndependent ℝ ys)
    (a : Fin m -> ℝ) {φ : SchwartzMap (Fin m -> ℝ) ℂ} {r : ℝ}
    (hφ : KernelSupportWithin φ r) :
    KernelSupportWithin
      (SCV.localEOWRealLinearKernelPushforwardCLM ys hli
        (SCV.translateSchwartz a φ))
      (‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * (r + ‖a‖))
```

The fixed-radius covariance statement may still assume
`KernelSupportWithin (localEOWRealLinearKernelPushforwardCLM ys hli φ) rψ`
and
`KernelSupportWithin
  (localEOWRealLinearKernelPushforwardCLM ys hli (translateSchwartz a φ)) rψ`
when it wants to stay inside one fixed window.  The translated-radius theorem
is for choosing a larger support window honestly; it is not a license to reuse
the old radius after translation.

Important route correction: the local fixed-window family alone does not
construct a globally translation-covariant product kernel.  A complex-chart
cutoff extension of `(φ, ψ) ↦ ∫ z, G ψ z * φ z` would generally destroy
`ProductKernelRealTranslationCovariantGlobal`.  Thus the checked global
recovery theorem can only be used with a genuinely global covariant `K`; the
pure-SCV local theorem instead uses the local descent package below.  The
shifted-overlap covariance lemma is already checked and is the pointwise input
for `ProductKernelRealTranslationCovariantLocal`.  It lives immediately after
`regularizedLocalEOW_family_from_fixedWindow` in
`SCV/LocalDistributionalEOW.lean` and uses the same fixed-window hypothesis
prefix as `regularizedLocalEOW_family_add` / `regularizedLocalEOW_family_smul`.
The kernel-specific tail is:

```lean
lemma regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap
    {m : ℕ} {rψ ρ r δ : ℝ}
    -- same fixed-window hypotheses as
    -- `regularizedLocalEOW_family_from_fixedWindow`, ending with `hminus`
    (hm : 0 < m)
    (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m -> ℝ) ℂ)
    (a : Fin m -> ℝ)
    (hφ :
      KernelSupportWithin
        (localEOWRealLinearKernelPushforwardCLM ys hli φ) rψ)
    (hφa :
      KernelSupportWithin
        (localEOWRealLinearKernelPushforwardCLM ys hli
          (SCV.translateSchwartz a φ)) rψ)
    (hpos_overlap :
      ∃ z0,
        z0 ∈ localEOWShiftedWindow (m := m) δ a ∧
        (∀ j, 0 < (z0 j).im)) :
    let G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ :=
      fun ψ =>
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
    ∀ w,
      w ∈ localEOWShiftedWindow (m := m) δ a ->
        G (localEOWRealLinearKernelPushforwardCLM ys hli
            (SCV.translateSchwartz a φ)) w =
          G (localEOWRealLinearKernelPushforwardCLM ys hli φ)
            (w - realEmbed a)
```

The support hypotheses are intentionally duplicated.  If the caller wants to
derive the translated-kernel hypothesis from a smaller chart-coordinate radius,
it should use
`KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_translateSchwartz`
before calling this theorem.  The covariance theorem itself should not pretend
that translating the kernel preserves the old fixed radius.

Proof plan with exact checked API:

1. Set
   `V = localEOWShiftedWindow (m := m) δ a`,
   `ψ0 = localEOWRealLinearKernelPushforwardCLM ys hli φ`, and
   `ψa = localEOWRealLinearKernelPushforwardCLM ys hli
     (SCV.translateSchwartz a φ)`.
2. Obtain `hfamily` by calling
   `regularizedLocalEOW_family_from_fixedWindow` with the fixed-window data.
3. The left function `fun w => G ψa w` is differentiable on `V` by restricting
   `hfamily.1 ψa hφa` from the whole ball, using
   `localEOWShiftedWindow_mem_left`.
4. The right function `fun w => G ψ0 (w - realEmbed a)` is differentiable on
   `V` by composing `hfamily.1 ψ0 hφ` with
   `fun w => w - realEmbed a`, using
   `localEOWShiftedWindow_mem_shift`.
5. Convert both differentiability facts to `AnalyticOnNhd` on `V` with
   `differentiableOn_analyticAt` and `isOpen_localEOWShiftedWindow`; use
   `isPreconnected_localEOWShiftedWindow` for the identity theorem.
6. On a positive-imaginary neighborhood of the supplied `z0`, use
   `hfamily.2.1 ψa hφa` at `w` and
   `hfamily.2.1 ψ0 hφ` at `w - realEmbed a`.  The imaginary parts are
   unchanged by subtracting `realEmbed a`.
7. The middle equality on that seed is exactly
   `realMollifyLocal_localEOWChart_translate_kernelPushforwardCLM`
   applied to `Fplus`.
8. Apply `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on `V`.

This is a local pointwise covariance theorem.  It is useful for chart
consistency and is the analytic input to
`regularizedLocalEOW_pairingCLM_localCovariant`, but it is not by itself
`ProductKernelRealTranslationCovariantGlobal K`.

Checked usability helper for the covariance theorem:

```lean
theorem exists_positive_imag_mem_localEOWShiftedWindow_of_norm_lt
    (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ)
    {a : Fin m -> ℝ} (ha : ‖a‖ < δ / 4) :
    ∃ z0 : ComplexChartSpace m,
      z0 ∈ localEOWShiftedWindow (m := m) δ a ∧
      (∀ j, 0 < (z0 j).im)
```

Checked proof: take `z0 j = (δ / 8 : ℂ) * Complex.I`.  Then
`‖z0‖ = δ / 8 < δ / 2`, and
`‖z0 - realEmbed a‖ ≤ ‖z0‖ + ‖realEmbed a‖ ≤ δ / 8 + ‖a‖ < δ / 2`
using `norm_realEmbed_le`.  This removes the ad hoc `hpos_overlap`
hypothesis whenever the real shift is small relative to the fixed Rudin
window, which is exactly the regime used by compactly supported local
mollifiers.

The older schematic
`regularizedEnvelope_productKernel_representation_from_family` is retired.
It compressed three different mathematical steps into one statement: mixed
Schwartz CLM construction, local translation descent, and holomorphic
regularity.  The active route is the four-theorem local package above:
construct the cutoff-localized mixed CLM, prove local covariance, descend on
supported product tests, and then run the local recovery consumer.  Do not
restore the compressed schematic as a Lean target.

lemma regularizedEnvelope_deltaLimit_agreesOnWedges
    {m : ℕ} {ι : Type*} {l : Filter ι}
    (Ucore : Set (Fin m -> ℂ))
    (U0 : Set (Fin m -> ℂ))
    (G : SchwartzMap (Fin m -> ℝ) ℂ ->
      (Fin m -> ℂ) -> ℂ)
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (DplusSmall DminusSmall : Set (Fin m -> ℂ))
    (H : (Fin m -> ℂ) -> ℂ)
    (r : ℝ)
    (hH_holo : DifferentiableOn ℂ H U0)
    (hH_rep :
      ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
        KernelSupportWithin ψ r ->
        ∀ z ∈ Ucore,
          G ψ z = ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t)
    (ψι : ι -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hψι_support : ∀ᶠ i in l, KernelSupportWithin (ψι i) r)
    (hG_plus :
      ∀ᶠ i in l, ∀ z ∈ Ucore ∩ DplusSmall,
        G (ψι i) z = realMollifyLocal Fplus (ψι i) z)
    (hG_minus :
      ∀ᶠ i in l, ∀ z ∈ Ucore ∩ DminusSmall,
        G (ψι i) z = realMollifyLocal Fminus (ψι i) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun i => realMollifyLocal Fplus (ψι i) z) l (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun i => realMollifyLocal Fminus (ψι i) z) l (nhds (Fminus z)))
    :
    (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
    (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z)

lemma chartDistributionalEOW_local_envelope
    {m : ℕ}
    (Ωplus Ωminus : Set (Fin m -> ℂ))
    (E C : Set (Fin m -> ℝ))
    (x0 : Fin m -> ℝ) (hx0 : x0 ∈ E)
    (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    -- exactly the `hlocal_wedge`, `hslow_plus`, `hslow_minus`,
    -- `hplus_bv`, and `hminus_bv` hypotheses of
    -- `SCV.local_distributional_edge_of_the_wedge_envelope`, specialized to
    -- compact real boxes around `x0` and then transported by
    -- `localEOWChart x0 ys`
    :
    ∃ (Ux0 Ux0plus Ux0minus : Set (Fin m -> ℂ))
      (Hx0 : (Fin m -> ℂ) -> ℂ),
      IsOpen Ux0 ∧
      IsOpen Ux0plus ∧
      IsOpen Ux0minus ∧
      Ux0plus ⊆ Ux0 ∩ Ωplus ∧
      Ux0minus ⊆ Ux0 ∩ Ωminus ∧
      realEmbed x0 ∈ Ux0 ∧
      DifferentiableOn ℂ Hx0 Ux0 ∧
      (∀ z ∈ Ux0plus, Hx0 z = Fplus z) ∧
      (∀ z ∈ Ux0minus, Hx0 z = Fminus z)
```

The displayed `regularizedEnvelope_deltaLimit_agreesOnWedges` surface must not
be implemented by adding a free `hkernel_limit` assumption.  That would hide the
main delta-limit step.  The checked implementation split in
`SCV/DistributionalEOWKernelRecovery.lean` is now:

1. prove the shrinking-support geometry for real translates inside an open
   chart domain;
2. prove local compact-support integrability of
   `t ↦ H (z + realEmbed t) * ψ t`;
3. prove the difference-integral identity from the product-kernel
   representation, compact support, local continuity/integrability, and
   normalization;
4. prove the approximate-identity estimate once the kernel-recovery expression
   has already been rewritten as a difference integral;
5. apply limit uniqueness to identify the recovered envelope with the plus and
   minus wedge functions.

This is not a wrapper chain: item 2 is the compact-support integrability
bookkeeping, item 3 is the normalization/integral-subtraction identity, and
item 4 is the actual epsilon estimate.

```lean
lemma eventually_translate_mem_open_of_shrinking_support
    {m : ℕ}
    (Ucore U0 : Set (ComplexChartSpace m))
    (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore, ∀ ρ > 0,
      ∀ᶠ n in atTop,
        ∀ t ∈ tsupport (ψn n : (Fin m -> ℝ) -> ℂ),
          z + realEmbed t ∈ U0 ∧ ‖realEmbed t‖ < ρ

lemma regularizedEnvelope_kernelLimit_from_difference_integral
    {m : ℕ}
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m -> ℂ)
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hdiff :
      ∀ z ∈ Ucore,
        ∀ᶠ n in atTop,
          G (ψn n) z - H z =
            ∫ t : Fin m -> ℝ,
              (H (z + realEmbed t) - H z) * ψn n t)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      Tendsto (fun n => G (ψn n) z) atTop (nhds (H z))

lemma regularizedEnvelope_difference_integral_identity_eventually
    {m : ℕ}
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m -> ℂ)
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hH_rep :
      ∀ n, ∀ z ∈ Ucore,
        G (ψn n) z =
          ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψn n t)
    (hψ_norm : ∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      ∀ᶠ n in atTop,
        G (ψn n) z - H z =
          ∫ t : Fin m -> ℝ,
            (H (z + realEmbed t) - H z) * ψn n t

lemma regularizedEnvelope_kernelLimit_from_representation
    {m : ℕ}
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m -> ℂ)
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hH_rep :
      ∀ n, ∀ z ∈ Ucore,
        G (ψn n) z =
          ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψn n t)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      Tendsto (fun n => G (ψn n) z) atTop (nhds (H z))

lemma regularizedEnvelope_deltaLimit_agreesOnWedges
    {m : ℕ}
    (Ucore : Set (ComplexChartSpace m))
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    (Fplus Fminus H : ComplexChartSpace m -> ℂ)
    (DplusSmall DminusSmall : Set (ComplexChartSpace m))
    (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DplusSmall,
        G (ψn n) z = realMollifyLocal Fplus (ψn n) z)
    (hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DminusSmall,
        G (ψn n) z = realMollifyLocal Fminus (ψn n) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
          atTop (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
          atTop (nhds (Fminus z)))
    (hkernel_limit :
      ∀ z ∈ Ucore, Tendsto (fun n => G (ψn n) z) atTop (nhds (H z))) :
    (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
    (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z)
```

Lean transcript for `eventually_translate_mem_open_of_shrinking_support`:
fix `z ∈ Ucore` and `ρ > 0`.  Since `z ∈ U0` and `U0` is open, choose
`η > 0` with `Metric.ball z η ⊆ U0`.  Choose `N` so that
`1 / (N + 1) < min η ρ`.  If `n ≥ N` and
`t ∈ tsupport (ψn n)`, then `hψ_support n` gives
`‖t‖ ≤ 1 / (n + 1)`.  The checked `norm_realEmbed_le` gives
`‖realEmbed t‖ ≤ ‖t‖`, hence
`‖realEmbed t‖ < ρ` and
`dist (z + realEmbed t) z < η`; therefore `z + realEmbed t ∈ U0`.

Lean transcript for `regularizedEnvelope_kernelLimit_from_difference_integral`:
fix `z ∈ Ucore`.  From `hH_cont z (hcore_U0 hz)` get a neighborhood radius
`δ` such that `w ∈ U0` and `dist w z < δ` imply
`dist (H w) (H z) < ε / 2`.  Apply
`eventually_translate_mem_open_of_shrinking_support` with `ρ = δ`.  For all
large `n`, use `hdiff n z hz` and estimate

```lean
‖∫ t, (H (z + realEmbed t) - H z) * ψn n t‖
  ≤ ∫ t, ‖H (z + realEmbed t) - H z‖ * ‖ψn n t‖
  ≤ (ε / 2) * ∫ t, ‖ψn n t‖
  = ε / 2
  < ε
```

The last equality is `integral_norm_eq_one_of_real_nonneg_normalized`.
The pointwise zero outside `tsupport (ψn n)` is supplied by
`image_eq_zero_of_notMem_tsupport`, so no global boundedness of `H` is needed.

Lean transcript for `regularizedEnvelope_difference_integral_identity_eventually`: fix
`z ∈ Ucore`.  Use `eventually_translate_mem_open_of_shrinking_support` to
restrict to all large `n`, so the translated support
`z + realEmbed (tsupport (ψn n))` lies inside `U0`.  For such `n`, starting
from `hH_rep n z hz`, subtract `H z` and rewrite
`H z` as

```lean
∫ t : Fin m -> ℝ, H z * ψn n t
```

using `hψ_norm n` and `MeasureTheory.integral_const_mul`.  The only non-formal
obligation is integrability of
`t ↦ H (z + realEmbed t) * ψn n t` and
`t ↦ H z * ψn n t`.  It is supplied by compact support of `ψn n`, zero outside
`tsupport`, the eventual translated-support containment in `U0`, and
continuity of `H` on the compact translated support.  Then
`integral_sub` and pointwise ring simplification give the displayed difference
integral.  This identity is now checked; do not replace it by an assumption in
the final representation theorem.

Lean transcript for `regularizedEnvelope_deltaLimit_agreesOnWedges`: for the
plus side, fix `z ∈ Ucore ∩ DplusSmall`.  The eventual identity `hG_plus`
converts the limit of `G (ψn n) z` to the limit of
`realMollifyLocal Fplus (ψn n) z`; uniqueness of limits in `ℂ` gives
`H z = Fplus z`.  The minus side is identical.  This second lemma is only the
limit-uniqueness wrapper; the mathematical content is the preceding
kernel-limit theorem.  This wrapper is now checked too, with the explicit
definition

```lean
noncomputable def realMollifyLocal
    (F : ComplexChartSpace m -> ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
    ComplexChartSpace m -> ℂ :=
  fun z => ∫ t : Fin m -> ℝ, F (z + realEmbed t) * ψ t
```

Checked final chart-envelope assembly:

```lean
theorem regularizedEnvelope_chartEnvelope_from_productKernel
    {m : ℕ} {r : ℝ}
    (hm : 0 < m) (hr : 0 < r)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    (Ucore U0 DplusSmall DminusSmall : Set (ComplexChartSpace m))
    (Fplus Fminus : ComplexChartSpace m -> ℂ)
    (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hUcore_open : IsOpen Ucore)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hmargin_r :
      ∀ z ∈ Ucore, ∀ t : Fin m -> ℝ, ‖t‖ ≤ r ->
        z + realEmbed t ∈ U0)
    (hcov : ProductKernelRealTranslationCovariantGlobal K)
    (hG_holo :
      ∀ ψ, KernelSupportWithin ψ r -> DifferentiableOn ℂ (G ψ) U0)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
        KernelSupportWithin ψ r ->
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, G ψ z * φ z)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1)
    (hψ_support_shrink :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ)))
    (hψ_support_r : ∀ n, KernelSupportWithin (ψn n) r)
    (hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DplusSmall,
        G (ψn n) z = realMollifyLocal Fplus (ψn n) z)
    (hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DminusSmall,
        G (ψn n) z = realMollifyLocal Fminus (ψn n) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
          atTop (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
          atTop (nhds (Fminus z))) :
    ∃ H : ComplexChartSpace m -> ℂ,
      DifferentiableOn ℂ H U0 ∧
      ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
        RepresentsDistributionOnComplexDomain Hdist H U0 ∧
        (∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
          K (schwartzTensorProduct₂ φ ψ) =
            Hdist (realConvolutionTest φ ψ)) ∧
        (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
        (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z)
```

Proof transcript: first apply
`regularizedEnvelope_holomorphicDistribution_from_productKernel` to obtain
`H`, holomorphy of `H`, a representative distribution `Hdist`, and the descent
identity.  For each `n`, apply the checked
`regularizedEnvelope_pointwiseRepresentation_of_productKernel` with
`hψ_support_r n`, `hG_holo (ψn n) (hψ_support_r n)`, `hH_holo`, `hRep`,
`hdesc`, and the real-translation core margin `hmargin_r`.  This gives

```lean
G (ψn n) z = ∫ t, H (z + realEmbed t) * ψn n t
```

on `Ucore`.  Apply
`regularizedEnvelope_kernelLimit_from_representation`, using
`hH_holo.continuousOn`, to get `G (ψn n) z -> H z` on `Ucore`.  Apply
`regularizedEnvelope_deltaLimit_agreesOnWedges` to identify the same `H` with
`Fplus` and `Fminus` on the shrunken wedge pieces.  There is no longer a free
`hkernel_limit` or pointwise-representation supplier in the final chart
assembly.

Next implementation target: build the exact regularized-family package that
feeds this checked chart assembly.  This is the remaining Streater-Wightman
Theorem 2-16 content before `SCV.local_distributional_edge_of_the_wedge_envelope`
can be stated in production Lean.  It must produce the actual `K` and `G`
objects consumed by `regularizedEnvelope_chartEnvelope_from_productKernel`;
it must not add a record that merely assumes boundary pairings or assumes the
product-kernel representation.

Lean-facing subtheorems for the next file
`SCV/LocalDistributionalEOW.lean`:

```lean
theorem localRealMollifySide_holomorphicOn_of_translate_margin
    {m : ℕ}
    (F : ComplexChartSpace m -> ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (Ω D : Set (ComplexChartSpace m))
    (hΩ_open : IsOpen Ω)
    (hD_open : IsOpen D)
    (hF_holo : DifferentiableOn ℂ F Ω)
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ))
    (hmargin :
      ∀ z ∈ D, ∀ t ∈ tsupport (ψ : (Fin m -> ℝ) -> ℂ),
        z + realEmbed t ∈ Ω) :
    DifferentiableOn ℂ (realMollifyLocal F ψ) D

theorem regularizedBoundaryValue_continuousOn
    {m : ℕ}
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (E : Set (Fin m -> ℝ))
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ)) :
    ContinuousOn (fun x : Fin m -> ℝ => T (translateSchwartz (-x) ψ)) E

theorem realMollifyLocal_eq_sliceIntegral_translate
    {m : ℕ}
    (F : ComplexChartSpace m -> ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (w : ComplexChartSpace m) :
    realMollifyLocal F ψ w =
      ∫ x : Fin m -> ℝ,
        F (fun i => (x i : ℂ) + ((w i).im : ℂ) * Complex.I) *
          translateSchwartz (fun i => - (w i).re) ψ x

theorem realMollifyLocal_eq_sliceFunctional
    {m : ℕ}
    (F : ComplexChartSpace m -> ℂ)
    (Tseq : (Fin m -> ℝ) -> SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (w : ComplexChartSpace m)
    (hTseq_eval :
      ∀ (y : Fin m -> ℝ) (φ : SchwartzMap (Fin m -> ℝ) ℂ),
        Tseq y φ =
          ∫ x : Fin m -> ℝ,
            F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) * φ x) :
    realMollifyLocal F ψ w =
      Tseq (fun i => (w i).im)
        (translateSchwartz (fun i => - (w i).re) ψ)

theorem exists_cutoffSliceIntegral_clm_of_continuousOn
    {m : ℕ}
    (F : ComplexChartSpace m -> ℂ)
    (χ : SchwartzMap (Fin m -> ℝ) ℂ)
    (Ω : Set (ComplexChartSpace m))
    (y : Fin m -> ℝ)
    (hΩ_open : IsOpen Ω)
    (hF_cont : ContinuousOn F Ω)
    (hχ_compact : HasCompactSupport (χ : (Fin m -> ℝ) -> ℂ))
    (hmargin :
      ∀ x ∈ tsupport (χ : (Fin m -> ℝ) -> ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ω) :
    ∃ T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ,
      ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
        T φ = ∫ x : Fin m -> ℝ,
          (χ x * F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) *
            φ x

theorem realMollifyLocal_eq_cutoffSliceCLM
    {m : ℕ}
    (F : ComplexChartSpace m -> ℂ)
    (χ ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (w : ComplexChartSpace m)
    (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
    (hχ_one :
      ∀ x ∈ tsupport
          ((translateSchwartz (fun i => - (w i).re) ψ :
            SchwartzMap (Fin m -> ℝ) ℂ) : (Fin m -> ℝ) -> ℂ),
        χ x = 1)
    (hT :
      ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
        T φ = ∫ x : Fin m -> ℝ,
          (χ x * F (fun i => (x i : ℂ) + ((w i).im : ℂ) * Complex.I)) *
            φ x) :
    realMollifyLocal F ψ w =
      T (translateSchwartz (fun i => - (w i).re) ψ)

theorem tendsto_cutoffSliceCLM_of_boundaryValue
    {m : ℕ}
    {C : Set (Fin m -> ℝ)}
    (F : ComplexChartSpace m -> ℂ)
    (χ : SchwartzMap (Fin m -> ℝ) ℂ)
    (Traw : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
    (Tseq : (Fin m -> ℝ) -> SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
    (hTseq :
      ∀ (y : Fin m -> ℝ) (φ : SchwartzMap (Fin m -> ℝ) ℂ),
        Tseq y φ = ∫ x : Fin m -> ℝ,
          (χ x * F (fun i =>
            (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) * φ x)
    (hbv :
      ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
        Tendsto
          (fun y : Fin m -> ℝ => ∫ x : Fin m -> ℝ,
            F (fun i =>
              (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 C)
          (nhds (Traw φ))) :
    ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
      Tendsto (fun y : Fin m -> ℝ => Tseq y φ) (nhdsWithin 0 C)
        (nhds (Traw ((SchwartzMap.smulLeftCLM ℂ
          (χ : (Fin m -> ℝ) -> ℂ)) φ)))

theorem exists_cutoffSliceCLM_family_of_boundaryValue
    {m : ℕ}
    {C : Set (Fin m -> ℝ)}
    (F : ComplexChartSpace m -> ℂ)
    (χ : SchwartzMap (Fin m -> ℝ) ℂ)
    (Ω : Set (ComplexChartSpace m))
    (Traw : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
    (hΩ_open : IsOpen Ω)
    (hF_cont : ContinuousOn F Ω)
    (hχ_compact : HasCompactSupport (χ : (Fin m -> ℝ) -> ℂ))
    (hmargin :
      ∀ y ∈ C, ∀ x ∈ tsupport (χ : (Fin m -> ℝ) -> ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ω)
    (hbv :
      ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
        Tendsto
          (fun y : Fin m -> ℝ => ∫ x : Fin m -> ℝ,
            F (fun i =>
              (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 C)
          (nhds (Traw φ))) :
    ∃ Tseq : (Fin m -> ℝ) -> SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ,
      (∀ y ∈ C, ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
        Tseq y φ = ∫ x : Fin m -> ℝ,
          (χ x * F (fun i =>
            (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) * φ x) ∧
      (∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
        Tendsto (fun y : Fin m -> ℝ => Tseq y φ) (nhdsWithin 0 C)
          (nhds (Traw ((SchwartzMap.smulLeftCLM ℂ
            (χ : (Fin m -> ℝ) -> ℂ)) φ))))

theorem tendsto_mollified_boundary_of_clm
    {m : ℕ}
    {C : Set (Fin m -> ℝ)}
    {Tseq : (Fin m -> ℝ) ->
      SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ}
    {T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ}
    (hT :
      ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
        Tendsto (fun y => Tseq y f) (nhdsWithin 0 C) (nhds (T f)))
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ))
    (x0 : Fin m -> ℝ) :
    Tendsto
      (fun w : ComplexChartSpace m =>
        Tseq (fun i => (w i).im)
          (translateSchwartz (fun i => - (w i).re) ψ))
      (nhdsWithin (realEmbed x0) (TubeDomain C))
      (nhds (T (translateSchwartz (fun i => - x0 i) ψ)))

theorem localRealMollify_commonContinuousBoundary_of_clm
    {m : ℕ}
    (Ωplus Ωminus : Set (ComplexChartSpace m))
    {Cplus Cminus : Set (Fin m -> ℝ)}
    (Fplus Fminus : ComplexChartSpace m -> ℂ)
    (Tplus Tminus :
      (Fin m -> ℝ) -> SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (B : Set (Fin m -> ℝ))
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ))
    (hΩplus_sub : Ωplus ⊆ TubeDomain Cplus)
    (hΩminus_sub : Ωminus ⊆ TubeDomain Cminus)
    (hplus_eval :
      ∀ w ∈ Ωplus,
        realMollifyLocal Fplus ψ w =
          Tplus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ w ∈ Ωminus,
        realMollifyLocal Fminus ψ w =
          Tminus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f))) :
    ContinuousOn (fun x : Fin m -> ℝ =>
      Tchart (translateSchwartz (-x) ψ)) B ∧
    (∀ x ∈ B,
      Tendsto (realMollifyLocal Fplus ψ)
        (nhdsWithin (realEmbed x) Ωplus)
        (nhds (Tchart (translateSchwartz (-x) ψ)))) ∧
    (∀ x ∈ B,
      Tendsto (realMollifyLocal Fminus ψ)
        (nhdsWithin (realEmbed x) Ωminus)
        (nhds (Tchart (translateSchwartz (-x) ψ))))

theorem regularizedLocalEOW_window_from_continuousEOW
    {m : ℕ} {r : ℝ}
    (hm : 0 < m) (hr : 0 < r)
    (Ωplus Ωminus U0 DplusSmall DminusSmall : Set (ComplexChartSpace m))
    (B0 : Set (Fin m -> ℝ))
    (Fplus Fminus : ComplexChartSpace m -> ℂ)
    (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
    -- local continuous EOW hypotheses and the previous regularization theorem
    :
    ∃ G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ,
      (∀ ψ, KernelSupportWithin ψ r ->
        DifferentiableOn ℂ (G ψ) U0) ∧
      (∀ ψ, KernelSupportWithin ψ r ->
        ∀ z ∈ U0 ∩ DplusSmall,
          G ψ z = realMollifyLocal Fplus ψ z) ∧
      (∀ ψ, KernelSupportWithin ψ r ->
        ∀ z ∈ U0 ∩ DminusSmall,
          G ψ z = realMollifyLocal Fminus ψ z) ∧
      (∀ ψ a,
        KernelSupportWithin ψ r ->
        KernelSupportWithin (translateSchwartz a ψ) r ->
        -- whenever both real-translated points remain in U0
        ∀ z ∈ U0, z - realEmbed a ∈ U0 ->
          G (translateSchwartz a ψ) z = G ψ (z - realEmbed a))

theorem regularizedEnvelope_productBilinear_from_localEOW_window
    {m : ℕ} {r : ℝ}
    (U0 : Set (ComplexChartSpace m))
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    -- explicit Cauchy-polydisc formula for G, slow-growth bounds,
    -- fixed support cutoff χr = 1 on closedBall 0 r
    :
    ∃ B : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
        (SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
        KernelSupportWithin ψ r ->
          B φ ψ = ∫ z : ComplexChartSpace m, G ψ z * φ z

theorem regularizedEnvelope_realTranslation_integral_from_uniqueness
    {m : ℕ} {r : ℝ}
    (U0 : Set (ComplexChartSpace m))
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    -- uniqueness output of local continuous EOW and real-translation
    -- support-margin hypotheses
    :
    ∀ (a : Fin m -> ℝ)
      (φ : SchwartzMap (ComplexChartSpace m) ℂ)
      (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
      SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
      SupportsInOpen
        (complexTranslateSchwartz a φ : ComplexChartSpace m -> ℂ) U0 ->
      KernelSupportWithin ψ r ->
      KernelSupportWithin (translateSchwartz a ψ) r ->
        (∫ z : ComplexChartSpace m,
            G ψ z * complexTranslateSchwartz a φ z) =
          ∫ z : ComplexChartSpace m,
            G (translateSchwartz a ψ) z * φ z

theorem regularizedLocalEOW_productKernel_package
    {m : ℕ} {r : ℝ}
    (hm : 0 < m) (hr : 0 < r)
    (Ucore U0 DplusSmall DminusSmall : Set (ComplexChartSpace m))
    (Fplus Fminus : ComplexChartSpace m -> ℂ)
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
    (hψ_support_r : ∀ n, KernelSupportWithin (ψn n) r)
    -- output of the local EOW window theorem:
    (hG_holo_window :
      ∀ ψ, KernelSupportWithin ψ r -> DifferentiableOn ℂ (G ψ) U0)
    (hG_plus_window :
      ∀ ψ, KernelSupportWithin ψ r ->
        ∀ z ∈ Ucore ∩ DplusSmall,
          G ψ z = realMollifyLocal Fplus ψ z)
    (hG_minus_window :
      ∀ ψ, KernelSupportWithin ψ r ->
        ∀ z ∈ Ucore ∩ DminusSmall,
          G ψ z = realMollifyLocal Fminus ψ z)
    (hB :
      ∃ B : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
          (SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ),
        ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
          SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
          KernelSupportWithin ψ r ->
            B φ ψ = ∫ z : ComplexChartSpace m, G ψ z * φ z)
    (hcov_window :
      ∀ (a : Fin m -> ℝ)
        (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
        SupportsInOpen
          (complexTranslateSchwartz a φ : ComplexChartSpace m -> ℂ) U0 ->
        KernelSupportWithin ψ r ->
        KernelSupportWithin (translateSchwartz a ψ) r ->
          (∫ z : ComplexChartSpace m,
              G ψ z * complexTranslateSchwartz a φ z) =
            ∫ z : ComplexChartSpace m,
              G (translateSchwartz a ψ) z * φ z)
    :
    ∃ K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ,
      ProductKernelRealTranslationCovariantGlobal K ∧
      (∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
        KernelSupportWithin ψ r ->
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, G ψ z * φ z) ∧
      (∀ n, ∀ z ∈ Ucore ∩ DplusSmall,
        G (ψn n) z = realMollifyLocal Fplus (ψn n) z) ∧
      (∀ n, ∀ z ∈ Ucore ∩ DminusSmall,
        G (ψn n) z = realMollifyLocal Fminus (ψn n) z)
```

In production this theorem should either take a fixed approximate-identity
sequence satisfying the four checked support/normalization hypotheses, as
displayed above, or obtain one from
`exists_realConvolutionTest_approxIdentity (m := m) hr` and return it together
with `K` and `G`.  The important interface is exact: after this theorem, the
call to `regularizedEnvelope_chartEnvelope_from_productKernel` is mechanical;
the two `∀ n` wedge identities feed its eventual hypotheses by
`Filter.Eventually.of_forall`.

Proof transcript for the next target:

1. `localRealMollifySide_holomorphicOn_of_translate_margin` is now checked in
   `SCV/LocalDistributionalEOW.lean`.  It adapts the checked
   differentiation-under-the-integral proof of
   `differentiableOn_realMollify_tubeDomain` and replaces tube-domain
   imaginary-part invariance with the explicit support-margin hypothesis
   `z + realEmbed t ∈ Ω` on `tsupport ψ`.
2. Prove `regularizedBoundaryValue_continuousOn` directly from
   `continuous_apply_translateSchwartz_of_isCompactSupport` and continuity of
   `x ↦ -x`.  Lean proof:

   ```lean
   have hcont :
       Continuous (fun t : Fin m -> ℝ => T (translateSchwartz t ψ)) :=
     continuous_apply_translateSchwartz_of_isCompactSupport T ψ hψ_compact
   simpa [Function.comp_def] using (hcont.comp continuous_neg).continuousOn
   ```

   This theorem supplies only continuity of the candidate boundary function
   `bvψ x = T (translateSchwartz (-x) ψ)`; it does not by itself prove the
   plus/minus mollified sides converge to that function.
3. Prove `tendsto_mollified_boundary_of_clm` as the nonzero version of the
   existing checked theorem `tendsto_mollified_boundary_zero_of_clm_zero`.
   The proof uses the same maps
   `w ↦ im w` and `w ↦ -re w`; the first tends to `nhdsWithin 0 C` inside
   `TubeDomain C`, the second tends to `-x0`; then
   `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter` combines pointwise
   convergence of the slice functionals with convergence of the translated
   Schwartz test.
4. Prove the checked slice-to-mollifier bridge
   `realMollifyLocal_eq_sliceIntegral_translate` by translating the real
   integration variable by `re w`:

   ```lean
   let a : Fin m -> ℝ := fun i => (w i).re
   let f : (Fin m -> ℝ) -> ℂ := fun x =>
     F (fun i => (x i : ℂ) + ((w i).im : ℂ) * Complex.I) *
       translateSchwartz (fun i => - (w i).re) ψ x
   calc
     realMollifyLocal F ψ w
         = ∫ t, F (fun i =>
             ((t i + a i : ℝ) : ℂ) + ((w i).im : ℂ) * Complex.I) * ψ t := by
           -- pointwise coordinate algebra using `Complex.re_add_im`
           ...
     _ = ∫ t, f (t + a) := by
           -- `translateSchwartz (-re w) ψ (t + re w) = ψ t`
           ...
     _ = ∫ x, f x := MeasureTheory.integral_add_right_eq_self (μ := volume) f a
   ```

   The follow-up theorem `realMollifyLocal_eq_sliceFunctional` is then a direct
   rewrite by the slice-functional representation
   `Tseq y φ = ∫ x, F (x + i y) * φ x`.
5. Prove `localRealMollify_commonContinuousBoundary_of_clm` from the two
   checked ingredients above.  Lean proof shape:

   ```lean
   refine ⟨regularizedBoundaryValue_continuousOn Tchart ψ B hψ_compact, ?_, ?_⟩
   · intro x hx
     have h := tendsto_mollified_boundary_of_clm
       (C := Cplus) (Tseq := Tplus) (T := Tchart.restrictScalars ℝ)
       hplus_limit ψ hψ_compact x
     have hΩ := h.mono_left (nhdsWithin_mono _ hΩplus_sub)
     refine Tendsto.congr' ?_ hΩ
     filter_upwards [self_mem_nhdsWithin] with w hw
     exact (hplus_eval w hw).symm
   ```

   The minus side is identical.  This theorem is the precise
   Streater-Wightman regularization extraction: it proves common continuous
   boundary values for each compact real kernel once the slice CLMs have been
   constructed and shown to converge to the same chart distribution.
6. The fixed-kernel continuous-envelope bridge is now checked as
   `SCV.regularizedLocalEOW_fixedKernelEnvelope_from_clm`.  It applies the two
   holomorphy-margin lemmas to `realMollifyLocal Fplus ψ` and
   `realMollifyLocal Fminus ψ`, uses
   `SCV.localRealMollify_commonContinuousBoundary_of_clm` for the common
   boundary value
   `x ↦ Tchart (translateSchwartz (-x) ψ)`, and then calls
   `SCV.local_continuous_edge_of_the_wedge_envelope` on the shrunken local
   wedges `Dplus/Dminus`.  Its Lean proof is the following composition, with
   no hidden boundary assumption:

   ```lean
   have hψ_compact := KernelSupportWithin_hasCompactSupport hψ_support
   have hFplus_moll_holo :=
     localRealMollifySide_holomorphicOn_of_translate_margin
       Fplus ψ Ωplus Dplus hΩplus_open hDplus_open hFplus_diff
       hψ_compact hplus_margin
   have hFminus_moll_holo :=
     localRealMollifySide_holomorphicOn_of_translate_margin
       Fminus ψ Ωminus Dminus hΩminus_open hDminus_open hFminus_diff
       hψ_compact hminus_margin
   have hcommon :=
     localRealMollify_commonContinuousBoundary_of_clm
       Dplus Dminus Fplus Fminus Tplus Tminus Tchart ψ E hψ_compact
       hDplus_sub hDminus_sub hplus_eval hminus_eval
       hplus_limit hminus_limit
   exact
     local_continuous_edge_of_the_wedge_envelope hm
       Dplus Dminus E C hDplus_open hDminus_open hE_open hC_open
       hC_conv hC_ne hlocal_wedge
       (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
       hFplus_moll_holo hFminus_moll_holo
       (fun x => Tchart (translateSchwartz (-x) ψ))
       hcommon.1 hcommon.2.1 hcommon.2.2 x0 hx0
   ```

   This checked theorem is exactly the per-kernel input for the next family
   stage.  The next theorem may use it, but must not restate its conclusion as
   an assumption.
7. Pinned slice-CLM production theorem for the final
   `local_distributional_edge_of_the_wedge_envelope` assembly: construct the
   local slice CLMs `Tplus y` and `Tminus y` from the distributional
   boundary-value hypotheses.  The integral-interchange and slow-growth
   estimates are discharged inside the displayed theorem by the checked
   cutoff-slice CLM lemmas named in the transcript; downstream proofs must not
   assume the four conclusions directly.  The required production theorem
   must show:

   ```lean
   theorem sliceCLM_family_from_distributionalBoundary
       (Ωplus Ωminus : Set (ComplexChartSpace m))
       {Cplus Cminus : Set (Fin m -> ℝ)}
       (Fplus Fminus : ComplexChartSpace m -> ℂ)
       (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (E B0 B1 B2 : Set (Fin m -> ℝ))
       (hB0_sub_E : B0 ⊆ E) (hB1_sub_E : B1 ⊆ E)
       (hB2_sub_E : B2 ⊆ E)
       (χ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hχ_one_B1 : ∀ x ∈ B1, χ x = 1)
       (hχ_support_B2 :
         tsupport (χ : (Fin m -> ℝ) -> ℂ) ⊆ B2)
       (hψ_translate_B1 :
         ∀ w ∈ Ωplus ∪ Ωminus,
           tsupport
             (translateSchwartz (fun i => - (w i).re) ψ :
               (Fin m -> ℝ) -> ℂ) ⊆ B1)
       (hplus_slice_mem :
         ∀ y ∈ Cplus, ∀ x ∈ B2,
           (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) ∈ Ωplus)
       (hminus_slice_mem :
         ∀ y ∈ Cminus, ∀ x ∈ B2,
           (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) ∈ Ωminus)
       (hplus_bv_cutoff :
         ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
           Tendsto (fun y =>
             ∫ x : Fin m -> ℝ,
               Fplus (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) *
                 (SchwartzMap.smulLeftCLM ℂ
                   (χ : (Fin m -> ℝ) -> ℂ) φ) x)
             (nhdsWithin 0 Cplus) (nhds (Tchart φ)))
       (hminus_bv_cutoff :
         ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
           Tendsto (fun y =>
             ∫ x : Fin m -> ℝ,
               Fminus (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) *
                 (SchwartzMap.smulLeftCLM ℂ
                   (χ : (Fin m -> ℝ) -> ℂ) φ) x)
             (nhdsWithin 0 Cminus) (nhds (Tchart φ)))
       :
       ∃ Tplus Tminus :
           (Fin m -> ℝ) -> SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ,
         (∀ w ∈ Ωplus,
           realMollifyLocal Fplus ψ w =
             Tplus (fun i => (w i).im)
               (translateSchwartz (fun i => - (w i).re) ψ)) ∧
         (∀ w ∈ Ωminus,
           realMollifyLocal Fminus ψ w =
             Tminus (fun i => (w i).im)
               (translateSchwartz (fun i => - (w i).re) ψ)) ∧
         (∀ φ, Tendsto (fun y => Tplus y φ) (nhdsWithin 0 Cplus)
           (nhds ((Tchart.restrictScalars ℝ) φ))) ∧
         (∀ φ, Tendsto (fun y => Tminus y φ) (nhdsWithin 0 Cminus)
           (nhds ((Tchart.restrictScalars ℝ) φ)))
   ```

   This theorem is not optional and must not be replaced by a wrapper that
   assumes the four displayed conclusions.  The mathematical content is:
   a fixed local cutoff extends compactly supported slice tests to global
   Schwartz CLMs; the support margin makes this cutoff invisible on
   `translateSchwartz (-re w) ψ`; compact support gives finite local real
   integration; slow growth gives the domination needed near the edge; and the
   OS-II distributional BV hypothesis gives convergence on every compactly
   supported Schwartz test after chart pullback.

   The exact implementation transcript should be:

   1. Choose nested real edge sets
      `B0 ⋐ B1 ⋐ B2 ⋐ Echart` and a support radius `rψ` with
      `u + tsupport ψ ⊆ B1` for every `u ∈ B0`.  Equivalently, for
      `w` in the local plus/minus wedge with `re w ∈ B0`,
      `Function.support (translateSchwartz (fun i => - (w i).re) ψ) ⊆ B1`.
      This follows from `translateSchwartz_apply` and the already documented
      `BoxMargin B0 B1 rψ`.
   2. Choose a compactly supported smooth cutoff `χ` with `χ = 1` on `B1` and
      `tsupport χ ⊆ B2`.  In Lean this should be exposed as a multiplication
      CLM
      `cutoffSchwartzCLM χ : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ]
        SchwartzMap (Fin m -> ℝ) ℂ`
      together with:

      ```lean
      cutoffSchwartzCLM_apply
      cutoffSchwartzCLM_eq_self_of_support_subset_oneRegion
      cutoffSchwartzCLM_preserves_compact_support
      ```

      This is a genuine cutoff/multiplication theorem, not an LF-space wrapper.
   3. Define the local chart distribution as the cutoff extension
      `Tchart φ = Traw (cutoffSchwartzCLM χ φ)`.  This is why
      `hplus_limit` and `hminus_limit` may target `Tchart` on all Schwartz
      tests even though the original paper hypothesis is local on compactly
      supported tests in `E`.
   4. For each fixed `y`, set
      `gplus_y x = χ x * Fplus (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)`
      and similarly for the minus side.  Since `χ` has compact support and
      the local wedge hypotheses keep `x + i y` inside the holomorphy domain
      on `B2`, prove `Continuous gplus_y` and
      `∀ φ, Integrable (fun x => gplus_y x * φ x)`.  Then use the existing
      checked constructor
      `exists_integral_clm_of_continuous` from
      `SCV/DistributionalUniqueness.lean` to obtain

      ```lean
      Tplus y φ =
        ∫ x, (χ x * Fplus (fun i =>
          (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) * φ x
      Tminus y φ =
        ∫ x, (χ x * Fminus (fun i =>
          (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) * φ x
      ```

      as real-linear Schwartz CLMs.  This is now checked as
      `exists_cutoffSliceIntegral_clm_of_continuousOn`: outside `tsupport χ`
      the integrand is eventually zero, while on `tsupport χ` local continuity
      of `F` gives continuity of the slice; compactness of `tsupport χ` gives
      the integrability needed by `exists_integral_clm_of_continuous`.
   5. Prove the evaluation hypotheses for the chosen kernel `ψ`: on the support
      of `translateSchwartz (-re w) ψ`, the cutoff is `1`, so

      ```lean
      Tplus (im w) (translateSchwartz (-re w) ψ)
        = ∫ x, Fplus (x + i * im w) *
            translateSchwartz (-re w) ψ x
        = realMollifyLocal Fplus ψ w
      ```

      This is now checked as `realMollifyLocal_eq_cutoffSliceCLM`, using
      `realMollifyLocal_eq_sliceIntegral_translate` and the cutoff-one
      hypothesis on the translated kernel support.
   6. Prove pointwise convergence of the CLMs from the OS-II/SW distributional
      boundary-value hypothesis applied to the cutoff tests:

      ```lean
      Tplus y φ
        = ∫ x, Fplus (x + i y) * (cutoffSchwartzCLM χ φ) x
        --> Traw (cutoffSchwartzCLM χ φ)
        = Tchart φ
      ```

      and similarly on the minus side.  For the `T(f_x)` family needed by
      Streater-Wightman 2-16, the already checked
      `tendsto_translateSchwartz_nhds_of_isCompactSupport` supplies the
      bounded/continuous translated-test family in Schwartz topology; the
      Banach-Steinhaus payoff is already encapsulated in
      `tendsto_mollified_boundary_of_clm`.

      The cutoff-pullback part is now checked as
      `tendsto_cutoffSliceCLM_of_boundaryValue`.  Its proof applies the raw
      boundary-value hypothesis to
      `(SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ)) φ`, then rewrites
      the integrand by
      `SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth`.  Thus the
      remaining work is not Banach-Steinhaus or moving-test convergence; it is
      the local OS-II hypothesis plumbing that identifies the correct
      cutoff-extended `Traw` for the plus and minus sides.

   Paper-faithfulness check against Streater-Wightman Theorem 2-16: the paper
   regularizes by
   `F_f(x + i y) = ∫ dξ f(x - ξ) F(ξ + i y)` and observes that, as `y -> 0`
   through the cone, the regularized function has continuous boundary value
   `T(f_x)` uniformly for `x` in small compact subsets of the edge, because
   distributional convergence is uniform on bounded sets of test functions.
   The Lean route above is the same argument in local-chart form:
   `translateSchwartz (-x) ψ` is the `f_x` family, the checked continuity
   theorem proves `x ↦ T(f_x)` is continuous, and the next slice-CLM theorem
   must prove convergence for that bounded translated-kernel family from the
   original distributional BV hypothesis.  No step may replace this with a
   pre-assumed continuous common boundary value.
7. Apply `SCV.local_continuous_edge_of_the_wedge_envelope` to the two
   regularized sides.  The nested boxes and support radius must be chosen
   before `ψ`; this is why the output domain `U0` is independent of the
   smoothing kernel inside the fixed support window.
8. Prove linearity in `ψ` by applying uniqueness in the local continuous EOW
   theorem to `G (a • ψ1 + b • ψ2)` and
   `a • G ψ1 + b • G ψ2`; the two sides agree on both regularized wedge
   pieces by linearity of the real convolution integral and the common
   boundary value.
9. Prove real-translation covariance by applying the same uniqueness theorem
   to `G (translateSchwartz a ψ) z` and `G ψ (z - realEmbed a)` on the
   overlap where both points lie in `U0`; the plus/minus wedge identities
   reduce the claim to the checked translation formula for
   `realMollifyLocal`.
10. Do **not** extend the local pairing by a complex-chart cutoff and then
   claim `ProductKernelRealTranslationCovariantGlobal`.  That was the
   rejected route: the cutoff destroys global translation covariance.
11. For the pure-SCV local distributional EOW theorem, the recovery fork is
   now resolved in favor of a local descent theorem.  The OS-side option of
   sourcing a genuinely global covariant kernel from Wightman/OS translation
   invariance may later be useful for an OS-specific shortcut, but it cannot be
   the proof of the QFT-free theorem
   `SCV.local_distributional_edge_of_the_wedge_envelope`.
12. The local descent route keeps the cutoffs only as localization devices,
   never as a source of global covariance.  Fix radii
   `0 < Rcore < Rdesc < Rcov < Rcut < δ / 2` and chart-kernel radii
   `0 < r` and `0 < rη` with the concrete margins

   ```lean
   Rcore + r < Rdesc
   Rdesc + (r + rη) < Rcov
   2 * Rcov < δ / 4
   ```

   and set
   `Ucore = Metric.ball (0 : ComplexChartSpace m) Rcore`,
   `Udesc = Metric.ball (0 : ComplexChartSpace m) Rdesc`,
   `Ucov = Metric.ball (0 : ComplexChartSpace m) Rcov`, and
   `Ucut = Metric.ball (0 : ComplexChartSpace m) Rcut`.  The first two
   inequalities are exactly the support margins used by
   `realConvolutionTest_supportsInOpen_of_translate_margin`; the third makes
   the shifted-overlap seed automatic in every nonzero local covariance
   application.  Indeed, if `φ u ≠ 0`,
   `SupportsInOpen φ Ucov`, and
   `SupportsInOpen (complexTranslateSchwartz a φ) Ucov`, then
   `u ∈ Ucov` and `u - realEmbed a ∈ Ucov`, hence
   `‖a‖ ≤ ‖u‖ + ‖u - realEmbed a‖ < 2 * Rcov < δ / 4`; the documented
   helper `exists_positive_imag_mem_localEOWShiftedWindow_of_norm_lt` supplies
   the positive-imaginary seed required by
   `regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap`.

   The helper surfaces in this chart-kernel layer are now checked.  These are
   not wrappers: together they are exactly the functional-analytic content
   needed to turn the local family `Gchart` into one mixed Schwartz continuous
   linear functional.  The checked package includes the cutoff helpers, the
   full partial-evaluation CLM/apply/tensor/seminorm package, the compact
   original-family value-CLM bound, the SCV-local continuity-in-the-chart-
   variable theorem for partial evaluation, support-radius monotonicity,
   finite-seminorm transport through a continuous Schwartz CLM, and the
   chart-kernel value-CLM theorem
   `regularizedLocalEOW_chartKernelFamily_valueCLM`.  The next unimplemented
   surface is the varying-slice continuity theorem for the actual cutoff
   envelope integrand.

   ```lean
   theorem exists_complexChart_schwartz_cutoff_eq_one_on_closedBall
       {m : ℕ} {R Rlarge : ℝ} (hR : 0 < R) (hRlarge : R < Rlarge) :
       ∃ χ : SchwartzMap (ComplexChartSpace m) ℂ,
         (∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) R, χ z = 1) ∧
         tsupport (χ : ComplexChartSpace m -> ℂ) ⊆
           Metric.closedBall 0 Rlarge

   theorem SupportsInOpen.smulLeftCLM_eq_of_eq_one_on
       {m : ℕ} {U : Set (ComplexChartSpace m)}
       (χ : SchwartzMap (ComplexChartSpace m) ℂ)
       {φ : SchwartzMap (ComplexChartSpace m) ℂ}
       (hχ_one : ∀ z ∈ U, χ z = 1)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U) :
       SchwartzMap.smulLeftCLM ℂ (χ : ComplexChartSpace m -> ℂ) φ = φ

   def schwartzPartialEval₁CLM
       {m : ℕ} (z : ComplexChartSpace m) :
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ]
         SchwartzMap (Fin m -> ℝ) ℂ

   theorem schwartzPartialEval₁CLM_apply
       {m : ℕ} (z : ComplexChartSpace m)
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (t : Fin m -> ℝ) :
       schwartzPartialEval₁CLM z F t = F (z, t)

   theorem schwartzPartialEval₁CLM_tensorProduct₂
       {m : ℕ} (z : ComplexChartSpace m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       schwartzPartialEval₁CLM z (schwartzTensorProduct₂ φ ψ) =
         φ z • ψ

   theorem schwartzPartialEval₁CLM_compactSeminormBound
       {m : ℕ} (R : ℝ) (hR : 0 ≤ R)
       (s : Finset (ℕ × ℕ)) :
       ∃ s' : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
         ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) R,
         ∀ F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ,
           s.sup (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ)
               (schwartzPartialEval₁CLM z F) ≤
             C * s'.sup
               (schwartzSeminormFamily ℂ
                 (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) F

   theorem continuous_schwartzPartialEval₁CLM
       {m : ℕ}
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       Continuous (fun z : ComplexChartSpace m =>
         schwartzPartialEval₁CLM z F)

   theorem KernelSupportWithin.mono
       {m : ℕ} {ψ : SchwartzMap (Fin m -> ℝ) ℂ} {r R : ℝ}
       (hψ : KernelSupportWithin ψ r) (hrR : r ≤ R) :
       KernelSupportWithin ψ R

   theorem SchwartzMap.exists_schwartzCLM_finsetSeminormBound
       {m : ℕ}
       (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ]
             SchwartzMap (Fin m -> ℝ) ℂ)
       (s0 : Finset (ℕ × ℕ)) :
       ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
         ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
           s0.sup (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ) (T ψ) ≤
             C * s.sup (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ) ψ

   theorem regularizedLocalEOW_originalFamily_compactValueCLM
       -- copy the exact parameter block of the checked theorem
       -- `regularizedEnvelope_valueCLM_of_cutoff`:
       --   `{Cplus Cminus : Set (Fin m -> ℝ)} {rLarge ρ r δ : ℝ}`,
       --   `hm`, `Ωplus`, `Ωminus`, `Dplus`, `Dminus`, `E`,
       --   all openness hypotheses including `hE_open`,
       --   `Fplus`, `Fminus`, their differentiability hypotheses,
       --   closed support-margin hypotheses, `hDplus_sub`, `hDminus_sub`,
       --   `Tplus`, `Tminus`, `Tchart`, evaluation and limit hypotheses,
       --   `x0`, `ys`, `hδ`, `hδρ`, `hδsum`, `hE_mem`,
       --   `hplus`, `hminus`, and the original-edge cutoff
       --   `χψ` with `hχψ_support`.
       (Rcut : ℝ)
       (hRcut_window :
         Metric.closedBall (0 : ComplexChartSpace m) Rcut ⊆
           Metric.ball (0 : ComplexChartSpace m) (δ / 2)) :
       ∃ L : ComplexChartSpace m ->
           SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
         (∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
           ∀ η : SchwartzMap (Fin m -> ℝ) ℂ,
             L z η =
               localRudinEnvelope δ x0 ys
                 (fun w => realMollifyLocal Fplus
                   (SchwartzMap.smulLeftCLM ℂ
                     (χψ : (Fin m -> ℝ) -> ℂ) η) w)
                 (fun w => realMollifyLocal Fminus
                   (SchwartzMap.smulLeftCLM ℂ
                     (χψ : (Fin m -> ℝ) -> ℂ) η) w)
                 z) ∧
         ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
           ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
           ∀ η : SchwartzMap (Fin m -> ℝ) ℂ,
             ‖L z η‖ ≤
               C * s.sup (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ) η
   ```

   Proof transcripts for these helpers:

   * The complex-chart cutoff is checked as
     `exists_complexChart_schwartz_cutoff_eq_one_on_closedBall`.  It is the
     same `ContDiffBump` argument as
     `exists_schwartz_cutoff_eq_one_on_closedBall`, but with center
     `0 : ComplexChartSpace m`.
   * `SupportsInOpen.smulLeftCLM_eq_of_eq_one_on` is checked as the
     complex-chart analogue of
     `KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall`.
   * `schwartzPartialEval₁CLM z` is checked in the SCV layer, without
     importing the Wightman partial-evaluation file.  Define
     `g z : (Fin m -> ℝ) -> ComplexChartSpace m × (Fin m -> ℝ)` by
     `g z t = (z,t)` and set the CLM to
     `SchwartzMap.compCLM (𝕜 := ℂ) (g := g z) ...`.  The temperate-growth
     proof is exact: write `g z` as the pointwise sum of the constant map
     `fun _ => (z,0)` and the continuous linear inclusion
     `ContinuousLinearMap.inr ℝ (ComplexChartSpace m) (Fin m -> ℝ)`.  The
     reverse-growth witness is `(k,C) = (1,1)`, because the product norm gives
     `‖t‖ ≤ ‖(z,t)‖ ≤ 1 * (1 + ‖(z,t)‖)^1`.  Therefore no compact `z`
     hypothesis is needed for the definition.  The apply theorem is checked by
     definitional reduction (`rfl`), and the tensor-product theorem is checked
     by extensionality plus `schwartzTensorProduct₂_apply`.
   * The compact partial-evaluation seminorm bound is checked and stronger
     than the compact statement needs.  The proof adds the pure first-variable
     derivative lemmas to
     `SCV/SchwartzPartialEval.lean`:
     `iteratedFDeriv_partialEval₁_eq_compContinuousLinearMap_inr` and
     `norm_iteratedFDeriv_partialEval₁_le`.  They are the `inr` analogues of
     the existing `partialEval₂` lemmas.  It then proves
     `schwartzPartialEval₁CLM_seminorm_le` in the kernel layer:
     ```
     SchwartzMap.seminorm ℂ k l (schwartzPartialEval₁CLM z F) ≤
       SchwartzMap.seminorm ℂ k l F
     ```
     because the derivative of `t ↦ F (z,t)` is the full mixed derivative
     precomposed with `ContinuousLinearMap.inr`, whose operator norm is at
     most one, and the product norm gives `‖t‖ ≤ ‖(z,t)‖`.  Therefore
     `schwartzPartialEval₁CLM_compactSeminormBound` uses the exact witnesses
     `s' = s` and `C = 1`; the hypotheses `z ∈ closedBall 0 R` and `0 ≤ R`
     are retained only for the downstream compact-family API.  No
     Banach-Steinhaus input is used here.
   * `continuous_schwartzPartialEval₁CLM` is the SCV-local analogue of the
     existing Wightman-side `continuous_partialEval₂`, but it must be proved in
     the SCV layer rather than imported.  To avoid an import cycle, put the
     genuine Frechet-topology proof in `SCV/SchwartzPartialEval.lean` for the
     generic first-variable partial-evaluation map:
     ```lean
     def schwartzPartialEval₁
         (F : SchwartzMap (E₁ × E₂) G) (x : E₁) :
         SchwartzMap E₂ G

     theorem schwartzPartialEval₁_apply
         (F : SchwartzMap (E₁ × E₂) G) (x : E₁) (y : E₂) :
         schwartzPartialEval₁ F x y = F (x,y)

     theorem continuous_schwartzPartialEval₁
         (F : SchwartzMap (E₁ × E₂) G) :
         Continuous (fun x : E₁ => schwartzPartialEval₁ F x)
     ```
     Then the public kernel theorem
     `continuous_schwartzPartialEval₁CLM` is the consumer-facing corollary in
     `SCV/DistributionalEOWKernel.lean`, proved by extensionality from
     `schwartzPartialEval₁_apply` and `schwartzPartialEval₁CLM_apply`.  This
     corollary is not a substitute for the proof; it connects the checked
     generic continuity theorem to the actual CLM API used by the mixed
     pairing.

     The generic proof is the same Frechet-topology argument with the two
     factors swapped.  First prove a tail lemma:
     ```
     schwartzPartialEval₁_tail_small :
       ∀ k l ε, 0 < ε ->
         ∃ R, 0 < R ∧ ∀ z t, R < ‖t‖ ->
           ‖t‖ ^ k *
             ‖iteratedFDeriv ℝ l
               (fun t' => F (z,t')) t‖ < ε.
     ```
     It uses `F.decay' (k+2) l`, `‖t‖ ≤ ‖(z,t)‖`, and
     `norm_iteratedFDeriv_partialEval₁_le`.  Then prove the parameter
     derivative lemmas, obtained from the already checked derivative formula by
     replacing `ContinuousLinearMap.inr`/`inl` in the Wightman proof:
     ```
     hasFDerivAt_iteratedFDeriv_partialEval₁_param
     norm_fderiv_iteratedFDeriv_partialEval₁_param_le
     ```
     The norm bound is controlled by the `(l+1)`-st full mixed derivative of
     `F`.  Finally use
     `(schwartz_withSeminorms ℂ (Fin m -> ℝ) ℂ).tendsto_nhds`: given a
     seminorm `(k,l)` and `ε`, split the `t`-space into the tail
     `R < ‖t‖`, controlled by the tail lemma for both `z` and `z0`, and the
     compact ball `‖t‖ ≤ max R 1`, controlled by the mean-value estimate from
     `norm_fderiv_iteratedFDeriv_partialEval₁_param_le` as `z -> z0`.
     This is the exact continuity input used later for
     `z ↦ η z` in the cutoff-envelope integrand.
   * `KernelSupportWithin.mono` is the closed-ball inclusion proof:
     if `hψ : tsupport ψ ⊆ closedBall 0 r` and `r ≤ R`, then every support
     point lies in `closedBall 0 R` by
     `Metric.closedBall_subset_closedBall`.  This is used so the original-edge
     cutoff can be chosen on any convenient positive radius `rψ` satisfying
     `‖A‖ * rcut ≤ rψ`; no positivity theorem for the operator norm of the
     local chart equivalence is needed.
   * `SchwartzMap.exists_schwartzCLM_finsetSeminormBound` is the generic
     finite-seminorm transport fact for the kernel Schwartz space.  Let
     `p := schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ`.  For each output
     seminorm index `i`, the seminorm `(p i).comp T.toLinearMap` is continuous
     on the input Schwartz space because `(schwartz_withSeminorms ℂ
     (Fin m -> ℝ) ℂ).continuous_seminorm i` composes with `T.continuous`.
     Applying `Seminorm.bound_of_continuous` gives a finite input seminorm
     controlling that one output seminorm.  Package these pointwise bounds as
     `Seminorm.IsBounded p p T.toLinearMap`, then apply
     `Seminorm.isBounded_sup` to the finite set `s0`.  Coerce the returned
     `NNReal` constant to `ℝ`; its nonnegativity is `Cnn.2`.  The final line is
     `Seminorm.le_def.mp hsup ψ`.
   * `regularizedLocalEOW_originalFamily_compactValueCLM` is checked as the
     compact version of `regularizedEnvelope_valueCLM_of_cutoff`.  Its proof
     not rebuild the circle-parameter CLM from scratch.  Define the total
     family
     ```
     L z =
       if hz : z ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) then
         (regularizedEnvelope_valueCLM_of_cutoff ... z hz).choose
       else
         0
     ```
     using the same original-edge cutoff `χψ`.  On
     `z ∈ Metric.closedBall 0 Rcut`, the hypothesis
     `closedBall 0 Rcut ⊆ ball 0 (δ / 2)` supplies `hz`, and
     `.choose_spec` gives the exact value identity
     `L z η = localRudinEnvelope δ x0 ys
       (realMollifyLocal Fplus (χψ • η))
       (realMollifyLocal Fminus (χψ • η)) z`.

     For the single finite-seminorm bound, index Banach-Steinhaus by the
     compact-window subtype
     `Zcut := {z // z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut}`
     and the real-linear family `z ↦ (L z).restrictScalars ℝ`.  For each fixed
     test `η`, let `ηχ := χψ • η`.  The support lemma
     `KernelSupportWithin.smulLeftCLM_of_leftSupport hχψ_support η` gives
     `KernelSupportWithin ηχ rLarge`; hence `ηχ` has compact support and the
     existing side-margin, side-holomorphy, and common-boundary proofs used in
     `exists_localRudinIntegrand_smulLeftCLM_clmFamily` apply verbatim.
     Applying `exists_bound_localRudinIntegrand` once to this fixed `ηχ`
     gives a constant `Mη` that bounds the Rudin integrand for every
     `w ∈ ball 0 (δ / 2)` and every circle parameter `θ`.  Therefore every
     `z : Zcut` satisfies
     ```
     ‖L z η‖ ≤ ‖((2 * Real.pi)⁻¹ : ℝ)‖ *
       ((max Mη 0) * |Real.pi - (-Real.pi)|).
     ```
     This proves pointwise boundedness of the family `z ↦ L z` on each fixed
     test `η`.  Apply
     `SchwartzMap.tempered_uniform_schwartz_bound` to the subtype-indexed
     real-linear family, convert the resulting real Schwartz seminorm
     supremum to the complex one by the same `sup_apply_real_eq_complex`
     induction used in
     `exists_schwartz_bound_normalized_intervalIntegral_clm_family`, and return
     the common finite set and constant.  This is the step that prevents a
     hidden pointwise-continuity-to-continuity gap in the mixed `K`.

   The chart-kernel value theorem is deliberately stated as a transformation of
   the original-family compact value-CLM package, rather than by repeating the
   full fixed-window hypothesis block.  This is not a wrapper: it contains the
   chart-linear change of kernel coordinates, the two cutoff-removal arguments,
   support-radius transport, and the finite-seminorm transport for the composed
   Schwartz CLM.

   ```lean
   theorem regularizedLocalEOW_chartKernelFamily_valueCLM
       {m : ℕ}
       (ys : Fin m -> Fin m -> ℝ) (hli : LinearIndependent ℝ ys)
       {Rcut r rcut rψ : ℝ}
       (χr χψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (Gorig : SchwartzMap (Fin m -> ℝ) ℂ ->
         ComplexChartSpace m -> ℂ)
       (Lorig : ComplexChartSpace m ->
         SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
       (hχr_one :
         ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r, χr t = 1)
       (hχr_support :
         tsupport (χr : (Fin m -> ℝ) -> ℂ) ⊆
           Metric.closedBall 0 rcut)
       (hAcut_le :
         ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
             rcut ≤ rψ)
       (hχψ_one :
         ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) rψ, χψ t = 1)
       (hLorig_value :
         ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
         ∀ η : SchwartzMap (Fin m -> ℝ) ℂ,
           Lorig z η =
             Gorig
               (SchwartzMap.smulLeftCLM ℂ
                 (χψ : (Fin m -> ℝ) -> ℂ) η) z)
       (hLorig_bound :
         ∃ s0 : Finset (ℕ × ℕ), ∃ C0 : ℝ, 0 ≤ C0 ∧
           ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
           ∀ η : SchwartzMap (Fin m -> ℝ) ℂ,
             ‖Lorig z η‖ ≤
               C0 * s0.sup
                 (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ) η) :
       let P := localEOWRealLinearKernelPushforwardCLM ys hli
       let Gchart : SchwartzMap (Fin m -> ℝ) ℂ ->
           ComplexChartSpace m -> ℂ :=
         fun ψ z => Gorig (P ψ) z
       ∃ Lchart : ComplexChartSpace m ->
           SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
         (∀ z ψ,
           Lchart z ψ =
             Lorig z
               (P (SchwartzMap.smulLeftCLM ℂ
                 (χr : (Fin m -> ℝ) -> ℂ) ψ))) ∧
         (∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
           ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
             KernelSupportWithin ψ r ->
               Lchart z ψ = Gchart ψ z) ∧
         ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
           ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
           ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
             ‖Lchart z ψ‖ ≤
               C * s.sup (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ) ψ
   ```

   Proof transcript:

   1. Set `P := localEOWRealLinearKernelPushforwardCLM ys hli` and
      `B := P.comp (SchwartzMap.smulLeftCLM ℂ
      (χr : (Fin m -> ℝ) -> ℂ))`.  Define
      `Lchart z := (Lorig z).comp B`.  The first returned identity is then
      definitional after unfolding `B`.
   2. For a supported chart kernel `hψ : KernelSupportWithin ψ r`, remove the
      chart cutoff:
      ```
      hχr_id :
        SchwartzMap.smulLeftCLM ℂ (χr : (Fin m -> ℝ) -> ℂ) ψ = ψ :=
          KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall
            χr hχr_one hψ
      ```
   3. Independently, use the cutoff support to place the cutoff kernel in the
      larger chart radius:
      ```
      hcut_support :
        KernelSupportWithin
          (SchwartzMap.smulLeftCLM ℂ
            (χr : (Fin m -> ℝ) -> ℂ) ψ) rcut :=
        KernelSupportWithin.smulLeftCLM_of_leftSupport hχr_support ψ
      ```
      Push this through the Jacobian-normalized chart-to-original kernel map:
      ```
      hpush0 :
        KernelSupportWithin
          (P (SchwartzMap.smulLeftCLM ℂ
            (χr : (Fin m -> ℝ) -> ℂ) ψ))
          (‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * rcut) :=
        KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM
          ys hli hcut_support
      hpush : KernelSupportWithin (P (χr • ψ)) rψ :=
        hpush0.mono hAcut_le
      ```
   4. Remove the original-edge cutoff by the same cutoff-removal lemma:
      ```
      hχψ_id :
        SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m -> ℝ) -> ℂ)
            (P (χr • ψ)) =
          P (χr • ψ) :=
        KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall
          χψ hχψ_one hpush
      ```
      Then the value identity on `z ∈ closedBall 0 Rcut` is the calc chain
      ```
      Lchart z ψ
        = Lorig z (P (χr • ψ))
        = Gorig (χψ • P (χr • ψ)) z
        = Gorig (P (χr • ψ)) z
        = Gorig (P ψ) z
        = Gchart ψ z.
      ```
      The penultimate equality rewrites by `hχr_id` and linearity of `P`
      (or simply `rw [hχr_id]` under the argument of `P`).
   5. For the finite-seminorm bound, unpack `hLorig_bound` as `s0, C0`.
      Apply
      `SchwartzMap.exists_schwartzCLM_finsetSeminormBound B s0` to obtain
      `s1, C1`.  For `z ∈ closedBall 0 Rcut`,
      ```
      ‖Lchart z ψ‖
        = ‖Lorig z (B ψ)‖
        ≤ C0 * s0.sup p (B ψ)
        ≤ C0 * (C1 * s1.sup p ψ)
        = (C0 * C1) * s1.sup p ψ,
      ```
      where `p = schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ`.  The middle
      inequality uses `mul_le_mul_of_nonneg_left` and `0 ≤ C0`; the returned
      constant is `C0 * C1`, nonnegative by `mul_nonneg hC0 hC1`.

   The mixed pairing cannot be defined by integrating an arbitrary
   choice-valued map `z ↦ Lchart z`: that would hide a measurability gap.
   Instead, define the integral from the actual cutoff envelope expression and
   use the chart-kernel value CLM only to prove linearity and the uniform
   seminorm bound.  The continuity helper needed for the definition is:

   ```lean
   theorem continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand
       {Cplus Cminus : Set (Fin m -> ℝ)}
       {δ ρ r Rcut rψLarge : ℝ}
       (hm : 0 < m)
       (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
       (E : Set (Fin m -> ℝ))
       (hΩplus_open : IsOpen Ωplus)
       (hΩminus_open : IsOpen Ωminus)
       (hDplus_open : IsOpen Dplus)
       (hDminus_open : IsOpen Dminus)
       (Fplus Fminus : ComplexChartSpace m -> ℂ)
       (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
       (hplus_margin_closed :
         ∀ z ∈ Dplus,
         ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) rψLarge,
           z + realEmbed t ∈ Ωplus)
       (hminus_margin_closed :
         ∀ z ∈ Dminus,
         ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) rψLarge,
           z + realEmbed t ∈ Ωminus)
       (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
       (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
       (Tplus Tminus :
         (Fin m -> ℝ) ->
           SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
       (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
       (hplus_eval :
         ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
           KernelSupportWithin ψ rψLarge ->
           ∀ w ∈ Dplus,
             realMollifyLocal Fplus ψ w =
               Tplus (fun i => (w i).im)
                 (translateSchwartz (fun i => - (w i).re) ψ))
       (hminus_eval :
         ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
           KernelSupportWithin ψ rψLarge ->
           ∀ w ∈ Dminus,
             realMollifyLocal Fminus ψ w =
               Tminus (fun i => (w i).im)
                 (translateSchwartz (fun i => - (w i).re) ψ))
       (hplus_limit :
         ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
           Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
             (nhds ((Tchart.restrictScalars ℝ) f)))
       (hminus_limit :
         ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
           Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
             (nhds ((Tchart.restrictScalars ℝ) f)))
       (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
       (hli : LinearIndependent ℝ ys)
       (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
       (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
       (hRcut_window :
         Metric.closedBall (0 : ComplexChartSpace m) Rcut ⊆
           Metric.ball (0 : ComplexChartSpace m) (δ / 2))
       (hE_compact : IsCompact E)
       (hE_mem :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
           localEOWRealChart x0 ys u ∈ E)
       (hplus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, 0 ≤ v j) ->
           0 < ∑ j, v j ->
           (∑ j, v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
       (hminus :
         ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
         ∀ v : Fin m -> ℝ,
           (∀ j, v j ≤ 0) ->
           0 < ∑ j, -v j ->
           (∑ j, -v j) < r ->
             localEOWChart x0 ys
               (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
       (χU : SchwartzMap (ComplexChartSpace m) ℂ)
       (χr χψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hχψ_support :
         tsupport (χψ : (Fin m -> ℝ) -> ℂ) ⊆
           Metric.closedBall 0 rψLarge)
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       let P := localEOWRealLinearKernelPushforwardCLM ys hli
       let η : ComplexChartSpace m ->
           SchwartzMap (Fin m -> ℝ) ℂ :=
         fun z =>
           SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m -> ℝ) -> ℂ)
             (P (SchwartzMap.smulLeftCLM ℂ
               (χr : (Fin m -> ℝ) -> ℂ)
               (schwartzPartialEval₁CLM z F)))
       ContinuousOn
         (fun z : ComplexChartSpace m =>
           χU z *
             localRudinEnvelope δ x0 ys
               (fun w => realMollifyLocal Fplus (η z) w)
               (fun w => realMollifyLocal Fminus (η z) w) z)
         (Metric.closedBall (0 : ComplexChartSpace m) Rcut)
   ```

   Proof transcript for this continuity helper.  This theorem should not be
   implemented as one monolithic proof; the Lean-ready route is the following
   helper stack.

   1. First prove continuity of the actual varying cutoff kernel:
      ```lean
      theorem continuous_chartKernelCutoffSlice
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
          let P := localEOWRealLinearKernelPushforwardCLM ys hli
          Continuous fun z : ComplexChartSpace m =>
            SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m -> ℝ) -> ℂ)
              (P (SchwartzMap.smulLeftCLM ℂ
                (χr : (Fin m -> ℝ) -> ℂ)
                (schwartzPartialEval₁CLM z F)))
      ```
      This is a pure composition of
      `continuous_schwartzPartialEval₁CLM F` with the continuous linear maps
      `χr • ·`, `localEOWRealLinearKernelPushforwardCLM ys hli`, and
      `χψ • ·`.

      Also record the pointwise formula.  For
      `z : ComplexChartSpace m` and `y : Fin m -> ℝ`,
      ```
      η z y =
        χψ y *
          ((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
          χr ((localEOWRealLinearCLE ys hli).symm y) *
          F (z, (localEOWRealLinearCLE ys hli).symm y).
      ```
      This is obtained by rewriting with
      `localEOWRealLinearKernelPushforwardCLM_apply`,
      `SchwartzMap.smulLeftCLM_apply_apply`, and
      `schwartzPartialEval₁CLM_apply`.  The right-hand side is continuous in
      `(z,y)`.

      The scalar evaluation continuity used by the variable-kernel mollifier is
      a separate small theorem, not an implicit property of Schwartz-space
      convergence:
      ```lean
      theorem continuous_chartKernelCutoffSlice_eval
          (ys : Fin m -> Fin m -> ℝ) (hli : LinearIndependent ℝ ys)
          (χr χψ : SchwartzMap (Fin m -> ℝ) ℂ)
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
          Continuous fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
            (SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m -> ℝ) -> ℂ)
              (localEOWRealLinearKernelPushforwardCLM ys hli
                (SchwartzMap.smulLeftCLM ℂ
                (χr : (Fin m -> ℝ) -> ℂ)
                (schwartzPartialEval₁CLM p.1 F)))) p.2
      ```
      Proof: use the displayed pointwise formula.  The maps
      `p ↦ p.1`, `p ↦ (localEOWRealLinearCLE ys hli).symm p.2`, the two
      cutoff evaluations, and the mixed Schwartz test evaluation
      `p ↦ F (p.1, (localEOWRealLinearCLE ys hli).symm p.2)` are continuous;
      multiplication by the constant inverse Jacobian is continuous.  This
      theorem supplies the `hη_eval_cont` input of
      `continuousOn_realMollifyLocal_varyingKernel_of_fixedSupport` by
      restriction to any parameter set.

      The support input is also explicit:
      ```lean
      theorem KernelSupportWithin.chartKernelCutoffSlice
          (ys : Fin m -> Fin m -> ℝ) (hli : LinearIndependent ℝ ys)
          (χr χψ : SchwartzMap (Fin m -> ℝ) ℂ)
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
          {rψLarge : ℝ}
          (hχψ_support :
            tsupport (χψ : (Fin m -> ℝ) -> ℂ) ⊆
              Metric.closedBall 0 rψLarge) :
          ∀ z : ComplexChartSpace m,
            KernelSupportWithin
              (SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m -> ℝ) -> ℂ)
                (SCV.localEOWRealLinearKernelPushforwardCLM ys hli
                  (SchwartzMap.smulLeftCLM ℂ
                  (χr : (Fin m -> ℝ) -> ℂ)
                  (schwartzPartialEval₁CLM z F))))
              rψLarge
      ```
      This is exactly
      `KernelSupportWithin.smulLeftCLM_of_leftSupport hχψ_support _`.
      When a pointwise zero-outside-`closedBall` hypothesis is needed, combine
      this support inclusion with the checked
      `KernelSupportWithin.eq_zero_of_not_mem_closedBall`.

   2. Prove a reusable varying-kernel real-mollifier continuity lemma:
      ```lean
      theorem continuousOn_realMollifyLocal_varyingKernel_of_fixedSupport
          {X : Type*} [TopologicalSpace X]
          (S : Set X) (K : Set (Fin m -> ℝ))
          (Fside : ComplexChartSpace m -> ℂ)
          (Ω : Set (ComplexChartSpace m))
          (w : X -> ComplexChartSpace m)
          (η : X -> SchwartzMap (Fin m -> ℝ) ℂ)
          (hK : IsCompact K)
          (hΩ_open : IsOpen Ω)
          (hFside_cont : ContinuousOn Fside Ω)
          (hw_cont : ContinuousOn w S)
          (hη_eval_cont :
            ContinuousOn
              (fun p : X × (Fin m -> ℝ) => η p.1 p.2)
              (S ×ˢ Set.univ))
          (hη_zero : ∀ q ∈ S, ∀ t ∉ K, η q t = 0)
          (hmargin : ∀ q ∈ S, ∀ t ∈ K,
            w q + realEmbed t ∈ Ω) :
          ContinuousOn
            (fun q => realMollifyLocal Fside (η q) (w q)) S
      ```
      Its proof is exactly the checked
      `continuousOn_realMollifyLocal_of_translate_margin`, but with parameter
      space `X` and variable kernel.  Let
      `f q t = Fside (w q + realEmbed t) * η q t`; prove
      `ContinuousOn f.uncurry (S ×ˢ Set.univ)` by `hFside_cont`, `hw_cont`,
      continuity of `realEmbed`, and `hη_eval_cont`.  The open-domain
      hypothesis `hΩ_open` is essential: at a point with `t ∈ K`, the margin
      puts `w q + realEmbed t` in `Ω`, and openness gives a neighborhood on
      which the side function is evaluated inside `Ω`.  At a point with
      `t ∉ K`, compactness gives `IsClosed K`, hence a neighborhood of `t`
      disjoint from `K`, and `hη_zero` makes the integrand locally zero.
      Finally prove `f q t = 0` outside the fixed compact `K` by `hη_zero`
      and apply mathlib's checked
      `MeasureTheory.continuousOn_integral_of_compact_support`
      (whose local name is `continuousOn_integral_of_compact_support`).

      For the chart-kernel slice, take
      `K = Metric.closedBall (0 : Fin m -> ℝ) rψLarge`.  Compactness is
      finite-dimensional closed-ball compactness, and
      `hη_zero` follows from
      `KernelSupportWithin (η z) rψLarge`, which in turn follows from
      `KernelSupportWithin.smulLeftCLM_of_leftSupport hχψ_support _`.  Thus
      every real-mollifier integral is restricted to the same compact ball,
      and the fixed-window side-margin hypotheses keep all translated points
      inside `Ωplus` or `Ωminus`.

   3. Prove the fixed-support joint translation-continuity helper needed for
      the boundary branch.  First add the genuine uniform-on-compact seminorm
      estimate that the proof needs:
      ```lean
      theorem seminorm_translateSchwartz_uniformOn
          (E : Set (Fin m -> ℝ)) (hE : IsCompact E)
          (k l : ℕ) :
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ a ∈ E, ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
              (SchwartzMap.seminorm ℝ k l) (translateSchwartz a ψ) ≤
                C * ((SchwartzMap.seminorm ℝ k l) ψ +
                  (SchwartzMap.seminorm ℝ 0 l) ψ)
      ```
      Proof: use compactness of `E` and continuity of `a ↦ ‖a‖` to choose
      `R` with `0 ≤ R` and `‖a‖ ≤ R` on `E`.  For
      `(translateSchwartz a ψ) x = ψ (x + a)`, rewrite derivatives with
      `iteratedFDeriv_comp_add_right`.  With `y = x + a`, use
      `‖x‖ = ‖y - a‖ ≤ ‖y‖ + ‖a‖` and `add_pow_le` to control the translated
      `k,l` seminorm by the sum of the original `k,l` and `0,l` seminorms,
      uniformly for `a ∈ E`; one admissible constant is
      `C = 2 ^ (k - 1) * (1 + R) ^ k`.  The extra `0,l` seminorm is essential:
      the `k,l` seminorm alone does not control values translated through the
      origin.  This is a real estimate, not a wrapper around the
      existing pointwise-growth theorem `seminorm_translateSchwartz_le`; the
      old theorem has a constant depending on `ψ`, while this one is uniform
      as a continuous operator bound on compact translation sets.

      Then prove:
      ```lean
      theorem continuousOn_translateSchwartz_varyingKernel_of_fixedSupport
          (Z : Set (ComplexChartSpace m)) (E : Set (Fin m -> ℝ))
          (K : Set (Fin m -> ℝ))
          (η : ComplexChartSpace m -> SchwartzMap (Fin m -> ℝ) ℂ)
          (hE_compact : IsCompact E) (hK_compact : IsCompact K)
          (hη_cont : ContinuousOn η Z)
          (hη_zero : ∀ z ∈ Z, ∀ t ∉ K, η z t = 0) :
          ContinuousOn
            (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
              translateSchwartz (-p.2) (η p.1))
            (Z ×ˢ E)
      ```
      The proof is a Schwartz-seminorm argument, not a scalar shortcut.  For
      each finite seminorm, write
      ```
      translate (-a) (η z) - translate (-a0) (η z0)
        =
        translate (-a) (η z - η z0) +
        (translate (-a) (η z0) - translate (-a0) (η z0)).
      ```
      Apply `seminorm_translateSchwartz_uniformOn` to the compact set
      `(fun a => -a) '' E`.  The first term tends to zero by `hη_cont`.  For the
      second term, derive `HasCompactSupport (η z0 : (Fin m -> ℝ) -> ℂ)` from
      `hη_zero z0 hz0`, `isClosed_tsupport`, and `hK_compact`; then use the
      checked compact-support translation-continuity theorem
      `tendsto_translateSchwartz_nhds_of_isCompactSupport`, with support of
      `η z0` contained in `K`.  This is the vector-valued version of the scalar
      `continuous_apply_translateSchwartz_of_isCompactSupport` route, and it is
      the exact input needed before applying `Tchart.continuous`.

   4. Prove the missing uniform bound as a parametric version of the checked
      compact-bound theorem:
      ```lean
      theorem exists_bound_localRudinIntegrand_varyingKernel
          (hm : 0 < m)
          (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
          (E : Set (Fin m -> ℝ))
          (hΩplus_open : IsOpen Ωplus)
          (hΩminus_open : IsOpen Ωminus)
          (Fplus Fminus : ComplexChartSpace m -> ℂ)
          (hFplus_cont : ContinuousOn Fplus Ωplus)
          (hFminus_cont : ContinuousOn Fminus Ωminus)
          {δ ρ r rψLarge : ℝ}
          (hplus_margin_closed :
            ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) rψLarge,
              z + realEmbed t ∈ Ωplus)
          (hminus_margin_closed :
            ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) rψLarge,
              z + realEmbed t ∈ Ωminus)
          (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
          (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
          (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
          (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
          (Z : Set (ComplexChartSpace m))
          (η : ComplexChartSpace m -> SchwartzMap (Fin m -> ℝ) ℂ)
          (hZ_compact : IsCompact Z)
          (hZ_ball :
            Z ⊆ Metric.ball (0 : ComplexChartSpace m) (δ / 2))
          (hη_eval_cont :
            ContinuousOn
              (fun p : ComplexChartSpace m × (Fin m -> ℝ) => η p.1 p.2)
              (Z ×ˢ Set.univ))
          (hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge)
          (hbv_cont :
            ContinuousOn
              (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
                Tchart (translateSchwartz (-p.2) (η p.1)))
              (Z ×ˢ E))
          (hplus_boundary :
            ∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
              l0.im = 0 ->
                Filter.Tendsto
                  (fun p : ComplexChartSpace m × ℂ =>
                    realMollifyLocal Fplus (η p.1)
                      (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
                  (nhdsWithin (z0, l0)
                    ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
                      {p : ComplexChartSpace m × ℂ | 0 < p.2.im}))
                  (nhds
                    (Tchart
                      (translateSchwartz
                        (-(localEOWRealChart x0 ys
                          (fun j => (localEOWSmp δ z0 l0 j).re)))
                        (η z0)))))
          (hminus_boundary :
            ∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
              l0.im = 0 ->
                Filter.Tendsto
                  (fun p : ComplexChartSpace m × ℂ =>
                    realMollifyLocal Fminus (η p.1)
                      (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
                  (nhdsWithin (z0, l0)
                    ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
                      {p : ComplexChartSpace m × ℂ | p.2.im < 0}))
                  (nhds
                    (Tchart
                      (translateSchwartz
                        (-(localEOWRealChart x0 ys
                          (fun j => (localEOWSmp δ z0 l0 j).re)))
                        (η z0)))))
          (hE_mem :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
              localEOWRealChart x0 ys u ∈ E)
          (hplus :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
            ∀ v : Fin m -> ℝ,
              (∀ j, 0 ≤ v j) ->
              0 < ∑ j, v j ->
              (∑ j, v j) < r ->
                localEOWChart x0 ys
                  (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
          (hminus :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
            ∀ v : Fin m -> ℝ,
              (∀ j, v j ≤ 0) ->
              0 < ∑ j, -v j ->
              (∑ j, -v j) < r ->
                localEOWChart x0 ys
                  (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) :
          ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Z, ∀ θ : ℝ,
            ‖localRudinIntegrand δ x0 ys
              (realMollifyLocal Fplus (η z))
              (realMollifyLocal Fminus (η z)) z θ‖ ≤ M
      ```
      Here `Dplus` and `Dminus` are the inner local EOW side domains used by
      the Rudin circle, while `Ωplus` and `Ωminus` are the original domains on
      which the translated real-mollifier integrals evaluate `Fplus` and
      `Fminus`.  The bound theorem itself only needs `Fplus` and `Fminus`
      continuous on those original domains; the differentiability and openness
      of the inner domains belong to the later measurability/holomorphy step,
      not to this scalar compact-bound theorem.  The proof is not a
      compactness handwave.  It copies the checked
      `exists_bound_localRudinIntegrand` construction with one extra compact
      parameter `z ∈ Z`: replace the compact set
      `closedBall 0 (δ/2) × sphere 0 1` by `Z ×ˢ sphere 0 1`, using
      `hZ_ball` whenever the checked local-sphere lemmas require membership in
      `closedBall 0 (δ/2)`.

      Define on `S := Z ×ˢ Metric.sphere (0 : ℂ) 1`
      ```
      sample (z,l) = localEOWChart x0 ys (localEOWSmp δ z l)
      realSample (z,l) =
        localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ z l j).re)
      H (z,l) =
        if 0 < l.im then
          realMollifyLocal Fplus (η z) (sample (z,l))
        else if l.im < 0 then
          realMollifyLocal Fminus (η z) (sample (z,l))
        else
          Tchart (translateSchwartz (-(realSample (z,l))) (η z)).
      ```
      The positive and negative branches are continuous on the corresponding
      open arcs by
      `continuousOn_realMollifyLocal_varyingKernel_of_fixedSupport` with
      compact kernel set `Metric.closedBall 0 rψLarge`, side point
      `w(z,l) = sample (z,l)`, and the margin hypotheses
      `hplus_margin_closed` / `hminus_margin_closed` after
      `localEOWChart_smp_upper_mem_of_delta_on_sphere` /
      `localEOWChart_smp_lower_mem_of_delta_on_sphere` place `sample (z,l)` in
      `Dplus` / `Dminus`; the lemma's `hFside_cont` input is
      `hFplus_cont` or `hFminus_cont`.  Its `hη_eval_cont` input is the
      displayed hypothesis composed with the projection
      `(q,t) : ((ComplexChartSpace m × ℂ) × (Fin m -> ℝ)) ↦ (q.1.1,t)`.
      In Lean, prove this by composing `hη_eval_cont` with
      `(continuous_fst.comp continuous_fst).prodMk continuous_snd` and the
      map-to proof `q.1.1 ∈ Z` from the side-domain membership.  The zero-off
      compact support input is
      `KernelSupportWithin.eq_zero_of_not_mem_closedBall (hη_support q.1.1 hz)`.

      At zero imaginary part, `realSample (z,l) ∈ E` follows from
      `localEOWSmp_re_mem_closedBall`, `hδρ`, and `hE_mem`.  The boundary
      branch is continuous by composing `hbv_cont` with
      `realParam (z,l) = (z, realSample (z,l))`; the same
      `real_chart_smp_cont` proof as above gives continuity of `realSample`,
      and `realParam` maps `S ∩ {p | p.2.im = 0}` into `Z ×ˢ E`.

      The proof of `ContinuousOn H S` is a local three-way patch at each
      `p0 = (z0,l0) ∈ S`, exactly like the checked scalar theorem, but with the
      side-limit hypotheses replacing fixed-kernel boundary limits.

      * If `0 < l0.im`, then the positive half-plane is an open neighborhood
        of `p0`; eventually on `nhdsWithin p0 S`, `H` is the positive
        real-mollifier branch.  The positive branch is continuous at `p0`
        by `continuousOn_realMollifyLocal_varyingKernel_of_fixedSupport` on
        `S ∩ {p | 0 < p.2.im}`, using `hFplus_cont`, the continuous `sample`
        map, the projected `hη_eval_cont`, the zero-off-support consequence of
        `hη_support`, and the margin
        `hplus_margin_closed (sample p) hsampleD t ht`.
      * If `l0.im < 0`, use the identical lower-side argument with
        `hFminus_cont`, `hminus_margin_closed`, and
        `localEOWChart_smp_lower_mem_of_delta_on_sphere`.
      * If `l0.im = 0`, set `x' = realSample p0`.  The endpoint identity
        `sample p0 = realEmbed x'` is
        `localEOWChart_smp_realEdge_eq_of_unit_real x0 ys`
        after deriving `Complex.normSq l0 = 1` from `l0 ∈ sphere 0 1`.
        The value of `H p0` is
        `Tchart (translateSchwartz (-x') (η z0))`.  On the positive side,
        `H` is eventually the plus real-mollifier branch, and
        `hplus_boundary z0 hz0 l0 hl0 hreal` gives exactly the required
        convergence to `H p0`.  On the negative side use
        `hminus_boundary`.  On the zero side, `H` is the boundary branch and
        continuity is the `hbv_cont ∘ realParam` convergence described above.
        Combine these three within-continuity statements using
        `ContinuousWithinAt.union`, then cover `S` by the trichotomy
        `l.im < 0 ∨ l.im = 0 ∨ 0 < l.im`.

      The side-boundary hypotheses are genuinely varying-kernel limits:
      fixed-`z` limits are not sufficient, because the kernel `η z` changes
      along the approaching arc.  In the final instantiation they are proved
      from the checked side-value identities and CLM limits as follows.  On
      the positive arc, rewrite
      ```
      realMollifyLocal Fplus (η z) (sample (z,l))
        =
      Tplus (fun i => (sample (z,l) i).im)
        (translateSchwartz (fun i => - (sample (z,l) i).re) (η z))
      ```
      using the local BHW/EOW side-evaluation theorem and
      `KernelSupportWithin (η z) rψLarge`.  The imaginary part tends to
      `0` within `Cplus` because `sample (z,l) ∈ Dplus` on the positive arc
      and `Dplus ⊆ TubeDomain Cplus`; the translated kernels tend in Schwartz
      topology by `continuousOn_translateSchwartz_varyingKernel_of_fixedSupport`
      applied to `(z, realSample (z,l))`.  The equality
      `fun i => (sample (z,l) i).re = realSample (z,l)` is the real part of
      `localEOWChart_real_imag`, and membership in `E` along the arc is
      supplied by `localEOWSmp_re_mem_closedBall` and `hE_mem`.
      Then
      `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter` combines the
      pointwise CLM convergence `hplus_limit` with this kernel convergence.
      On the negative arc, rewrite with `hminus_eval` instead; use
      `localEOWChart_smp_lower_mem_of_delta_on_sphere` to place
      `sample (z,l)` in `Dminus`, use `hDminus_sub` to get the imaginary
      sample in `Cminus`, compose `hminus_limit` with that lower-side
      `nhdsWithin 0 Cminus` convergence, and use the same
      `realSample` kernel convergence.  At the endpoint, rewrite
      `sample (z0,l0) = realEmbed (realSample (z0,l0))` with
      `localEOWChart_smp_realEdge_eq_of_unit_real`.

      The preceding scalar `hbv_cont`, the vector-valued translated-kernel
      continuity needed by Banach-Steinhaus, and the two side limits are
      supplied by one CLM boundary-data theorem, so they are not new assumptions
      in the final chart-kernel instantiation.  Internally that theorem first
      proves
      ```
      hkernel_cont :
        ContinuousOn
          (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
            translateSchwartz (-p.2) (η p.1))
          (Z ×ˢ E)
      ```
      from `continuousOn_translateSchwartz_varyingKernel_of_fixedSupport`,
      then obtains the returned scalar `hbv_cont` by composing with
      `Tchart.continuous`.  The split plus/minus side-limit theorems consume
      `hkernel_cont`, not merely scalar `Tchart` continuity.
      ```lean
      theorem localRudin_varyingKernel_boundaryData_of_clm
          {Cplus Cminus : Set (Fin m -> ℝ)} {δ ρ r rψLarge : ℝ}
          (hm : 0 < m)
          (Dplus Dminus : Set (ComplexChartSpace m))
          (E : Set (Fin m -> ℝ))
          (Fplus Fminus : ComplexChartSpace m -> ℂ)
          (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
          (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
          (Tplus Tminus :
            (Fin m -> ℝ) ->
              SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
          (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
          (hplus_eval :
            ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
              KernelSupportWithin ψ rψLarge ->
              ∀ w ∈ Dplus,
                realMollifyLocal Fplus ψ w =
                  Tplus (fun i => (w i).im)
                    (translateSchwartz (fun i => - (w i).re) ψ))
          (hminus_eval :
            ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
              KernelSupportWithin ψ rψLarge ->
              ∀ w ∈ Dminus,
                realMollifyLocal Fminus ψ w =
                  Tminus (fun i => (w i).im)
                    (translateSchwartz (fun i => - (w i).re) ψ))
          (hplus_limit :
            ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
              Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
                (nhds ((Tchart.restrictScalars ℝ) f)))
          (hminus_limit :
            ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
              Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
                (nhds ((Tchart.restrictScalars ℝ) f)))
          (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
          (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
          (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
          (Z : Set (ComplexChartSpace m))
          (η : ComplexChartSpace m -> SchwartzMap (Fin m -> ℝ) ℂ)
          (hZ_ball :
            Z ⊆ Metric.ball (0 : ComplexChartSpace m) (δ / 2))
          (hE_compact : IsCompact E)
          (hη_cont : ContinuousOn η Z)
          (hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge)
          (hE_mem :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
              localEOWRealChart x0 ys u ∈ E)
          (hplus :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
            ∀ v : Fin m -> ℝ,
              (∀ j, 0 ≤ v j) ->
              0 < ∑ j, v j ->
              (∑ j, v j) < r ->
                localEOWChart x0 ys
                  (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
          (hminus :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
            ∀ v : Fin m -> ℝ,
              (∀ j, v j ≤ 0) ->
              0 < ∑ j, -v j ->
              (∑ j, -v j) < r ->
                localEOWChart x0 ys
                  (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) :
          ContinuousOn
            (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
              Tchart (translateSchwartz (-p.2) (η p.1)))
            (Z ×ˢ E) ∧
          (∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
            l0.im = 0 ->
              Filter.Tendsto
                (fun p : ComplexChartSpace m × ℂ =>
                  realMollifyLocal Fplus (η p.1)
                    (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
                (nhdsWithin (z0, l0)
                  ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
                    {p : ComplexChartSpace m × ℂ | 0 < p.2.im}))
                (nhds
                  (Tchart
                    (translateSchwartz
                      (-(localEOWRealChart x0 ys
                        (fun j => (localEOWSmp δ z0 l0 j).re)))
                      (η z0))))) ∧
          (∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
            l0.im = 0 ->
              Filter.Tendsto
                (fun p : ComplexChartSpace m × ℂ =>
                  realMollifyLocal Fminus (η p.1)
                    (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
                (nhdsWithin (z0, l0)
                  ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
                    {p : ComplexChartSpace m × ℂ | p.2.im < 0}))
                (nhds
                  (Tchart
                    (translateSchwartz
                      (-(localEOWRealChart x0 ys
                        (fun j => (localEOWSmp δ z0 l0 j).re)))
                      (η z0)))))
      ```
      Proof: first derive `η z t = 0` outside
      `Metric.closedBall 0 rψLarge` from `hη_support` and
      `KernelSupportWithin.eq_zero_of_not_mem_closedBall`, then apply
      `continuousOn_translateSchwartz_varyingKernel_of_fixedSupport` on
      `Z ×ˢ E` to get the vector-valued `hkernel_cont`.  Composing
      `hkernel_cont` with `Tchart.continuous` gives the returned first
      component, checked separately as
      `continuousOn_localRudinBoundaryCLM_varyingKernel_of_fixedSupport`.
      For the positive
      side-limit, work with the filter on
      `(Z ×ˢ sphere 0 1) ∩ {0 < im}`.  The side-evaluation identity
      `hplus_eval (η z) (hη_support z hz)` rewrites the mollifier to
      `Tplus (im sample) (translateSchwartz (-realSample) (η z))`.
      The imaginary part tends to `nhdsWithin 0 Cplus` because
      `sample` is continuous, the endpoint is real by
      `localEOWChart_smp_realEdge_eq_of_unit_real`, and
      `hDplus_sub` maps the positive side into `TubeDomain Cplus`.  The
      translated kernels tend by the just-proved vector-valued `hkernel_cont`,
      composed with the continuous real-sample map.  Then
      `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter` combines
      `hplus_limit` with this moving-kernel convergence.  For the negative
      side-limit, use the lower filter
      `(Z ×ˢ sphere 0 1) ∩ {p | p.2.im < 0}`.  The identity
      `hminus_eval (η z) (hη_support z hz)` rewrites the mollifier to
      `Tminus (im sample) (translateSchwartz (-realSample) (η z))`; the
      imaginary part tends to `nhdsWithin 0 Cminus` because
      `localEOWChart_smp_lower_mem_of_delta_on_sphere` puts `sample` in
      `Dminus` and `hDminus_sub` maps `Dminus` into `TubeDomain Cminus`;
      the translated-kernel convergence is the same already checked
      `hkernel_cont` composition with `realSample`; and
      `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter` combines
      `hminus_limit` with that kernel convergence.  The two split theorem
      statements below record these plus and minus proofs without relying on a
      symmetry shortcut.

      For implementation, split the two side-limit components out before
      proving the bundled `localRudin_varyingKernel_boundaryData_of_clm`:
      ```lean
      theorem tendsto_localRudinPlusBoundary_varyingKernel_of_clm
          {Cplus : Set (Fin m -> ℝ)} {δ ρ r rψLarge : ℝ}
          (hm : 0 < m)
          (Dplus : Set (ComplexChartSpace m))
          (E : Set (Fin m -> ℝ)) (Z : Set (ComplexChartSpace m))
          (Fplus : ComplexChartSpace m -> ℂ)
          (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
          (Tplus :
            (Fin m -> ℝ) ->
              SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
          (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
          (hplus_eval :
            ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
              KernelSupportWithin ψ rψLarge ->
              ∀ w ∈ Dplus,
                realMollifyLocal Fplus ψ w =
                  Tplus (fun i => (w i).im)
                    (translateSchwartz (fun i => - (w i).re) ψ))
          (hplus_limit :
            ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
              Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
                (nhds ((Tchart.restrictScalars ℝ) f)))
          (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
          (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
          (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
          (η : ComplexChartSpace m -> SchwartzMap (Fin m -> ℝ) ℂ)
          (hZ_ball :
            Z ⊆ Metric.ball (0 : ComplexChartSpace m) (δ / 2))
          (hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge)
          (hkernel_cont :
            ContinuousOn
              (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
                translateSchwartz (-p.2) (η p.1))
              (Z ×ˢ E))
          (hE_mem :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
              localEOWRealChart x0 ys u ∈ E)
          (hplus :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
            ∀ v : Fin m -> ℝ,
              (∀ j, 0 ≤ v j) ->
              0 < ∑ j, v j ->
              (∑ j, v j) < r ->
                localEOWChart x0 ys
                  (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus) :
          ∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
            l0.im = 0 ->
              Filter.Tendsto
                (fun p : ComplexChartSpace m × ℂ =>
                  realMollifyLocal Fplus (η p.1)
                    (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
                (nhdsWithin (z0, l0)
                  ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
                    {p : ComplexChartSpace m × ℂ | 0 < p.2.im}))
                (nhds
                  (Tchart
                    (translateSchwartz
                      (-(localEOWRealChart x0 ys
                        (fun j => (localEOWSmp δ z0 l0 j).re)))
                      (η z0))))

      theorem tendsto_localRudinMinusBoundary_varyingKernel_of_clm
          {Cminus : Set (Fin m -> ℝ)} {δ ρ r rψLarge : ℝ}
          (hm : 0 < m)
          (Dminus : Set (ComplexChartSpace m))
          (E : Set (Fin m -> ℝ)) (Z : Set (ComplexChartSpace m))
          (Fminus : ComplexChartSpace m -> ℂ)
          (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
          (Tminus :
            (Fin m -> ℝ) ->
              SchwartzMap (Fin m -> ℝ) ℂ ->L[ℝ] ℂ)
          (Tchart : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
          (hminus_eval :
            ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
              KernelSupportWithin ψ rψLarge ->
              ∀ w ∈ Dminus,
                realMollifyLocal Fminus ψ w =
                  Tminus (fun i => (w i).im)
                    (translateSchwartz (fun i => - (w i).re) ψ))
          (hminus_limit :
            ∀ f : SchwartzMap (Fin m -> ℝ) ℂ,
              Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
                (nhds ((Tchart.restrictScalars ℝ) f)))
          (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
          (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
          (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
          (η : ComplexChartSpace m -> SchwartzMap (Fin m -> ℝ) ℂ)
          (hZ_ball :
            Z ⊆ Metric.ball (0 : ComplexChartSpace m) (δ / 2))
          (hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge)
          (hkernel_cont :
            ContinuousOn
              (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
                translateSchwartz (-p.2) (η p.1))
              (Z ×ˢ E))
          (hE_mem :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
              localEOWRealChart x0 ys u ∈ E)
          (hminus :
            ∀ u ∈ Metric.closedBall (0 : Fin m -> ℝ) ρ,
            ∀ v : Fin m -> ℝ,
              (∀ j, v j ≤ 0) ->
              0 < ∑ j, -v j ->
              (∑ j, -v j) < r ->
                localEOWChart x0 ys
                  (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) :
          ∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
            l0.im = 0 ->
              Filter.Tendsto
                (fun p : ComplexChartSpace m × ℂ =>
                  realMollifyLocal Fminus (η p.1)
                    (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
                (nhdsWithin (z0, l0)
                  ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
                    {p : ComplexChartSpace m × ℂ | p.2.im < 0}))
                (nhds
                  (Tchart
                    (translateSchwartz
                      (-(localEOWRealChart x0 ys
                        (fun j => (localEOWSmp δ z0 l0 j).re)))
                      (η z0))))
      ```

      Lean proof of the plus theorem.  Fix `z0 ∈ Z`, `l0 ∈ sphere 0 1`,
      and `hreal : l0.im = 0`.  Let
      `S = Z ×ˢ Metric.sphere (0 : ℂ) 1`,
      `sample p = localEOWChart x0 ys (localEOWSmp δ p.1 p.2)`, and
      `realSample p = localEOWRealChart x0 ys
        (fun j => (localEOWSmp δ p.1 p.2 j).re)`.  The needed continuity
      facts are local `have`s, not new public wrappers:
      - `hsmp_cont`: continuity of
        `p ↦ localEOWSmp δ p.1 p.2` on
        `(Metric.closedBall 0 (δ/2)) ×ˢ Metric.closedBall 0 1`, copied from
        the checked construction in `exists_bound_localRudinIntegrand`;
      - `hsample_cont`: continuity of `sample` on `S`, obtained by composing
        `hsmp_cont` with `continuous_localEOWChart x0 ys` and restricting by
        `hZ_ball` and `Metric.sphere_subset_closedBall`;
      - `hrealSample_cont`: continuity of `realSample` on `S`, obtained by
        composing `hsmp_cont`, coordinatewise `Complex.continuous_re`, and
        `continuous_localEOWRealChart x0 ys`.

      Endpoint algebra is fixed.  From `l0 ∈ sphere 0 1`,
      get `‖l0‖ = 1` and `Complex.normSq l0 = 1`; with `hreal`,
      `localEOWChart_smp_realEdge_eq_of_unit_real x0 ys` gives
      ```
      sample (z0,l0) = realEmbed (realSample (z0,l0)).
      ```
      Therefore `fun i => (sample (z0,l0) i).im = 0`.

      The imaginary-sample map tends to `nhdsWithin 0 Cplus`.  Let
      `imSample p = fun i => (sample p i).im`.  Its continuity follows from
      `hsample_cont` and coordinatewise imaginary-part continuity, its endpoint
      is `0` by the real-edge rewrite, and it maps the positive side
      `(S ∩ {p | 0 < p.2.im})` into `Cplus`: for
      `p = (z,l)` in that side, `hZ_ball z hz` gives
      `z ∈ closedBall 0 (δ/2)`, the sphere hypothesis gives `‖l‖ = 1`, and
      `localEOWChart_smp_upper_mem_of_delta_on_sphere hm Dplus x0 ys
      hδ hδρ hδsum hplus` gives `sample p ∈ Dplus`; then
      `hDplus_sub` unfolds `TubeDomain Cplus` to obtain `imSample p ∈ Cplus`.

      The moving kernel tends in the Schwartz topology by composing
      `hkernel_cont` with
      ```
      realParam p = (p.1, realSample p).
      ```
      The map `realParam` is continuous within the positive-side filter by
      `hrealSample_cont`.  It maps the positive-side filter into `Z ×ˢ E`:
      `p.1 ∈ Z` comes from `S`, and
      `realSample p ∈ E` follows from
      `localEOWSmp_re_mem_closedBall hδ hδρ` plus `hE_mem`; the closed-ball
      input to `localEOWSmp_re_mem_closedBall` is again supplied by
      `hZ_ball` and `Metric.ball_subset_closedBall`.  Hence
      `hkernel_cont.tendsto_nhdsWithin` yields
      ```
      Tendsto
        (fun p => translateSchwartz (-(realSample p)) (η p.1))
        (nhdsWithin (z0,l0) (S ∩ {p | 0 < p.2.im}))
        (nhds (translateSchwartz (-(realSample (z0,l0))) (η z0))).
      ```

      Pointwise CLM convergence is
      `hplus_limit.comp himSample_tendsto`.  Apply
      `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter` with that CLM
      convergence and the moving-kernel convergence to get convergence of
      ```
      Tplus (imSample p)
        (translateSchwartz (-(realSample p)) (η p.1)).
      ```
      Finally use `Filter.Tendsto.congr'` on the positive-side filter.  For
      every sampled `p = (z,l)` in that filter, the side membership just used
      for the cone map gives `sample p ∈ Dplus`, and `hη_support z hz` gives
      the fixed support hypothesis.  Therefore
      `hplus_eval (η z) (hη_support z hz) (sample p) hsampleD`
      rewrites the mollifier to
      ```
      Tplus (fun i => (sample p i).im)
        (translateSchwartz (fun i => -(sample p i).re) (η z)).
      ```
      The two arguments of `Tplus` are exactly the moving-limit arguments:
      `fun i => (sample p i).im = imSample p` by definition, and
      ```
      fun i => -(sample p i).re = -(realSample p)
      ```
      by extensionality and the real-coordinate identity obtained by unfolding
      `sample`, `realSample`, `localEOWChart`, and `localEOWRealChart` (or,
      equivalently, by applying `localEOWChart_real_imag` to the real and
      imaginary parts of `localEOWSmp δ z l`).  This is not a new public lemma:
      it is a local `have hsample_re : (fun i => (sample p i).re) =
      realSample p := by ext i; simp [sample, realSample, localEOWChart,
      localEOWRealChart]`, followed by `rw [hsample_re]`.  Thus the congruent
      eventual function is precisely the one handled by
      `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`.

      Lean proof of the minus theorem.  Use the same definitions `S`,
      `sample`, `realSample`, and `imSample`, the same continuity facts, and
      the same endpoint rewrite.  The map-to-cone proof uses the negative side
      `(S ∩ {p | p.2.im < 0})`: for `p = (z,l)` in that side,
      `localEOWChart_smp_lower_mem_of_delta_on_sphere hm Dminus x0 ys
      hδ hδρ hδsum hminus` gives `sample p ∈ Dminus`, and `hDminus_sub`
      gives `imSample p ∈ Cminus`.  Compose `hminus_limit` with this
      `nhdsWithin 0 Cminus` convergence, reuse the same moving-kernel
      convergence from `hkernel_cont`, apply
      `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`, and finish by
      `Filter.Tendsto.congr'` using
      `hminus_eval (η z) (hη_support z hz)` and the lower-side domain
      membership just proved.  The final translate congruence is the same
      local real-coordinate identity
      `fun i => -(sample p i).re = -(realSample p)`; do not introduce a
      separate minus-side wrapper for it.

      The three-way patch described above gives `hH_cont : ContinuousOn H S`.
      Since `hZ_compact.prod (isCompact_sphere 0 1)` makes `S` compact,
      `S.exists_bound_of_continuousOn hH_cont` gives `M0` with
      `‖H p‖ ≤ M0` for all `p ∈ S`; return `M = max M0 0`.  No nonemptiness
      hypothesis on `Z` is needed.  If `S` is empty the final universal bound
      is vacuous; otherwise `‖H p‖ ≤ M0 ≤ max M0 0`, and in all cases
      `0 ≤ max M0 0`.

      For the final `θ`-bound, fix `z ∈ Z` and set
      `l = Complex.exp ((θ : ℂ) * Complex.I)`.  Then
      `l ∈ Metric.sphere 0 1` by `Complex.norm_exp_ofReal_mul_I`, so
      `(z,l) ∈ S`.  If `0 < Real.sin θ`, then
      `0 < l.im` by `Complex.exp_ofReal_mul_I_im`; both
      `localRudinIntegrand` and `H (z,l)` choose the plus branch, so
      `simp [localRudinIntegrand, H, hl_def, hsin_pos, hl_im]` rewrites the
      desired norm to `‖H (z,l)‖`.  The negative branch is identical with
      `Real.sin θ < 0` and `l.im < 0`.  If neither strict inequality holds,
      the integrand is definitionally `0`, hence bounded by `0 ≤ M`.  This is
      the same final trigonometric rewrite as the checked
      `exists_bound_localRudinIntegrand`, with `z ∈ Z` replacing
      `w ∈ ball 0 (δ/2)`.

   5. Prove a varying-kernel Rudin-envelope continuity theorem:
      ```lean
      theorem continuousOn_localRudinEnvelope_varyingKernel_of_bound
          {δ : ℝ}
          (x0 : Fin m -> ℝ) (ys : Fin m -> Fin m -> ℝ)
          (Fplus Fminus : ComplexChartSpace m -> ℂ)
          (Z : Set (ComplexChartSpace m))
          (η : ComplexChartSpace m -> SchwartzMap (Fin m -> ℝ) ℂ)
          (hside_plus :
            ∀ θ, 0 < Real.sin θ ->
              ContinuousOn
                (fun z => realMollifyLocal Fplus (η z)
                  (localEOWChart x0 ys
                    (localEOWSmp δ z
                      (Complex.exp ((θ : ℂ) * Complex.I))))) Z)
          (hside_minus :
            ∀ θ, Real.sin θ < 0 ->
              ContinuousOn
                (fun z => realMollifyLocal Fminus (η z)
                  (localEOWChart x0 ys
                    (localEOWSmp δ z
                      (Complex.exp ((θ : ℂ) * Complex.I))))) Z)
          (M : ℝ)
          (hmeas :
            ∀ z ∈ Z,
              AEStronglyMeasurable
                (localRudinIntegrand δ x0 ys
                  (realMollifyLocal Fplus (η z))
                  (realMollifyLocal Fminus (η z)) z)
                (MeasureTheory.volume.restrict
                  (Set.uIoc (-Real.pi) Real.pi)))
          (hM : ∀ z ∈ Z, ∀ θ,
            ‖localRudinIntegrand δ x0 ys
              (realMollifyLocal Fplus (η z))
              (realMollifyLocal Fminus (η z)) z θ‖ ≤ M) :
          ContinuousOn
            (fun z =>
              localRudinEnvelope δ x0 ys
                (realMollifyLocal Fplus (η z))
                (realMollifyLocal Fminus (η z)) z) Z
      ```
      The proof is the same dominated interval argument as
      `continuousAt_localRudinIntegral_of_bound`, but the parameter is now the
      outer chart point `z`.  For a fixed `θ`, positive/negative sine cases
      use `hside_plus`/`hside_minus`; the zero-sine case is identically `0`.
      The measurability hypothesis `hmeas` supplies the first argument of
      `intervalIntegral.continuousWithinAt_of_dominated_interval`; in the final
      instantiation it is obtained from the checked
      `aestronglyMeasurable_localRudinIntegrand` using the per-`z`
      holomorphy facts supplied in step 4.  The bound `hM` supplies domination
      by the integrable constant function `fun _ => M`, and the final
      normalized envelope is a fixed real scalar multiple of the Rudin
      integral.

   6. Instantiate these helpers with
      `Z = Metric.closedBall (0 : ComplexChartSpace m) Rcut` and
      `η z = χψ • P (χr • schwartzPartialEval₁CLM z F)`.  The closed-ball
      compactness supplies `hZ_compact`, and `hRcut_window` supplies the
      `hZ_ball` hypothesis needed by the Rudin sphere lemmas.  From step 1,
      get both
      `hη_cont : ContinuousOn η Z` and the scalar evaluation continuity
      `hη_eval_cont`; from
      `KernelSupportWithin.chartKernelCutoffSlice hχψ_support`, get
      `hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge`; from this,
      get the zero-off-support hypothesis by
      `KernelSupportWithin.eq_zero_of_not_mem_closedBall`.

      Apply `localRudin_varyingKernel_boundaryData_of_clm` with this `Z` and
      `η`.  Its first component is
      ```
      hbv_cont :
        ContinuousOn
          (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
            Tchart (translateSchwartz (-p.2) (η p.1)))
          (Z ×ˢ E),
      ```
      produced from the internally derived vector-valued `hkernel_cont` and
      `Tchart.continuous`.  Its second and third components are the plus/minus
      moving-kernel side limits, with no extra assumptions: the theorem uses
      `hkernel_cont`, `hplus_eval`,
      `hminus_eval`, `hplus_limit`, `hminus_limit`,
      `hDplus_sub`, and `hDminus_sub` exactly as recorded above.

      Use step 2 to prove the fixed-`θ` side-arc continuities required by
      `continuousOn_localRudinEnvelope_varyingKernel_of_bound`.  For
      `0 < Real.sin θ`, take
      ```
      wθ z =
        localEOWChart x0 ys
          (localEOWSmp δ z (Complex.exp ((θ : ℂ) * Complex.I))).
      ```
      Continuity of `wθ` is the same `localEOWSmp`/`localEOWChart` composition
      used in the bound theorem.  The margin hypothesis for step 2 is proved
      by `localEOWChart_smp_upper_mem_of_delta_on_sphere`, followed by
      `hplus_margin_closed`; for `Real.sin θ < 0`, use the lower sphere lemma
      and `hminus_margin_closed`.  The fixed compact support set is
      `Metric.closedBall 0 rψLarge`.

      For the uniform bound, apply
      `exists_bound_localRudinIntegrand_varyingKernel` with the same
      `hbv_cont` and moving-kernel side-limit components from the boundary-data
      theorem, passing `hFplus_diff.continuousOn` and
      `hFminus_diff.continuousOn` as the original-side continuity inputs.  The
      measurability input for
      `continuousOn_localRudinEnvelope_varyingKernel_of_bound` is obtained
      pointwise from `aestronglyMeasurable_localRudinIntegrand`, and this is a
      separate obligation from the scalar bound.  For each `z ∈ Z`, set
      `ηz = η z`.  Compact support is
      `hηz_compact : HasCompactSupport (ηz : (Fin m -> ℝ) -> ℂ) :=
      KernelSupportWithin_hasCompactSupport (hη_support z hz)`.  The support
      margins needed by `localRealMollifySide_holomorphicOn_of_translate_margin`
      are
      ```
      hplus_margin_ηz :
        ∀ w ∈ Dplus, ∀ t ∈ tsupport (ηz : (Fin m -> ℝ) -> ℂ),
          w + realEmbed t ∈ Ωplus :=
        fun w hw t ht => hplus_margin_closed w hw t ((hη_support z hz) ht)
      ```
      and similarly for the lower side.  Then
      ```
      hGplus_diff :
        DifferentiableOn ℂ (realMollifyLocal Fplus ηz) Dplus :=
        localRealMollifySide_holomorphicOn_of_translate_margin
          Fplus ηz Ωplus Dplus hΩplus_open hDplus_open hFplus_diff
          hηz_compact hplus_margin_ηz
      ```
      with the analogous `hGminus_diff` on `Dminus`.  Apply
      `aestronglyMeasurable_localRudinIntegrand hm Dplus Dminus
      (realMollifyLocal Fplus ηz) (realMollifyLocal Fminus ηz)
      hGplus_diff hGminus_diff x0 ys hδ hδρ hδsum hplus hminus`
      to `z`, using `hZ_ball z hz` as the required `δ/2` chart-window input.

      The dominated-continuity theorem then gives continuity of
      `z ↦ localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus (η z))
        (realMollifyLocal Fminus (η z)) z`
      on `Z`.  Multiplication by the fixed Schwartz cutoff `χU` is continuous,
      so the displayed cutoff-envelope integrand is continuous on
      `Metric.closedBall 0 Rcut`.  The separate support hypothesis
      `tsupport χU ⊆ closedBall 0 Rcut` is only needed later, when the pairing
      CLM rewrites its compact set integral as the all-space product-test
      representation.

   The pairing theorem should use the exact post-continuity/value-CLM
   interface below.  In the fixed-window instantiation,
   ```
   Gorig η z =
     localRudinEnvelope δ x0 ys
       (realMollifyLocal Fplus η)
       (realMollifyLocal Fminus η) z
   ```
   and `Lchart`, `hLchart_cutoff`, `hLchart_value`, and `hLchart_bound` are
   the outputs of `regularizedLocalEOW_chartKernelFamily_valueCLM`.  The
   hypothesis `hcont_integrand` is exactly
   `continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand` proved above,
   and `hG_holo` is the holomorphy field of
   `regularizedLocalEOW_family_from_fixedWindow` after applying the
   Jacobian-normalized chart-kernel pushforward.  This interface is not a
   wrapper: it is the construction step that turns the continuous cutoff
   envelope and the compact value-CLM bound into a genuine mixed Schwartz CLM.

   ```lean
   theorem regularizedLocalEOW_pairingCLM_of_fixedWindow
       (ys : Fin m -> Fin m -> ℝ)
       (hli : LinearIndependent ℝ ys)
       (δ Rcov Rcut r rcut rψ : ℝ)
       (hRcov_pos : 0 < Rcov) (hRcov_cut : Rcov < Rcut)
       (hRcut_window :
         Metric.closedBall (0 : ComplexChartSpace m) Rcut ⊆
           Metric.ball (0 : ComplexChartSpace m) (δ / 2))
       (hr : 0 < r) (hrcut : r < rcut)
       (hAcut_le :
         ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
             rcut ≤ rψ)
       (χU : SchwartzMap (ComplexChartSpace m) ℂ)
       (χr χψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hχU_one :
         ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcov,
           χU z = 1)
       (hχr_one :
         ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r, χr t = 1)
       (hχr_support :
         tsupport (χr : (Fin m -> ℝ) -> ℂ) ⊆
           Metric.closedBall 0 rcut)
       (hχψ_one :
         ∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) rψ, χψ t = 1)
       (Gorig : SchwartzMap (Fin m -> ℝ) ℂ ->
         ComplexChartSpace m -> ℂ)
       (Lchart : ComplexChartSpace m ->
         SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
       (hLchart_cutoff :
         ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
         ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
           Lchart z ψ =
             Gorig
               (SchwartzMap.smulLeftCLM ℂ
                 (χψ : (Fin m -> ℝ) -> ℂ)
                 (localEOWRealLinearKernelPushforwardCLM ys hli
                   (SchwartzMap.smulLeftCLM ℂ
                     (χr : (Fin m -> ℝ) -> ℂ) ψ))) z)
       (hLchart_value :
         ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
         ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
           KernelSupportWithin ψ r ->
             Lchart z ψ =
               Gorig (localEOWRealLinearKernelPushforwardCLM ys hli ψ) z)
       (hLchart_bound :
         ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
           ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
           ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
             ‖Lchart z ψ‖ ≤
               C * s.sup
                 (schwartzSeminormFamily ℂ (Fin m -> ℝ) ℂ) ψ)
       (hcont_integrand :
         ∀ F : SchwartzMap
             (ComplexChartSpace m × (Fin m -> ℝ)) ℂ,
           ContinuousOn
             (fun z : ComplexChartSpace m =>
               χU z *
                 Gorig
                   (SchwartzMap.smulLeftCLM ℂ
                     (χψ : (Fin m -> ℝ) -> ℂ)
                     (localEOWRealLinearKernelPushforwardCLM ys hli
                       (SchwartzMap.smulLeftCLM ℂ
                         (χr : (Fin m -> ℝ) -> ℂ)
                         (schwartzPartialEval₁CLM z F)))) z)
             (Metric.closedBall (0 : ComplexChartSpace m) Rcut))
       (hG_holo :
         ∀ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
           KernelSupportWithin ψ r ->
             DifferentiableOn ℂ
               (Gorig (localEOWRealLinearKernelPushforwardCLM ys hli ψ))
               (Metric.ball (0 : ComplexChartSpace m) (δ / 2))) :
       let Ucov := Metric.ball (0 : ComplexChartSpace m) Rcov
       let Gchart : SchwartzMap (Fin m -> ℝ) ℂ ->
           ComplexChartSpace m -> ℂ :=
         fun ψ => Gorig (localEOWRealLinearKernelPushforwardCLM ys hli ψ)
       ∃ K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ,
         (∀ ψ, KernelSupportWithin ψ r ->
           DifferentiableOn ℂ (Gchart ψ)
             (Metric.ball (0 : ComplexChartSpace m) (δ / 2))) ∧
         (∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucov ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               ∫ z : ComplexChartSpace m, Gchart ψ z * φ z)
   ```

   Proof transcript for the pairing CLM:

   1. Choose radii for the two cutoff layers:
      `Rcov < Rcut < δ / 2` in the complex chart, and
      `r < rcut` in chart-kernel coordinates.  Let
      `P = localEOWRealLinearKernelPushforwardCLM ys hli` and
      `A = ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖`.  Choose
      an original-edge identity radius `rψ` with `A * rcut ≤ rψ` and
      `0 < rψ`, for example `rψ = A * rcut + 1`; this uses only
      `0 ≤ A` and `0 < rcut`.  Choose a larger support radius
      `rψLarge` with `rψ < rψLarge`, for example `rψ + 1`.  The fixed-window
      side-margin hypotheses are instantiated with `rLarge = rψLarge`, while
      the cutoff-removal theorem for the pushed kernels uses the smaller
      identity radius `rψ`.
   2. Choose `χU` by
      `exists_complexChart_schwartz_cutoff_eq_one_on_closedBall`; choose `χr`
      from `0 < r < rcut`, and choose `χψ` from
      `0 < rψ < rψLarge`.  Thus `χr = 1` on `closedBall 0 r` and
      `tsupport χr ⊆ closedBall 0 rcut`, while `χψ = 1` on
      `closedBall 0 rψ` and `tsupport χψ ⊆ closedBall 0 rψLarge`.  The
      product-kernel construction may use these cutoffs only to make global
      Schwartz CLMs.  The later covariance statement removes them on supported
      tests.
   3. Use `regularizedLocalEOW_originalFamily_compactValueCLM` to obtain
      `Lorig z`, uniformly bounded for `z ∈ closedBall 0 Rcut`, with
      `Lorig z η = G (χψ • η) z`.  Define the chart-kernel value CLM by
      ```lean
      Lchart z :=
        (Lorig z).comp
          ((localEOWRealLinearKernelPushforwardCLM ys hli).comp
            (SchwartzMap.smulLeftCLM ℂ (χr : (Fin m -> ℝ) -> ℂ)))
      ```
      Then, if `KernelSupportWithin ψ r`, the chart cutoff is removed by
      `KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall`, the
      pushforward is supported in `closedBall 0 rψ`, the original-edge cutoff
      is removed by the same theorem, and
      `Lchart z ψ = Gchart ψ z`.
   4. Build the mixed CLM by the explicit slice formula
      ```lean
      K F =
        ∫ z in Metric.closedBall (0 : ComplexChartSpace m) Rcut,
          χU z *
            Gorig (χψ • P (χr • schwartzPartialEval₁CLM z F)) z
      ```
      Here `χr • _` and `χψ • _` abbreviate the corresponding
      `SchwartzMap.smulLeftCLM` applications.  In the fixed-window
      instantiation, expanding `Gorig` recovers the displayed local Rudin
      envelope with the plus and minus real mollifiers.  The preceding
      continuity helper gives integrability on the compact closed ball.
   5. Linearity of `F ↦ K F` is proved pointwise before integrating by
      rewriting the actual cutoff envelope through `hLchart_cutoff`:
      ```
      Gorig (χψ • P (χr • schwartzPartialEval₁CLM z F)) z
        = Lchart z (schwartzPartialEval₁CLM z F).
      ```
      The maps `schwartzPartialEval₁CLM z` and `Lchart z` are complex-linear,
      so additivity and homogeneity follow for the actual integrand after
      rewriting both sides back to the envelope expression.  The continuity
      helper supplies the integrability hypotheses for
      `MeasureTheory.integral_add` and `MeasureTheory.integral_const_mul`.
   6. The mixed finite-seminorm estimate is now mechanical but must be written
      against the value CLM, not against an arbitrary choice-valued integrand.
      For every `z ∈ closedBall 0 Rcut`,
      `hLchart_cutoff` gives
      ```
      Gorig (χψ • P (χr • schwartzPartialEval₁CLM z F)) z
        = Lchart z (schwartzPartialEval₁CLM z F).
      ```
      Combine the compact bound for `Lchart` with
      `schwartzPartialEval₁CLM_compactSeminormBound` to obtain
      ```
      ‖Lchart z (schwartzPartialEval₁CLM z F)‖
        ≤ Cmix * smix.sup p_mixed F
      ```
      uniformly for `z ∈ closedBall 0 Rcut`.  Bound the fixed cutoff on the
      compact ball by
      `Mχ := max M 0`, where `M` comes from
      `isCompact_closedBall.exists_bound_of_continuousOn` applied to
      `fun z => ‖χU z‖`.  Then
      ```
      ‖K F‖ ≤ (Mχ * Cmix * (volume (closedBall 0 Rcut)).toReal) *
        smix.sup p_mixed F.
      ```
      This is the `SchwartzMap.mkCLMtoNormedSpace` bound.
   7. For a pure tensor, use
      `schwartzPartialEval₁CLM_tensorProduct₂` to rewrite the slice as
      `φ z • ψ`.  After `hLchart_cutoff`, the integrand is
      `χU z * Lchart z (φ z • ψ)`.  Pull the scalar `φ z` through the
      continuous linear map `Lchart z`, then use `hLchart_value` to replace
      `Lchart z ψ` by `Gchart ψ z` for supported kernels.  On
      `tsupport φ`, the support hypothesis gives `z ∈ Ucov`, hence
      `z ∈ closedBall 0 Rcov` by `Metric.ball_subset_closedBall`, so
      `hχU_one` rewrites `χU z = 1`.  Off `tsupport φ`, `φ z = 0`, so both
      the compact-ball integrand and the all-space target integrand vanish
      pointwise.

      The passage from the compact-ball set integral to
      `∫ z, Gchart ψ z * φ z` must be proved by this support equality, not by
      assuming global regularity of `Gchart ψ`.  Since
      `tsupport φ ⊆ Ucov ⊆ Metric.closedBall 0 Rcut`, the all-space integrand
      is a.e. equal to the closed-ball integrand extended by zero.  On the
      closed ball, the integrand is the continuous cutoff-envelope integrand
      after the `Lchart` rewrites; outside the closed ball it is zero because
      `φ` is zero.  This supplies the measurability/integrability needed for
      the all-space integral and yields the representation
      `∫ z, Gchart ψ z * φ z` without any hidden global measurability
      assumption on `Gchart ψ`.

      The `hG_cont` input for
      `regularizedLocalEOW_pairingCLM_localCovariant` is not an additional
      analytic theorem.  In the fixed-window application it is obtained from
      the first output of `regularizedLocalEOW_pairingCLM_of_fixedWindow` by
      `DifferentiableOn.continuousOn.mono`, using
      `Metric.ball 0 Rcov ⊆ Metric.ball 0 (δ / 2)`.  This subset follows
      pointwise: from `x ∈ Metric.ball 0 Rcov` get `‖x‖ < Rcov`, hence
      `Rcov` is positive at that point, and `hRcov_small` gives
      `Rcov < δ / 2`.

   ```lean
   theorem regularizedLocalEOW_pairingCLM_localCovariant
       {m : ℕ} {δ : ℝ}
       (hm : 0 < m) (hδ : 0 < δ)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Gchart : SchwartzMap (Fin m -> ℝ) ℂ ->
         ComplexChartSpace m -> ℂ)
       (Rcov r : ℝ)
       (hRcov_small : 2 * Rcov < δ / 4)
       (hK_rep :
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ)
             (Metric.ball (0 : ComplexChartSpace m) Rcov) ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               ∫ z : ComplexChartSpace m, Gchart ψ z * φ z)
       (hG_cont :
         ∀ ψ, KernelSupportWithin ψ r ->
           ContinuousOn (Gchart ψ)
             (Metric.ball (0 : ComplexChartSpace m) Rcov))
       (hG_cov :
         ∀ a ψ,
           KernelSupportWithin ψ r ->
           KernelSupportWithin (translateSchwartz a ψ) r ->
           (∃ z0, z0 ∈ localEOWShiftedWindow (m := m) δ a ∧
             (∀ j, 0 < (z0 j).im)) ->
           ∀ w ∈ localEOWShiftedWindow (m := m) δ a,
             Gchart (translateSchwartz a ψ) w =
               Gchart ψ (w - realEmbed a)) :
       ProductKernelRealTranslationCovariantLocal K
         (Metric.ball (0 : ComplexChartSpace m) Rcov) r
   ```

   Proof transcript for local covariance:

   Preliminary helper needed here:

   ```lean
   theorem norm_realEmbed_eq {m : ℕ} (a : Fin m -> ℝ) :
       ‖realEmbed a‖ = ‖a‖
   ```

   Proof transcript: the checked `norm_realEmbed_le` gives
   `‖realEmbed a‖ ≤ ‖a‖`.  For the reverse inequality, use
   `pi_norm_le_iff_of_nonneg (norm_nonneg _)`; for each coordinate,
   `norm_le_pi_norm (realEmbed a) i` and `Complex.norm_real` give
   `‖a i‖ ≤ ‖realEmbed a‖`.  This is finite sup-norm equality for the real
   embedding, not a new analytic assumption.

   The all-space integral change of variables also needs a local lemma because
   `Gchart ψ` is only known on the covariance ball:

   ```lean
   theorem tsupport_subset_preimage_tsupport_complexTranslateSchwartz
       (a : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport (φ : ComplexChartSpace m -> ℂ) ⊆
         (fun z : ComplexChartSpace m => z - realEmbed a) ⁻¹'
           tsupport
             (complexTranslateSchwartz a φ : ComplexChartSpace m -> ℂ)
   ```

   Proof transcript: apply `tsupport_comp_subset_preimage` to
   `complexTranslateSchwartz a φ` and the continuous inverse translation
   `z ↦ z - realEmbed a`.  The composed function is pointwise equal to `φ`,
   because
   ```
   complexTranslateSchwartz a φ (z - realEmbed a)
     = φ ((z - realEmbed a) + realEmbed a)
     = φ z.
   ```
   This is the topological-support transport needed for local covariance.  It
   is strictly stronger than the pointwise nonzero observation and gives, from
   `SupportsInOpen (complexTranslateSchwartz a φ) U`,
   ```
   ∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
     z - realEmbed a ∈ U.
   ```

   ```lean
   theorem integral_mul_complexTranslateSchwartz_eq_shift_of_support
       (G : ComplexChartSpace m -> ℂ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (a : Fin m -> ℝ)
       (U : Set (ComplexChartSpace m))
       (hG_cont : ContinuousOn G U)
       (hφ_compact : HasCompactSupport (φ : ComplexChartSpace m -> ℂ))
       (hφ_shift :
         SupportsInOpen
           (complexTranslateSchwartz a φ : ComplexChartSpace m -> ℂ) U)
       (hshift_support :
         ∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
           z - realEmbed a ∈ U) :
       (∫ y : ComplexChartSpace m,
          G y * complexTranslateSchwartz a φ y) =
         ∫ z : ComplexChartSpace m, G (z - realEmbed a) * φ z
   ```

   Proof transcript: set
   `f y = G y * complexTranslateSchwartz a φ y`.  The shifted support
   hypothesis gives `tsupport f ⊆ tsupport (complexTranslateSchwartz a φ) ⊆ U`,
   and `hG_cont` restricted to that compact support plus continuity of the
   Schwartz factor gives integrability of `f`.  The right-hand integrand is
   supported inside `tsupport φ`, which is compact by `hφ_compact`; on this
   compact set `hshift_support` places `z - realEmbed a` in `U`, so
   `hG_cont` supplies the local continuity/measurability needed for
   `z ↦ G (z - realEmbed a) * φ z`.  The Lean change-of-variables step should
   use the additive Haar translation theorem exactly as:
   ```
   rw [← integral_add_right_eq_self
     (-realEmbed a)
     (f := fun y : ComplexChartSpace m =>
       G y * complexTranslateSchwartz a φ y)]
   ```
   and then rewrite the translated integrand pointwise:
   ```
   complexTranslateSchwartz a φ (z - realEmbed a) = φ z
   ```
   by `complexTranslateSchwartz_apply` and coordinate extensionality.  The
   compact-support/integrability proof for `f` is carried by
   `hφ_shift`; the translated right-hand integrand inherits integrability from
   this equality, and its local continuity can also be shown directly from
   `hφ_compact` and `hshift_support`.  This lemma is the only
   change-of-variables input used in the covariance proof; it avoids assuming
   any global measurability or continuity of `G`.

   1. Expand the two sides with `hK_rep`.  The left expansion is legal because
      the covariance hypothesis already supplies
      `SupportsInOpen (complexTranslateSchwartz a φ) Ucov`; the right
      expansion is legal because it supplies
      `SupportsInOpen φ Ucov` and
      `KernelSupportWithin (translateSchwartz a ψ) r`.
   2. If `φ = 0`, both product tensors are zero.  Otherwise choose
      `u` with `φ u ≠ 0` by extensionality of Schwartz maps.  Then
      `u ∈ Function.support (φ : _ -> ℂ) ⊆ tsupport φ`, hence
      `u ∈ Ucov`.
      Also
      ```
      complexTranslateSchwartz a φ (u - realEmbed a) = φ u,
      ```
      so `u - realEmbed a ∈ tsupport (complexTranslateSchwartz a φ)` and
      therefore `u - realEmbed a ∈ Ucov`.  Since
      `Ucov = Metric.ball 0 Rcov`,
      ```
      ‖realEmbed a‖ = ‖u - (u - realEmbed a)‖
        ≤ ‖u‖ + ‖u - realEmbed a‖ < Rcov + Rcov.
      ```
      Convert `‖realEmbed a‖` to `‖a‖` by `norm_realEmbed_eq`.  Thus
      `‖a‖ < 2 * Rcov < δ / 4`.
   3. Use
      `exists_positive_imag_mem_localEOWShiftedWindow_of_norm_lt` to discharge
      the seed hypothesis of `hG_cov`.
   4. Change variables in the left integral
      `∫ z, Gchart ψ z * complexTranslateSchwartz a φ z` by
      `integral_mul_complexTranslateSchwartz_eq_shift_of_support`, using
      `hG_cont ψ hψ`, `hφ.1`, the support hypothesis for
      `complexTranslateSchwartz a φ`, and
      ```
      hshift_support :
        ∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
          z - realEmbed a ∈ Ucov
      ```
      obtained by composing
      `tsupport_subset_preimage_tsupport_complexTranslateSchwartz a φ` with
      the shifted support hypothesis.  With the new variable still named `z`,
      the integrand becomes
      ```
      Gchart ψ (z - realEmbed a) * φ z.
      ```
      The sign is forced by the checked convention
      `complexTranslateSchwartz_apply`:
      `complexTranslateSchwartz a φ y = φ (y + realEmbed a)`.
   5. Prove the post-change-of-variables integrands equal pointwise by
      splitting on `φ z = 0`.  If `φ z = 0`, both sides vanish by the scalar
      factor.  If `φ z ≠ 0`, then
      `z ∈ Function.support (φ : _ -> ℂ) ⊆ tsupport φ`; the original support
      hypothesis gives `z ∈ Ucov`, and the transported topological-support
      inclusion from Step 4 gives `z - realEmbed a ∈ Ucov`.  The small-radius
      hypothesis gives `Ucov ⊆ Metric.ball 0 (δ / 2)`, hence
      `z ∈ localEOWShiftedWindow δ a`.  Therefore `hG_cov` rewrites
      ```
      Gchart ψ (z - realEmbed a)
      ```
      to
      ```
      Gchart (translateSchwartz a ψ) z.
      ```
      The all-space integral equality is therefore proved by support
      localization, not by any global measurability or global regularity
      statement for `Gchart ψ`.  The result is the right integral and hence the
      local product-kernel covariance.

   ```lean
   def schwartzTensorProduct₂CLMLeft
       {m : ℕ}
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ

   theorem schwartzTensorProduct₂CLMLeft_apply
       {m : ℕ}
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       schwartzTensorProduct₂CLMLeft φ ψ (z,t) = φ z * ψ t

   theorem shearedProductKernelFunctional_localQuotient_of_productCovariant
       {m : ℕ} {r rη : ℝ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Udesc Ucov : Set (ComplexChartSpace m))
       (hr_nonneg : 0 ≤ r) (hrη_nonneg : 0 ≤ rη)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη_norm : ∫ t : Fin m -> ℝ, η t = 1)
       (hη_support : KernelSupportWithin η rη)
       (hmargin :
         ∀ z ∈ Udesc, ∀ t : Fin m -> ℝ, ‖t‖ ≤ r + rη ->
           z + realEmbed t ∈ Ucov)
       (hcov : ProductKernelRealTranslationCovariantLocal K Ucov (r + rη))
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Udesc)
       (hψ : KernelSupportWithin ψ r) :
       K (schwartzTensorProduct₂ φ ψ) =
         complexRealFiberTranslationDescentCLM
           (shearedProductKernelFunctional K) η
           (realConvolutionTest φ ψ)

   theorem translationCovariantProductKernel_descends_local
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Udesc Ucov : Set (ComplexChartSpace m)) (r rη : ℝ)
       (hr_nonneg : 0 ≤ r) (hrη_nonneg : 0 ≤ rη)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη_norm : ∫ t : Fin m -> ℝ, η t = 1)
       (hη_support : KernelSupportWithin η rη)
       (hmargin :
         ∀ z ∈ Udesc, ∀ t : Fin m -> ℝ, ‖t‖ ≤ r + rη ->
           z + realEmbed t ∈ Ucov)
       (hcov : ProductKernelRealTranslationCovariantLocal K Ucov (r + rη)) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Udesc ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               Hdist (realConvolutionTest φ ψ)
   ```

   Proof transcript for local descent:

   1. Define `T := shearedProductKernelFunctional K` and
      `Hdist := complexRealFiberTranslationDescentCLM T η`.  Do **not** call
      `translationCovariantProductKernel_descends` or
      `map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant`:
      those checked theorems require full fiber-translation invariance on
      arbitrary mixed Schwartz tests.  Local product covariance is weaker.
      Also do **not** introduce a Bochner integral with codomain
      `SchwartzMap`: the local descent must be scalarized through real-fiber
      integration and ordinary complex-valued parameter integrals.
   2. Prove the fixed-left tensor CLM
      `schwartzTensorProduct₂CLMLeft φ` (the analogue of the checked
      `schwartzTensorProduct₂CLMRight`).  It is used only to form scalar
      continuous-linear-map compositions in the local quotient proof; it is
      not evidence for a `SchwartzMap`-valued parameter integral.
      Also prove the compact-support transport helper for complex-chart
      translations:
      ```lean
      theorem SupportsInOpen.complexTranslateSchwartz_of_image_subset
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (U V : Set (ComplexChartSpace m)) (a : Fin m -> ℝ)
          (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
          (himage :
            ∀ y : ComplexChartSpace m,
              y + realEmbed a ∈ U -> y ∈ V) :
          SupportsInOpen
            (complexTranslateSchwartz a φ : ComplexChartSpace m -> ℂ) V
      ```
      The compact-support component is the image of `tsupport φ` under the
      inverse translation `u ↦ u - realEmbed a`; the support-in-`V` component
      is `himage` applied to the defining relation
      `complexTranslateSchwartz a φ y = φ (y + realEmbed a)`.
   3. First prove the fixed-last-variable partial-evaluation CLM and the
      mixed-base real-fiber integration CLM and its scalarization theorem:
      ```lean
      def schwartzPartialEval₂CLM
          (a : Fin m -> ℝ) :
          SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ
              ->L[ℂ]
            SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ

      theorem schwartzPartialEval₂CLM_apply
          (a : Fin m -> ℝ)
          (A : SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ)
          (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
          schwartzPartialEval₂CLM a A (z,t) = A ((z,t),a)

      def mixedRealFiberIntegralCLM :
          SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ
              ->L[ℂ]
            SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ

      theorem mixedRealFiberIntegralCLM_apply
          (A : SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ)
          (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
          mixedRealFiberIntegralCLM A (z,t) =
            ∫ a : Fin m -> ℝ, A ((z,t),a)

      theorem continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral
          (L : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
          (A : SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ) :
          L (mixedRealFiberIntegralCLM A) =
            ∫ a : Fin m -> ℝ,
              L
                ((schwartzPartialEval₂CLM a A :
                  SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ))
      ```
      Here `schwartzPartialEval₂CLM` denotes fixed partial evaluation in the
      last real variable, with the product association
      `((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ))`.

      The proof of `mixedRealFiberIntegralCLM` is a literal new mixed-base
      copy of the checked `complexRealFiberIntegralCLM` construction, not an
      appeal to a hidden integral in the Schwartz topology.  Set
      `B := ComplexChartSpace m × (Fin m -> ℝ)` and
      `P := Fin m -> ℝ`.  Define
      `mixedRealFiberIntegralRaw A b := ∫ a : P, A (b,a)`, prove
      `integrable_mixedRealFiber A b`, and then prove:
      ```lean
      def mixedRealFiberIntegralRaw
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (A : SchwartzMap (B × P) V) (b : B) : V :=
          ∫ a : P, A (b,a)

      theorem integrable_mixedRealFiber
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (A : SchwartzMap (B × P) V) (b : B) :
          Integrable (fun a : P => A (b,a))

      theorem exists_seminorm_bound_mixedRealFiberIntegralRaw_zero
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
          [NormedSpace ℝ V] [SMulCommClass ℝ ℂ V] [CompleteSpace V]
          (k : ℕ) :
          ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
            ∀ (A : SchwartzMap (B × P) V) (b : B),
              ‖b‖ ^ k * ‖mixedRealFiberIntegralRaw A b‖ ≤
                C * s.sup (schwartzSeminormFamily ℂ (B × P) V) A

      def mixedBasePrecompCLM
          (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
          [NormedSpace ℝ V] [SMulCommClass ℝ ℂ V] :
          ((B × P) ->L[ℝ] V) ->L[ℂ] (B ->L[ℝ] V)

      def mixedBaseFDerivSchwartz
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (A : SchwartzMap (B × P) V) :
          SchwartzMap (B × P) (B ->L[ℝ] V)

      def mixedBaseFDerivSchwartzCLM
          (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
          [NormedSpace ℝ V] [SMulCommClass ℝ ℂ V] [CompleteSpace V] :
          SchwartzMap (B × P) V ->L[ℂ]
            SchwartzMap (B × P) (B ->L[ℝ] V)

      theorem exists_seminorm_bound_mixedBaseFDerivSchwartz
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
          [NormedSpace ℝ V] [SMulCommClass ℝ ℂ V] [CompleteSpace V]
          (s0 : Finset (ℕ × ℕ)) :
          ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
            ∀ A : SchwartzMap (B × P) V,
              s0.sup (schwartzSeminormFamily ℂ (B × P) (B ->L[ℝ] V))
                  (mixedBaseFDerivSchwartz A) ≤
                C * s.sup (schwartzSeminormFamily ℂ (B × P) V) A

      theorem fderiv_mixedRealFiberIntegralRaw_eq
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (A : SchwartzMap (B × P) V) :
          fderiv ℝ (mixedRealFiberIntegralRaw A) =
            mixedRealFiberIntegralRaw (mixedBaseFDerivSchwartz A)

      theorem exists_seminorm_bound_mixedRealFiberIntegralRaw_deriv
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
          [NormedSpace ℝ V] [SMulCommClass ℝ ℂ V] [CompleteSpace V]
          (k n : ℕ) :
          ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
            ∀ (A : SchwartzMap (B × P) V) (b : B),
              ‖b‖ ^ k *
                ‖iteratedFDeriv ℝ n (mixedRealFiberIntegralRaw A) b‖ ≤
                  C * s.sup (schwartzSeminormFamily ℂ (B × P) V) A
      ```
      These are the same estimates as the checked
      `exists_seminorm_bound_complexRealFiberIntegralRaw_zero`,
      `basePrecompCLM`, `baseFDerivSchwartzCLM`,
      `exists_seminorm_bound_baseFDerivSchwartz`, and
      `exists_seminorm_bound_complexRealFiberIntegralRaw_deriv`, with
      `ComplexChartSpace m` replaced everywhere by the real normed base
      `B`.  The only norm change is
      `‖b‖ ≤ ‖(b,a)‖` and `‖a‖ ≤ ‖(b,a)‖` from the product sup norm.  The
      derivative induction differentiates only in the `B` variable; the
      `succ` step rewrites
      `fderiv ℝ (mixedRealFiberIntegralRaw A)` as
      `mixedRealFiberIntegralRaw (mixedBaseFDerivSchwartz A)`, exactly as the
      checked proof rewrites through `baseFDerivSchwartz`.

      The scalarization theorem is proved as an equality of two continuous
      linear scalar functionals on the triple Schwartz space.  First define
      ```lean
      def mixedRealFiberIntegralScalarCLM
          (L : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
          SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ
              ->L[ℂ] ℂ

      theorem mixedRealFiberIntegralScalarCLM_apply
          (L : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
          (A : SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ) :
          mixedRealFiberIntegralScalarCLM L A =
            ∫ a : Fin m -> ℝ,
              L ((schwartzPartialEval₂CLM a A :
                SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ))
      ```
      Its continuity is a finite-seminorm estimate, not a
      `SchwartzMap`-valued Bochner statement.  From continuity of `L`, use
      `Seminorm.bound_of_continuous` for
      `schwartz_withSeminorms ℂ B ℂ` to get a finite family `s0` and constant
      `C0` with `‖L G‖ ≤ C0 * s0.sup ... G`.  For each seminorm in `s0`,
      prove the partial-evaluation decay estimate
      ```
      s0.sup ... (schwartzPartialEval₂CLM a A)
        ≤ C1 * (1 + ‖a‖) ^ (-(volume.integrablePower : ℝ))
            * s.sup ... A.
      ```
      The proof uses the full Schwartz weight in `B × P` with exponent
      enlarged by `volume.integrablePower`; since
      `‖b‖ ≤ ‖(b,a)‖` and `‖a‖ ≤ ‖(b,a)‖`, the extra weight is integrable in
      `a`.  Therefore
      `a ↦ L (schwartzPartialEval₂CLM a A)` is integrable and the scalar
      integral is bounded by a finite supremum of Schwartz seminorms of `A`.
      `SchwartzMap.mkCLMtoNormedSpace` then gives
      `mixedRealFiberIntegralScalarCLM`.

      To identify this scalar CLM with `L.comp mixedRealFiberIntegralCLM`,
      use dense product tensors in the split
      `B × P`:
      ```lean
      def mixedBaseFiberTensor
          (G : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
          (ξ : SchwartzMap (Fin m -> ℝ) ℂ) :
          SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ

      theorem mixedBaseFiberProductTensorDense_all (m : ℕ) :
          Dense ((Submodule.span ℂ
            {A | ∃ G ξ, A = mixedBaseFiberTensor G ξ}) :
            Set (SchwartzMap
              ((ComplexChartSpace m × (Fin m -> ℝ)) ×
                (Fin m -> ℝ)) ℂ))
      ```
      The density proof is the same flat Hermite argument as
      `ProductTensorDense_all`, now in real dimensions `3*m` for the base and
      `m` for the fiber: flatten
      `ComplexChartSpace m × (Fin m -> ℝ)` to `Fin (m * 2 + m) -> ℝ`, split
      Hermite products along
      `Fin ((m * 2 + m) + m)`, and use the zero-dimensional singleton case
      when `m = 0`.

      On a tensor `mixedBaseFiberTensor G ξ`,
      `mixedRealFiberIntegralCLM` gives `(∫ a, ξ a) • G`, while
      `schwartzPartialEval₂CLM a` gives `(ξ a) • G`; scalar integral linearity
      gives the same value after applying `L`.  Since both sides are
      continuous linear functionals on the triple Schwartz space and agree on
      the dense span, they agree everywhere:
      ```lean
      theorem mixedRealFiberIntegralScalarCLM_eq_comp_mixedRealFiberIntegralCLM
          (L : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
          mixedRealFiberIntegralScalarCLM L =
            L.comp mixedRealFiberIntegralCLM
      ```
      `continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral` is
      then just this equality applied to `A`, followed by
      `mixedRealFiberIntegralScalarCLM_apply`.  Every integral on the
      right-hand side has codomain `ℂ`.

   4. Prove
      the two parameterized Schwartz tests and their mixed-fiber integrals:
      ```lean
      def localDescentParamTestLeft
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ η : SchwartzMap (Fin m -> ℝ) ℂ) :
          SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ

      theorem localDescentParamTestLeft_apply
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ η : SchwartzMap (Fin m -> ℝ) ℂ)
          (z : ComplexChartSpace m) (t a : Fin m -> ℝ) :
          localDescentParamTestLeft φ ψ η ((z,t),a) =
            φ (z - realEmbed a) * η t * ψ (t + a)

      def localDescentParamTestRight
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ η : SchwartzMap (Fin m -> ℝ) ℂ) :
          SchwartzMap
            ((ComplexChartSpace m × (Fin m -> ℝ)) × (Fin m -> ℝ)) ℂ

      theorem localDescentParamTestRight_apply
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ η : SchwartzMap (Fin m -> ℝ) ℂ)
          (z : ComplexChartSpace m) (t a : Fin m -> ℝ) :
          localDescentParamTestRight φ ψ η ((z,t),a) =
            φ z * η (t - a) * ψ t

      theorem mixedRealFiberIntegralCLM_localDescentParamTestLeft
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ η : SchwartzMap (Fin m -> ℝ) ℂ) :
          mixedRealFiberIntegralCLM
              (localDescentParamTestLeft φ ψ η) =
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realConvolutionShearCLE m).symm)
              (schwartzTensorProduct₂ (realConvolutionTest φ ψ) η)

      theorem mixedRealFiberIntegralCLM_localDescentParamTestRight
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ η : SchwartzMap (Fin m -> ℝ) ℂ)
          (hη_norm : ∫ a : Fin m -> ℝ, η a = 1) :
          mixedRealFiberIntegralCLM
              (localDescentParamTestRight φ ψ η) =
            schwartzTensorProduct₂ φ ψ
      ```
      These definitions are genuine Schwartz tests, not placeholders.  Build
      the real two-parameter factors first:
      ```lean
      def realParamKernelLeft
          (ψ η : SchwartzMap (Fin m -> ℝ) ℂ) :
          SchwartzMap ((Fin m -> ℝ) × (Fin m -> ℝ)) ℂ

      theorem realParamKernelLeft_apply ... :
          realParamKernelLeft ψ η (t,a) = η t * ψ (t + a)

      def realParamKernelRight
          (ψ η : SchwartzMap (Fin m -> ℝ) ℂ) :
          SchwartzMap ((Fin m -> ℝ) × (Fin m -> ℝ)) ℂ

      theorem realParamKernelRight_apply ... :
          realParamKernelRight ψ η (t,a) = η (t - a) * ψ t
      ```
      `realParamKernelLeft` is
      `schwartzExternalProduct η ψ` precomposed with the real-linear
      automorphism `(t,a) ↦ (t,t+a)`.  `realParamKernelRight` is the same
      external product precomposed with `(t,a) ↦ (t-a,t)`.  Both maps are
      continuous linear equivalences, so the construction uses
      `SchwartzMap.compCLMOfContinuousLinearEquiv`, not an ad hoc smoothness
      proof.

      Then define `localDescentParamTestLeft` as the external product of `φ`
      and `realParamKernelLeft ψ η`, precomposed by the continuous linear
      equivalence
      ```
      ((z,t),a) ↦ (z - realEmbed a, (t,a)).
      ```
      Define `localDescentParamTestRight` as the external product of `φ` and
      `realParamKernelRight ψ η`, precomposed by
      ```
      ((z,t),a) ↦ (z, (t,a)).
      ```
      The displayed `*_apply` theorems follow by `simp` from these four
      equivalence formulas, `realEmbed`, and `schwartzExternalProduct`.

      The two mixed-fiber integral identities are pointwise.
      For the left test, at `(z,t)`:
      ```
      ∫ a, φ (z - realEmbed a) * η t * ψ (t + a)
        = η t * ∫ b, φ (z + realEmbed t - realEmbed b) * ψ b
        = ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realConvolutionShearCLE m).symm)
            (schwartzTensorProduct₂ (realConvolutionTest φ ψ) η)) (z,t).
      ```
      The change of variables is `b = t + a`, using translation invariance of
      Lebesgue measure on `Fin m -> ℝ`; the last equality is
      `realConvolutionTest_apply` and
      `realConvolutionShearCLE_symm_apply`.
      For the right test:
      ```
      ∫ a, φ z * η (t - a) * ψ t
        = φ z * ψ t * ∫ u, η u
        = φ z * ψ t,
      ```
      using the measure-preserving affine map `u = t - a` and `hη_norm`.
      No density or quotient theorem is used in these two identities; they are
      direct scalar change-of-variables calculations.

   5. Prove
      `shearedProductKernelFunctional_localQuotient_of_productCovariant`.  Let
      ```
      F =
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realConvolutionShearCLE m)) (schwartzTensorProduct₂ φ ψ)
      G = schwartzTensorProduct₂ (realConvolutionTest φ ψ) η.
      ```
      Then `complexRealFiberIntegral F = complexRealFiberIntegral G`: the
      left side is `realConvolutionTest φ ψ` by definition, while the right
      side is `(∫ t, η t) • realConvolutionTest φ ψ`, hence the same test by
      `hη_norm` and `complexRealFiberIntegral_schwartzTensorProduct₂`.
      Moreover
      ```
      T F = K (schwartzTensorProduct₂ φ ψ)
      T G = Hdist (realConvolutionTest φ ψ).
      ```
      To compare `T F` and `T G`, use
      `A = localDescentParamTestLeft φ ψ η` and
      `B = localDescentParamTestRight φ ψ η`.  Their last-fiber evaluations are
      ```
      A a =
        schwartzTensorProduct₂
          (complexTranslateSchwartz (-a) φ)
          (η • translateSchwartz a ψ)
      B a =
        schwartzTensorProduct₂ φ
          (translateSchwartz (-a) (η • translateSchwartz a ψ)).
      ```
      The theorems from Step 4 give
      `K (mixedRealFiberIntegralCLM A) = T G` and
      `K (mixedRealFiberIntegralCLM B) = T F`.

      Applying the scalarization theorem from Step 3 with `L = K` reduces the
      desired equality to
      ```
      ∫ a, K (schwartzPartialEval₂CLM a A)
        =
      ∫ a, K (schwartzPartialEval₂CLM a B),
      ```
      an equality of ordinary complex integrals.  The scalar integrands are
      continuous by continuity of `a ↦ schwartzPartialEval₂CLM a A`,
      `a ↦ schwartzPartialEval₂CLM a B`, and `K`.  They are integrable by the
      finite-seminorm construction of `mixedRealFiberIntegralScalarCLM`; in
      this local application they are in fact compactly parameter-supported.
      If `schwartzPartialEval₂CLM a A` or
      `schwartzPartialEval₂CLM a B` is nonzero, the displayed formulas for the
      tests give real support points in `tsupport η` and `tsupport ψ`, hence
      `‖a‖ ≤ r + rη`.  Thus outside the closed ball of radius `r + rη` both
      scalar integrands vanish.  It remains only to prove pointwise equality
      inside that ball, which is exactly the local covariance call in Step 6.
   6. In the local quotient proof, the only translated product tensors that
      occur have real-kernel factor
      `κ a := SchwartzMap.smulLeftCLM ℂ (η : (Fin m -> ℝ) -> ℂ)
        (translateSchwartz a ψ)`.
      If `κ a = 0`, the covariance identity for that parameter is trivial.
      Otherwise choose an ordinary support point of `κ a`, hence a point
      `t ∈ tsupport (κ a)`.  The checked
      `SchwartzMap.tsupport_smulLeftCLM_subset` gives
      `t ∈ tsupport η` and
      `t ∈ tsupport (translateSchwartz a ψ)`, and
      `tsupport_comp_subset_preimage` for the real translation gives
      `t + a ∈ tsupport ψ`.  Therefore
      `‖a‖ = ‖(t + a) - t‖ ≤ r + rη`.  This bound gives:
      - `SupportsInOpen φ Ucov`, from `hφ` and `hmargin` with translation `0`
        using `0 ≤ r + rη`;
      - `SupportsInOpen (complexTranslateSchwartz (-a) φ) Ucov`, because every
        support point has the form `u + realEmbed a` with `u ∈ Udesc`, and
        the just-proved `‖a‖ ≤ r + rη` lets `hmargin u hu a` place it in
        `Ucov`; the compact-support part is supplied by
        `SupportsInOpen.complexTranslateSchwartz_of_image_subset`;
      - `KernelSupportWithin (κ a) (r + rη)`, because support of `κ a` is
        contained in `tsupport η`, then enlarge radius `rη ≤ r + rη` using
        `hr_nonneg`;
      - `KernelSupportWithin (translateSchwartz (-a) (κ a)) (r + rη)`, from
        the pointwise formula
        `(translateSchwartz (-a) (κ a)) x = η (x - a) * ψ x`; after rewriting
        the translated factor as multiplication by `ψ`, the checked
        `SchwartzMap.tsupport_smulLeftCLM_subset` puts the topological support
        inside `tsupport ψ`, then enlarge radius `r ≤ r + rη` using
        `hrη_nonneg`.
      Therefore `hcov (-a)` applies and gives
      ```
      K (schwartzTensorProduct₂ (complexTranslateSchwartz (-a) φ) (κ a))
        =
      K (schwartzTensorProduct₂ φ (translateSchwartz (-a) (κ a))).
      ```
      These scalar covariance equalities are the local replacement for global
      fiber invariance inside the scalarized parameter integral.  The
      normalized cutoff identity is used only through the checked
      `complexRealFiberIntegral_schwartzTensorProduct₂`/pointwise
      `mixedRealFiberIntegralCLM` calculations above, not as a
      `SchwartzMap`-valued Bochner average.
   7. `translationCovariantProductKernel_descends_local` now simply packages
      `Hdist` and calls
      `shearedProductKernelFunctional_localQuotient_of_productCovariant` for
      every product test `φ, ψ` supported in `Udesc` and radius `r`.  The
      result is the exact local product-test descent identity needed by the
      recovery consumer.  No density theorem, no arbitrary-test global
      quotient, and no unsupported Schwartz-valued Bochner integral is invoked.

13. Once the local product-test descent identity exists, local
   distributional holomorphy and pointwise recovery are separate checked-style
   consumers, not part of the descent theorem itself:

   ```lean
   theorem translationCovariantKernel_distributionalHolomorphic_local
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Udesc : Set (ComplexChartSpace m)) {ι : Type*} {l : Filter ι}
       [NeBot l]
       (ψι : ι -> SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_support : ∀ᶠ i in l, KernelSupportWithin (ψι i) r)
       (hψ_approx :
         ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
           Tendsto (fun i => realConvolutionTest θ (ψι i)) l (nhds θ))
       (hdesc_local :
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Udesc ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               Hdist (realConvolutionTest φ ψ))
       (hK_dbar_zero :
         ∀ j φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Udesc ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0) :
       IsDistributionalHolomorphicOn Hdist Udesc
   ```

   This is the checked proof of
   `translationCovariantKernel_distributionalHolomorphic` with the single
   global `hdesc` call replaced by `hdesc_local θ (ψι i) (hφ.dbar j)`.
   Because the local package separates the product-kernel representation domain
   from the holomorphy domain, the `hK_dbar_zero` input is supplied by the
   following localized variant of the checked
   `regularizedEnvelope_productKernel_dbar_eq_zero`:

   ```lean
   theorem regularizedEnvelope_productKernel_dbar_eq_zero_local
       {r : ℝ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Gchart : SchwartzMap (Fin m -> ℝ) ℂ ->
         ComplexChartSpace m -> ℂ)
       (Udesc Ucov U0 : Set (ComplexChartSpace m))
       (hUdesc_open : IsOpen Udesc)
       (hdesc_cov : Udesc ⊆ Ucov)
       (hcov_window : Ucov ⊆ U0)
       (hG_holo :
         ∀ ψ, KernelSupportWithin ψ r ->
           DifferentiableOn ℂ (Gchart ψ) U0)
       (hK_rep :
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucov ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               ∫ z : ComplexChartSpace m, Gchart ψ z * φ z)
       (j : Fin m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Udesc)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ : KernelSupportWithin ψ r) :
       K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0
   ```

   Proof transcript: first build
   `hdbar_cov : SupportsInOpen (dbarSchwartzCLM j φ : _ -> ℂ) Ucov` from
   `hφ.dbar j` by keeping the same compact-support proof and composing its
   `tsupport` inclusion with `hdesc_cov`.  Use `hK_rep` with `hdbar_cov` to
   rewrite the product kernel as the all-space integral of
   `Gchart ψ * dbarSchwartzCLM j φ`.  Then apply
   `integral_holomorphic_mul_dbarSchwartz_eq_zero` on the open set `Udesc`,
   with holomorphy
   `(hG_holo ψ hψ).mono (hdesc_cov.trans hcov_window)`, and the original
   `hφ`.  The result is exactly the zero needed by the localized
   distributional-holomorphy theorem.

   ```lean
   theorem regularizedEnvelope_pointwiseRepresentation_of_localProductKernel
       {r : ℝ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Gchart : SchwartzMap (Fin m -> ℝ) ℂ ->
         ComplexChartSpace m -> ℂ)
       (H : ComplexChartSpace m -> ℂ)
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (Ucore Udesc Ucov U0 : Set (ComplexChartSpace m))
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hUcore_open : IsOpen Ucore)
       (hUdesc_open : IsOpen Udesc)
       (hcore_desc : Ucore ⊆ Udesc)
       (hdesc_cov : Udesc ⊆ Ucov)
       (hcov_window : Ucov ⊆ U0)
       (hmargin_core :
         ∀ z ∈ Ucore, ∀ t : Fin m -> ℝ, ‖t‖ ≤ r ->
           z + realEmbed t ∈ Udesc)
       (hψ_support : KernelSupportWithin ψ r)
       (hG_holo : DifferentiableOn ℂ (Gchart ψ) U0)
       (hH_holo : DifferentiableOn ℂ H Udesc)
       (hRep : RepresentsDistributionOnComplexDomain Hdist H Udesc)
       (hdesc_local :
         ∀ φ η,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Udesc ->
           KernelSupportWithin η r ->
             K (schwartzTensorProduct₂ φ η) =
               Hdist (realConvolutionTest φ η))
       (hK_rep :
         ∀ φ η,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucov ->
           KernelSupportWithin η r ->
             K (schwartzTensorProduct₂ φ η) =
               ∫ z : ComplexChartSpace m, Gchart η z * φ z) :
       ∀ z ∈ Ucore,
         Gchart ψ z =
           ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t

   theorem regularizedEnvelope_chartEnvelope_from_localProductKernel
       {r : ℝ}
       (hm : 0 < m)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Gchart : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
       (Ucore Udesc Ucov U0 DplusSmall DminusSmall :
         Set (ComplexChartSpace m))
       (Fplus Fminus : ComplexChartSpace m -> ℂ)
       (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
       (hUcore_open : IsOpen Ucore)
       (hUdesc_open : IsOpen Udesc)
       (hU0_open : IsOpen U0)
       (hcore_desc : Ucore ⊆ Udesc)
       (hdesc_cov : Udesc ⊆ Ucov)
       (hcov_window : Ucov ⊆ U0)
       (hmargin_core :
         ∀ z ∈ Ucore, ∀ t : Fin m -> ℝ, ‖t‖ ≤ r ->
           z + realEmbed t ∈ Udesc)
       (hG_holo : ∀ ψ, KernelSupportWithin ψ r ->
         DifferentiableOn ℂ (Gchart ψ) U0)
       (hK_rep :
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucov ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               ∫ z : ComplexChartSpace m, Gchart ψ z * φ z)
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (hdesc_local :
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Udesc ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               Hdist (realConvolutionTest φ ψ))
       (hCR : IsDistributionalHolomorphicOn Hdist Udesc)
       (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
       (hψ_real : ∀ n t, (ψn n t).im = 0)
       (hψ_norm : ∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1)
       (hψ_support_shrink :
         ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ)))
       (hψ_support_r : ∀ n, KernelSupportWithin (ψn n) r)
       (hG_plus :
         ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DplusSmall,
           Gchart (ψn n) z = realMollifyLocal Fplus (ψn n) z)
       (hG_minus :
         ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DminusSmall,
           Gchart (ψn n) z = realMollifyLocal Fminus (ψn n) z)
       (happrox_plus :
         ∀ z ∈ Ucore ∩ DplusSmall,
           Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
             atTop (nhds (Fplus z)))
       (happrox_minus :
         ∀ z ∈ Ucore ∩ DminusSmall,
           Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
             atTop (nhds (Fminus z))) :
       ∃ H : ComplexChartSpace m -> ℂ,
         DifferentiableOn ℂ H Udesc ∧
         RepresentsDistributionOnComplexDomain Hdist H Udesc ∧
         (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
         (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z)
   ```

   The recovery theorem above **consumes** `hCR`; it does not silently prove
   distributional holomorphy.  The full local product-kernel route obtains
   `hCR` immediately before calling it by:
   1. applying `regularizedEnvelope_productKernel_dbar_eq_zero_local` with
      `Udesc ⊆ Ucov ⊆ U0` to prove the local product-kernel annihilates
      `dbarSchwartzCLM` product tests;
   2. applying `translationCovariantKernel_distributionalHolomorphic_local`
      to the local descent identity, the approximate-identity convergence
      `realConvolutionTest θ (ψι i) -> θ`, and the local `∂bar` zero theorem.
   Thus the CR regularity input is a checked-style theorem consumer with its
   own hypotheses, not a field hidden in a wrapper and not an additional
   assumption in the final SCV EOW assembly.

   Proof transcript for the local recovery consumer:

   1. Apply `distributionalHolomorphic_regular Hdist hm hUdesc_open hCR` to
      get `H`, holomorphic on `Udesc`, and its representing identity on tests
      supported in `Udesc`.
   2. First prove
      `regularizedEnvelope_pointwiseRepresentation_of_localProductKernel`.
      The proof is the checked pointwise-representation proof with three
      substitutions:
      - `Ucore` remains the pointwise domain;
      - `Udesc` is the representation domain for `Hdist` and the margin target
        for `realConvolutionTest`;
      - `Ucov` is only the product-kernel representation domain for `hK_rep`.

      For a test `φ` supported in `Ucore`, monotonicity gives support in
      `Udesc` and `Ucov` via `hcore_desc` and `hdesc_cov`; holomorphy of
      `Gchart ψ` on `U0` restricts to continuity on `Ucore` via
      `hcore_desc.trans (hdesc_cov.trans hcov_window)`.  The support margin
      `hmargin_core` gives
      `SupportsInOpen (realConvolutionTest φ ψ) Udesc`, so `hRep` applies on
      the correct domain.  The test-pairing chain is
      ```
      ∫ z, Gchart ψ z * φ z
        = K (schwartzTensorProduct₂ φ ψ)
        = Hdist (realConvolutionTest φ ψ)
        = ∫ y, H y * realConvolutionTest φ ψ y
        = ∫ z, (∫ t, H (z + realEmbed t) * ψ t) * φ z.
      ```
      The first equality uses `hK_rep` on `Ucov`; the second uses
      `hdesc_local` on `Udesc`; the third is `hRep`; the fourth is the checked
      Fubini/change-of-variables theorem
      `realConvolutionTest_pairing_eq_mollifier_pairing` with target `Udesc`.
      The fundamental-lemma endpoint
      `regularizedEnvelope_pointwise_eq_of_test_integral_eq` then gives the
      pointwise identity on `Ucore`.
   3. Apply this local pointwise theorem to every `ψn n`.  The hypotheses
      `hψ_support_r n` and `hG_holo (ψn n) (hψ_support_r n)` supply the
      kernel support and holomorphy inputs, and the common `hmargin_core`
      supplies the translate margin for all `n`.
   4. The checked kernel-limit proof
      `regularizedEnvelope_kernelLimit_from_representation` applies with
      `U0 := Udesc`, using the identities from step 3 together with
      `hψ_nonneg`, `hψ_real`, `hψ_norm`, and `hψ_support_shrink`.  It gives
      `Tendsto (fun n => Gchart (ψn n) z) atTop (nhds (H z))` for every
      `z ∈ Ucore`.
   5. Feed this kernel-limit statement, plus the explicit side-agreement
      hypotheses `hG_plus` and `hG_minus` and the real-mollifier
      approximate-identity limits `happrox_plus` and `happrox_minus`, into
      `regularizedEnvelope_deltaLimit_agreesOnWedges`.  The result is the
      displayed agreement of `H` with `Fplus` on
      `Ucore ∩ DplusSmall` and with `Fminus` on
      `Ucore ∩ DminusSmall`.

   This theorem is not a wrapper around
   `regularizedEnvelope_chartEnvelope_from_productKernel`.  It replaces the
   global covariance input by the local descent data above, keeps the
   holomorphy domain `Udesc` explicit, and uses `Ucore` only for the final
   pointwise and wedge-agreement conclusions.

   Lean extraction order for the local package:

   1. `exists_complexChart_schwartz_cutoff_eq_one_on_closedBall`: checked; the
      `ComplexChartSpace m` version of
      `exists_schwartz_cutoff_eq_one_on_closedBall`, built with
      `ContDiffBump`.  Output: a Schwartz multiplier equal to `1` on
      `closedBall 0 Rcov` and supported in `closedBall 0 Rcut`.
   1b. `SupportsInOpen.smulLeftCLM_eq_of_eq_one_on`: checked; removes the
       complex-chart cutoff on tests whose topological support lies in the
       declared support window.
   2. `schwartzPartialEval₁CLM`: checked; the continuous linear map
      `F ↦ (t ↦ F (z,t))`, built directly in the SCV layer from
      `SchwartzMap.compCLM` along the affine map `t ↦ (z,t)`, with checked
      apply and tensor-product theorems.  No Wightman partial-evaluation file
      is imported.
   2b. `schwartzPartialEval₁CLM_compactSeminormBound`: checked; the compact
       finite-seminorm estimate for `z ∈ closedBall 0 Rcut`, with exact
       witnesses `s' = s` and `C = 1`.
   2c. `schwartzPartialEval₁`, `schwartzPartialEval₁_tail_small`,
       `hasFDerivAt_iteratedFDeriv_partialEval₁_param`,
       `norm_fderiv_iteratedFDeriv_partialEval₁_param_le`, and
       `continuous_schwartzPartialEval₁`: checked SCV-local port of the
       Wightman `partialEval₂_tail_small` / `continuous_partialEval₂` proof
       with the product factors swapped.  The public
       `continuous_schwartzPartialEval₁CLM` theorem in
       `SCV/DistributionalEOWKernel.lean` is then proved by identifying
       `schwartzPartialEval₁CLM z F` with `schwartzPartialEval₁ F z`.  This is
       needed for the varying-slice continuity theorem and is proved without
       importing the Wightman partial-evaluation file.
   3. `regularizedLocalEOW_originalFamily_compactValueCLM`: checked; the compact
      uniform version of `regularizedEnvelope_valueCLM_of_cutoff` on
      `closedBall 0 Rcut`, with one finite Schwartz seminorm bound for all
      `z` in the compact chart support.
   4a. `KernelSupportWithin.mono` and
       `SchwartzMap.exists_schwartzCLM_finsetSeminormBound`: checked helper
       targets before the chart-kernel value theorem.  The first is closed-ball
       support monotonicity.  The second packages the
       `Seminorm.bound_of_continuous`/`Seminorm.isBounded_sup` argument that
       transports any finite output Schwartz seminorm through a continuous
       kernel-to-kernel Schwartz CLM.
   4b. `regularizedLocalEOW_chartKernelFamily_valueCLM`: checked substantive
      chart-kernel target; define
      `Lchart z = Lorig z ∘ localEOWRealLinearKernelPushforwardCLM ys hli ∘
      (χr • ·)`.  On `KernelSupportWithin ψ r`, remove the chart cutoff,
      push the cutoff kernel support to radius `A * rcut`, enlarge it to the
      chosen original identity radius `rψ`, remove the original-edge cutoff,
      and obtain `Lchart z ψ = Gchart ψ z`.  Its common finite-seminorm bound
      is the compact `Lorig` bound composed with the helper in 4a.
   5a. `continuous_chartKernelCutoffSlice`,
       `seminorm_translateSchwartz_uniformOn`,
       `continuousOn_realMollifyLocal_varyingKernel_of_fixedSupport`,
       `continuousOn_translateSchwartz_varyingKernel_of_fixedSupport`,
       `continuousOn_localRudinEnvelope_varyingKernel_of_bound`: checked in
       `SCV/VaryingKernelContinuity.lean`.  The checked
       `seminorm_translateSchwartz_uniformOn` uses real Schwartz seminorms and
       controls the output `k,l` seminorm by both the input `k,l` and `0,l`
       seminorms; that `0,l` term is mathematically necessary near the origin.
       The scalar evaluation and final-cutoff support targets
       `continuous_chartKernelCutoffSlice_eval` and
       `KernelSupportWithin.chartKernelCutoffSlice` are also checked in the
       same file; the support theorem qualifies
       `SCV.localEOWRealLinearKernelPushforwardCLM` because the theorem lives
       under the `KernelSupportWithin` namespace.  The same file also checks
       `KernelSupportWithin.eq_zero_of_not_mem_closedBall`, the pointwise
       zero-off-support fact needed by the variable-kernel compact-support
       hypotheses, and
       `continuousOn_localRudinBoundaryCLM_varyingKernel_of_fixedSupport`, the
       boundary-branch continuity component of the CLM boundary-data theorem.
       The same file now also checks the split moving-kernel side limits
       `tendsto_localRudinPlusBoundary_varyingKernel_of_clm`,
       `tendsto_localRudinMinusBoundary_varyingKernel_of_clm`; their theorem
       surfaces correctly consume vector-valued translated-kernel continuity
       `hkernel_cont`, not merely the scalar `Tchart`-applied boundary
       continuity.  The same file also checks
       `localRudin_varyingKernel_boundaryData_of_clm`, which derives
       `hkernel_cont`, returns scalar `hbv_cont`, and bundles the two side
       limits.  The remaining
       continuity-support targets before the mixed pairing CLM are
       `exists_bound_localRudinIntegrand_varyingKernel`,
       `continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand`: before
       defining the mixed integral, prove continuity of the actual cutoff
       envelope integrand
       `z ↦ χU z * Gorig (χψ • P (χr • schwartzPartialEval₁CLM z F)) z`
       on `closedBall 0 Rcut`.  This closes the measurability gap that would
       arise from integrating a choice-valued `z ↦ Lchart z`.  The variable
       real-mollifier helper must include the open original side domain, and
       the parametric Rudin bound must keep the inner Rudin side domains
       `Dplus`/`Dminus` separate from the original holomorphy domains
       `Ωplus`/`Ωminus`.  The side-boundary limits in the parametric bound
       must be varying-kernel CLM limits, proved with
       `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`, not merely
       fixed-kernel boundary limits.
   5b. `regularizedLocalEOW_pairingCLM_of_fixedWindow`: define `K` by the
       actual cutoff envelope set integral, use `Lchart` only for the
       finite-seminorm bound, and prove the supported product-test
       representation by removing `χU`, `χr`, and `χψ`.
   6. `exists_positive_imag_mem_localEOWShiftedWindow_of_norm_lt`: checked;
      supplies the small-shift seed lemma for shifted overlaps.
   6b. `norm_realEmbed_eq`: checked in
       `SCV/DistributionalEOWApproxIdentity.lean`; equality of the finite sup
       norms under `realEmbed`.  This turns the two complex-chart support
       points `u` and `u - realEmbed a` into the real shift bound
       `‖a‖ < δ / 4`.
   6c. `tsupport_subset_preimage_tsupport_complexTranslateSchwartz`: prove the
       topological-support transport lemma for the inverse complex-chart
       translation.  This is what turns shifted support of
       `complexTranslateSchwartz a φ` into the all-`tsupport φ` hypothesis
       needed by local change of variables.
   6d. `integral_mul_complexTranslateSchwartz_eq_shift_of_support`: prove the
       support-localized all-space change-of-variables lemma for locally
       continuous scalar kernels multiplied by a translated Schwartz test.
   7. `regularizedLocalEOW_pairingCLM_localCovariant`: prove
      `ProductKernelRealTranslationCovariantLocal K Ucov r`.
   8a. `schwartzTensorProduct₂CLMLeft`, `schwartzPartialEval₂CLM`,
       `mixedRealFiberIntegralCLM`,
       `mixedBaseFiberTensor`, `mixedBaseFiberProductTensorDense_all`,
       `mixedRealFiberIntegralScalarCLM`,
       `mixedRealFiberIntegralScalarCLM_apply`,
       `mixedRealFiberIntegralScalarCLM_eq_comp_mixedRealFiberIntegralCLM`,
       `continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral`,
       `realParamKernelLeft`, `realParamKernelLeft_apply`,
       `realParamKernelRight`, `realParamKernelRight_apply`,
       `SupportsInOpen.complexTranslateSchwartz_of_image_subset` (checked in
       `SCV/DistributionalEOWSupport.lean`), and
       `shearedProductKernelFunctional_localQuotient_of_productCovariant`:
       local product-test descent infrastructure.  The quotient theorem is the
       scalarized/local fiber-integral replacement for the invalid
       `SchwartzMap`-valued averaging route; it replays the checked
       real-fiber integral estimates on the mixed base, proves scalarization
       by a scalar CLM plus dense split product tensors, and guards every
       covariance use by the local support window.
   8b. `translationCovariantProductKernel_descends_local`: prove the local
       product-test descent identity by packaging
       `complexRealFiberTranslationDescentCLM (shearedProductKernelFunctional K)
       η` and applying the local quotient theorem.  The normalized cutoff is
       used through `complexRealFiberIntegral_schwartzTensorProduct₂`, not by
       forming an unsupported `SchwartzMap`-valued Bochner integral.
   9. `regularizedEnvelope_productKernel_dbar_eq_zero_local`: checked in
      `SCV/DistributionalEOWRepresentative.lean`; localizes the checked
      `∂bar` product-kernel annihilation theorem to the separated domains
      `Udesc ⊆ Ucov ⊆ U0`.
   10. `translationCovariantKernel_distributionalHolomorphic_local`: checked
      in `SCV/DistributionalEOWRepresentative.lean`; localizes the checked
      distributional-holomorphy passage, consuming the local `∂bar` zero
      theorem and the local descent identity.
   11. `regularizedEnvelope_pointwiseRepresentation_of_localProductKernel` and
       then `regularizedEnvelope_chartEnvelope_from_localProductKernel`: reuse
       the checked pointwise representation and delta-limit proof with
       `Ucore ⊂ Udesc`.

Checked endpoint for the pointwise-representation bridge:

```lean
theorem regularizedEnvelope_pointwise_eq_of_test_integral_zero
    {m : ℕ}
    (Ucore : Set (ComplexChartSpace m))
    (Gψ Hψ : ComplexChartSpace m -> ℂ)
    (hUcore_open : IsOpen Ucore)
    (hG_cont : ContinuousOn Gψ Ucore)
    (hH_cont : ContinuousOn Hψ Ucore)
    (htest_zero :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
          (∫ z : ComplexChartSpace m, (Gψ z - Hψ z) * φ z) = 0) :
    ∀ z ∈ Ucore, Gψ z = Hψ z
```

This is the final fundamental-lemma step of pointwise representation.  For a
fixed smoothing kernel `ψ`, take

```lean
Hψ z = ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t.
```

The bridge theorem package is now checked.  The extra hypothesis is not
cosmetic: the pointwise representation requires a real-translation margin

```lean
∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m -> ℝ) -> ℂ),
  z + realEmbed t ∈ U0
```

or, for the final approximate-identity sequence, the uniform closed-ball
version

```lean
∀ z ∈ Ucore, ∀ t : Fin m -> ℝ, ‖t‖ ≤ r ->
  z + realEmbed t ∈ U0.
```

The weaker inclusion `Ucore ⊆ U0` is enough for the delta-limit estimate after
the pointwise representation is known, but it is not enough to justify
representing `Hdist (realConvolutionTest φ ψ)` by integration over `H` on
`U0`.

First, convert equality of all test pairings into pointwise equality.  This is
now checked in `SCV/DistributionalEOWKernelRecovery.lean`:

```lean
theorem regularizedEnvelope_pointwise_eq_of_test_integral_eq
    {m : ℕ}
    (Ucore : Set (ComplexChartSpace m))
    (Gψ Hψ : ComplexChartSpace m -> ℂ)
    (hUcore_open : IsOpen Ucore)
    (hG_cont : ContinuousOn Gψ Ucore)
    (hH_cont : ContinuousOn Hψ Ucore)
    (hG_int :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
          Integrable fun z : ComplexChartSpace m => Gψ z * φ z)
    (hH_int :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
          Integrable fun z : ComplexChartSpace m => Hψ z * φ z)
    (htest_eq :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
          (∫ z : ComplexChartSpace m, Gψ z * φ z) =
            ∫ z : ComplexChartSpace m, Hψ z * φ z) :
    ∀ z ∈ Ucore, Gψ z = Hψ z
```

Proof transcript: fix `φ` supported in `Ucore`.  Rewrite
`(Gψ z - Hψ z) * φ z` pointwise as
`Gψ z * φ z - Hψ z * φ z`; use `MeasureTheory.integral_sub` with `hG_int`
and `hH_int`; the hypothesis `htest_eq φ hφ` makes the result zero.  Then
apply `regularizedEnvelope_pointwise_eq_of_test_integral_zero`.

Second, prove the support theorem needed to apply
`RepresentsDistributionOnComplexDomain` to the convolution test.  This theorem
is now checked in `SCV/DistributionalEOWKernelRecovery.lean`:

```lean
theorem realConvolutionTest_supportsInOpen_of_translate_margin
    {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (Ucore U0 : Set (ComplexChartSpace m))
    (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore)
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ))
    (hmargin :
      ∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m -> ℝ) -> ℂ),
        z + realEmbed t ∈ U0) :
    SupportsInOpen
      (realConvolutionTest φ ψ : ComplexChartSpace m -> ℂ) U0
```

Proof transcript: let
`K = (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
  p.1 + realEmbed p.2) '' (tsupport φ ×ˢ tsupport ψ)`.
The product of the two topological supports is compact, hence `K` is compact
and closed.  If `y ∉ K`, then for every `t`, either
`t ∉ tsupport ψ` or `y - realEmbed t ∉ tsupport φ`; otherwise
`y = (y - realEmbed t) + realEmbed t` would lie in `K`.  Therefore the
integrand in `realConvolutionTest_apply` is identically zero at `y`, so the
ordinary support of `realConvolutionTest φ ψ` is contained in the closed
compact set `K`; `closure_minimal` then gives topological support contained in
`K`.  Finally, `hφ.2` and `hmargin` give `K ⊆ U0`.

Third, prove continuity of the recovered mollifier.  This theorem is now
checked in `SCV/DistributionalEOWKernelRecovery.lean`:

```lean
theorem continuousOn_realMollifyLocal_of_translate_margin
    {m : ℕ}
    (H : ComplexChartSpace m -> ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (Ucore U0 : Set (ComplexChartSpace m))
    (hU0_open : IsOpen U0)
    (hH_cont : ContinuousOn H U0)
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ))
    (hmargin :
      ∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m -> ℝ) -> ℂ),
        z + realEmbed t ∈ U0) :
    ContinuousOn (fun z : ComplexChartSpace m =>
      ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t) Ucore
```

Proof transcript: use Mathlib's
`MeasureTheory.continuousOn_integral_of_compact_support` with compact set
`tsupport ψ`.  The compact-support vanishing condition is
`image_eq_zero_of_notMem_tsupport`.  For continuity of the integrand on
`Ucore × univ`, split on `t ∈ tsupport ψ`: on support, compose `hH_cont` with
the continuous map `(z,t) ↦ z + realEmbed t` and use `hmargin`; off support,
`ψ` is eventually zero by `notMem_tsupport_iff_eventuallyEq`.

Fourth, prove the actual Fubini/change-of-variables identity.  This theorem is
now checked in `SCV/DistributionalEOWKernelRecovery.lean`:

```lean
theorem realConvolutionTest_pairing_eq_mollifier_pairing
    {m : ℕ}
    (H : ComplexChartSpace m -> ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (Ucore U0 : Set (ComplexChartSpace m))
    (hU0_open : IsOpen U0)
    (hH_cont : ContinuousOn H U0)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore)
    (hψ_compact : HasCompactSupport (ψ : (Fin m -> ℝ) -> ℂ))
    (hmargin :
      ∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m -> ℝ) -> ℂ),
        z + realEmbed t ∈ U0) :
    (∫ y : ComplexChartSpace m,
      H y * realConvolutionTest φ ψ y) =
      ∫ z : ComplexChartSpace m,
        (∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t) * φ z
```

Proof transcript: unfold `realConvolutionTest_apply`, expand the left side as
`∫ y, H y * ∫ t, φ (y - realEmbed t) * ψ t`.  Use compact support of
`φ` and `ψ` plus `hmargin` to prove the joint integrand has compact support
inside the compact image above, and is continuous by the same on/off-support
argument as the continuity theorem.  Apply
`MeasureTheory.integral_integral_swap_of_hasCompactSupport`.  For each fixed
`t`, use `integral_add_right_eq_self (realEmbed t)` on the complex chart to
rewrite the inner integral from `y` to `z + realEmbed t`.  Swap integrals
back, then pull the factor `φ z` outside the inner `t`-integral with
`MeasureTheory.integral_mul_left`/`integral_const_mul` and finish by pointwise
ring normalization.

Finally, the supplier consumed by the checked assembly theorem is itself
checked:

```lean
theorem regularizedEnvelope_pointwiseRepresentation_of_productKernel
    {m : ℕ} {r : ℝ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
    (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
    (H : ComplexChartSpace m -> ℂ)
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
    (Ucore U0 : Set (ComplexChartSpace m))
    (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
    (hUcore_open : IsOpen Ucore)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hmargin_r :
      ∀ z ∈ Ucore, ∀ t : Fin m -> ℝ, ‖t‖ ≤ r ->
        z + realEmbed t ∈ U0)
    (hψ_support : KernelSupportWithin ψ r)
    (hG_holo : DifferentiableOn ℂ (G ψ) U0)
    (hH_holo : DifferentiableOn ℂ H U0)
    (hRep : RepresentsDistributionOnComplexDomain Hdist H U0)
    (hdesc :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (η : SchwartzMap (Fin m -> ℝ) ℂ),
        K (schwartzTensorProduct₂ φ η) =
          Hdist (realConvolutionTest φ η))
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (η : SchwartzMap (Fin m -> ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
        KernelSupportWithin η r ->
          K (schwartzTensorProduct₂ φ η) =
            ∫ z : ComplexChartSpace m, G η z * φ z) :
    ∀ z ∈ Ucore,
      G ψ z = ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t
```

Proof transcript: define
`Hψ z = ∫ t, H (z + realEmbed t) * ψ t`.  Get
`hψ_compact` from `KernelSupportWithin_hasCompactSupport hψ_support` and the
pointwise margin from `hmargin_r` and `hψ_support`.  `G ψ` is continuous on
`Ucore` by `hG_holo.continuousOn.mono hcore_U0`; `Hψ` is continuous by
`continuousOn_realMollifyLocal_of_translate_margin`.  For any `φ` supported
in `Ucore`, use the support theorem to apply `hRep` to
`realConvolutionTest φ ψ`, compare `hK_rep φ ψ` with `hdesc φ ψ`, and then
rewrite the `H` side using
`realConvolutionTest_pairing_eq_mollifier_pairing`.  This gives the
`htest_eq` hypothesis for
`regularizedEnvelope_pointwise_eq_of_test_integral_eq`, which then gives the
desired pointwise representation.

Kernel-recovery implementation substrate:

1. Do **not** consume the QFT-facing axiom
   `Wightman.WightmanAxioms.schwartz_nuclear_extension` in this SCV theorem.
   The local distributional EOW theorem must remain QFT-free.  If the existing
   nuclear-space files are reused, the exported theorem should live in `SCV`
   with no Wightman, OS, field, or vacuum parameters.
2. The production file should introduce a pure theorem package, tentatively in
   `SCV/DistributionalEOWKernel.lean`:

   ```lean
   abbrev ComplexChartSpace (m : ℕ) := Fin m -> ℂ

   def SupportsInOpen
       {E : Type*} [TopologicalSpace E]
       (φ : E -> ℂ) (U : Set E) : Prop :=
     HasCompactSupport φ ∧ tsupport φ ⊆ U

   def complexRealDir {m : ℕ} (j : Fin m) : ComplexChartSpace m :=
     fun k => if k = j then 1 else 0

   def complexImagDir {m : ℕ} (j : Fin m) : ComplexChartSpace m :=
     fun k => if k = j then Complex.I else 0

   noncomputable def directionalDerivSchwartzCLM
       {m : ℕ} (v : ComplexChartSpace m) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ :=
     -- The Schwartz derivative CLM in the real direction `v`, where
     -- `ComplexChartSpace m` is regarded as a real normed vector space.
     LineDeriv.lineDerivOpCLM ℂ
       (SchwartzMap (ComplexChartSpace m) ℂ) v

   noncomputable def dbarSchwartzCLM
       {m : ℕ} (j : Fin m) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ :=
     (1 / 2 : ℂ) •
       (directionalDerivSchwartzCLM (complexRealDir j) +
         Complex.I • directionalDerivSchwartzCLM (complexImagDir j))

   def IsDistributionalHolomorphicOn
       {m : ℕ}
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (U : Set (ComplexChartSpace m)) : Prop :=
     ∀ j : Fin m,
       ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
         SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U ->
           T (dbarSchwartzCLM j φ) = 0

   def RepresentsDistributionOnComplexDomain
       {m : ℕ}
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (H : ComplexChartSpace m -> ℂ)
       (U : Set (ComplexChartSpace m)) : Prop :=
     ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
       SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U ->
         T φ = ∫ z : ComplexChartSpace m, H z * φ z

   noncomputable def complexTranslateSchwartz
       {m : ℕ} (a : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ :=
     -- `(complexTranslateSchwartz a φ) z = φ (z + realEmbed a)`,
     -- implemented by `SchwartzMap.compCLM` for the affine real translation.
     complexTranslateSchwartzCLM a φ

   noncomputable def schwartzTensorProduct₂
       {m : ℕ}
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ :=
     -- pointwise `(x,y) ↦ φ x * ψ y`, proved from product-space
     -- Schwartz seminorm estimates in `SCV/DistributionalEOWKernel.lean`.
     schwartzTensorProductRaw φ ψ

   -- Unimplemented theorem surface, not checked API.  The checked
   -- product-density/descent files currently provide uniqueness and descent
   -- from product tensors; they do not by themselves construct `K` from an
   -- arbitrary separately continuous bilinear family.
   theorem productKernel_from_continuous_bilinear_family
       {m : ℕ}
       (B : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         (SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)) :
       ∃! K :
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ, K (schwartzTensorProduct₂ φ ψ) = B φ ψ

   -- Unimplemented cutoff-existence theorem.  The checked support lemmas
   -- below show how such a Schwartz cutoff acts once supplied.
   lemma exists_schwartz_cutoff_eq_one_on_closedBall
       {m : ℕ} {r rLarge : ℝ} (hr : 0 < r) (hrLarge : r < rLarge) :
       ∃ χ : SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ t ∈ Metric.closedBall (0 : Fin m -> ℝ) r, χ t = 1) ∧
         tsupport (χ : (Fin m -> ℝ) -> ℂ) ⊆ Metric.closedBall 0 rLarge

   theorem KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall
       (χ : SchwartzMap (Fin m -> ℝ) ℂ)
       {ψ : SchwartzMap (Fin m -> ℝ) ℂ} {r : ℝ}
       (hχ_one :
         ∀ x : Fin m -> ℝ, x ∈ Metric.closedBall (0 : Fin m -> ℝ) r ->
           χ x = 1)
       (hψ : KernelSupportWithin ψ r) :
       SchwartzMap.smulLeftCLM ℂ (χ : (Fin m -> ℝ) -> ℂ) ψ = ψ

   lemma regularizedEnvelope_valueCLM_of_cutoff
       -- fixed cutoff, uniqueness of `Gψ`, slow-growth bounds, and explicit
       -- continuous-EOW construction
       :
       ∀ z ∈ U0,
         ∃ Lz : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
           ∀ ψ, KernelSupportWithin ψ r ->
             Lz ψ =
               G (SchwartzMap.smulLeftCLM ℂ
                    (χ : (Fin m -> ℝ) -> ℂ) ψ) z

   lemma regularizedEnvelope_covariance_of_uniqueness
       -- compare the translated-kernel envelope and translated envelope on a
       -- wedge piece, then use continuous-EOW uniqueness
       :
       ∀ a ψ z,
         KernelSupportWithin ψ r ->
         KernelSupportWithin (translateSchwartz a ψ) r ->
         z ∈ U0 -> z - realEmbed a ∈ U0 ->
           G (translateSchwartz a ψ) z = G ψ (z - realEmbed a)

   def ProductKernelRealTranslationCovariantGlobal
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
       Prop :=
     ∀ a φ ψ,
       K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
         K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))

   def ProductKernelRealTranslationCovariantLocal
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Ucore : Set (ComplexChartSpace m)) (r : ℝ) : Prop :=
     ∀ a φ ψ,
       SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
       SupportsInOpen
         (complexTranslateSchwartz a φ : ComplexChartSpace m -> ℂ) Ucore ->
       KernelSupportWithin ψ r ->
       KernelSupportWithin (translateSchwartz a ψ) r ->
         K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
           K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))

   def realConvolutionShearCLE (m : ℕ) :
       (ComplexChartSpace m × (Fin m -> ℝ)) ≃L[ℝ]
         (ComplexChartSpace m × (Fin m -> ℝ))

   noncomputable def complexRealFiberIntegralRaw
       {m : ℕ}
       {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
       [CompleteSpace V]
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
       (z : ComplexChartSpace m) : V :=
     ∫ t : Fin m -> ℝ, F (z, t)

   noncomputable def complexRealFiberIntegral
       {m : ℕ}
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ

   noncomputable def realConvolutionTest
       {m : ℕ}
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ :=
     complexRealFiberIntegral
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
         (realConvolutionShearCLE m)
         (schwartzTensorProduct₂ φ ψ))

   theorem realConvolutionTest_apply
       {m : ℕ}
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) :
       realConvolutionTest φ ψ z =
         ∫ t : Fin m -> ℝ, φ (z - realEmbed t) * ψ t

   theorem translationCovariantProductKernel_descends
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)

   theorem translationCovariantProductKernel_descends_local
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (Udesc Ucov : Set (ComplexChartSpace m)) (r rη : ℝ)
       (hr_nonneg : 0 ≤ r) (hrη_nonneg : 0 ≤ rη)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη_norm : ∫ t : Fin m -> ℝ, η t = 1)
       (hη_support : KernelSupportWithin η rη)
       (hmargin :
         ∀ z ∈ Udesc, ∀ t : Fin m -> ℝ, ‖t‖ ≤ r + rη ->
           z + realEmbed t ∈ Ucov)
       (hcov : ProductKernelRealTranslationCovariantLocal K Ucov (r + rη))
       :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Udesc ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               Hdist (realConvolutionTest φ ψ)

   theorem distributionalHolomorphic_regular
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (hU0_open : IsOpen U0)
       (hCR : IsDistributionalHolomorphicOn Hdist U0) :
       ∃ H : (Fin m -> ℂ) -> ℂ,
         DifferentiableOn ℂ H U0 ∧
         RepresentsDistributionOnComplexDomain Hdist H U0

   theorem regularizedEnvelope_kernelRecovery
       (Ucore U0 : Set (ComplexChartSpace m))
       (G : SchwartzMap (Fin m -> ℝ) ℂ -> (ComplexChartSpace m -> ℂ))
       (r : ℝ)
       (hU0_open : IsOpen U0)
       (hcore_margin : LocalTranslateMargin Ucore U0 r)
       (hG_holo :
         ∀ ψ, KernelSupportWithin ψ r ->
           DifferentiableOn ℂ (G ψ) U0)
       (hlin :
         ∀ z ∈ U0,
           ∃ Lz : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ,
             ∀ ψ, KernelSupportWithin ψ r -> Lz ψ = G ψ z)
       (hcov :
         ∀ a ψ z,
           KernelSupportWithin ψ r ->
           KernelSupportWithin (translateSchwartz a ψ) r ->
           z ∈ U0 -> z - realEmbed a ∈ U0 ->
             G (translateSchwartz a ψ) z = G ψ (z - realEmbed a)) :
       ∃ H : (Fin m -> ℂ) -> ℂ,
         DifferentiableOn ℂ H U0 ∧
         ∀ ψ, KernelSupportWithin ψ r ->
           ∀ z ∈ Ucore,
             G ψ z = ∫ t : Fin m -> ℝ, H (z + realEmbed t) * ψ t
   ```

   The derivative line is not pseudocode: the existing repo already uses
   `LineDeriv.lineDerivOpCLM` for Schwartz directional derivatives in
   `SCV/TubeBoundaryValueExistence.lean`.  The names
   `complexTranslateSchwartzCLM`, `schwartzTensorProduct₂`,
   `realConvolutionShearCLE`, `complexRealFiberIntegral`, and
   `realConvolutionTest` designate QFT-free construction lemmas on Schwartz
   space; they must be proved directly from `SchwartzMap.compCLM`, product-space
   tensor estimates, finite-dimensional fiber-integration estimates, and
   continuous-linear-equivalence pullback before the kernel-recovery theorem is
   attempted.
   Repo audit: there is already a generic-looking external tensor API
   `SchwartzMap.tensorProduct` with `SchwartzMap.tensorProduct_apply`, but it
   currently lives in `OSReconstruction/Wightman/SchwartzTensorProduct.lean`.
   The pure SCV file must not import that Wightman module.  The theorem-2 SCV
   file has therefore reproved the needed product-space Schwartz estimates
   locally and exposed only `schwartzTensorProduct₂`.
   For theorem 2, do not first broaden the public theorem surface to arbitrary
   finite-dimensional spaces.  The required public declaration is exactly the
   mixed chart product `ComplexChartSpace m × (Fin m -> ℝ)`.  Implement it by
   reproducing the split-variable seminorm proof locally in SCV: define a
   private projection-based product helper
   `schwartzTensorProductRaw φ ψ : SchwartzMap (E₁ × E₂) ℂ`, prove rapid decay
   from the Leibniz estimate
   `norm_iteratedFDeriv_mul_le`, the projection bounds
   `ContinuousLinearMap.norm_fst_le` and
   `ContinuousLinearMap.norm_snd_le`, and the pointwise seminorm bounds
   `SchwartzMap.le_seminorm`, then expose only
   `schwartzTensorProduct₂` for
   `E₁ = ComplexChartSpace m`, `E₂ = Fin m -> ℝ`.  This is now checked in
   `SCV/DistributionalEOWKernel.lean`, including the apply theorem
   `(schwartzTensorProduct₂ φ ψ) (z,t) = φ z * ψ t`.
   The real-direction shear is also checked there, with apply theorems for the
   forward and inverse maps.  The raw generic fiber integral
   `complexRealFiberIntegralRaw` is checked as a definition with its apply
   theorem, and the fixed-fiber Bochner integrability lemma
   `integrable_complexRealFiber` is checked.  The base-direction derivative
   field `baseFDerivSchwartz` and its apply theorem are also checked.  The
   zeroth-order weighted decay estimate
   `exists_norm_pow_mul_complexRealFiberIntegralRaw_le` is checked, as is the
   uniform integrable-bound lemma
   `exists_integrable_bound_baseFDerivSchwartz`.  The
   derivative-under-the-integral theorem
   `hasFDerivAt_complexRealFiberIntegralRaw` is checked, as are
   `fderiv_complexRealFiberIntegralRaw_eq`,
   `continuous_complexRealFiberIntegralRaw`,
   `contDiff_nat_complexRealFiberIntegralRaw`, and
   `contDiff_complexRealFiberIntegralRaw`.  The higher-order decay induction,
   `complexRealFiberIntegral`, `realConvolutionTest`, and the exact apply theorem
   `realConvolutionTest φ ψ z = ∫ t, φ (z - realEmbed t) * ψ t`
   are checked.  The finite-seminorm upgrade needed for a continuous-linear
   fiber-integral map is now also checked:
   `exists_seminorm_bound_complexRealFiberIntegralRaw_zero` is the generic
   zeroth-order estimate, `basePrecompCLM` and `baseFDerivSchwartzCLM` make the
   base derivative field a continuous complex-linear Schwartz-space map,
   `exists_seminorm_bound_baseFDerivSchwartz` controls its finite target
   seminorm suprema by finite source seminorms, and
   `exists_seminorm_bound_complexRealFiberIntegralRaw_deriv` is the full
   derivative-induction estimate used by `SchwartzMap.mkCLM`.
   Consequently `complexRealFiberIntegralCLM` and
   `complexRealFiberIntegralCLM_apply` are checked, and
   `boundaryProductKernel_from_complexRealFiberIntegralCLM` gives the chart
   product kernel
   `K F = Tchart (complexRealFiberIntegralCLM (shear F))` with product-test
   representation and real-translation covariance once a complex-chart
   distribution `Tchart` is available.  The theorem-2 supplier still has to
   construct the mixed product kernel from the regularized family
   `G ψ`; the fiber-integral theorem only removes the separate analytic
   obstruction in the chart-distribution case.

   The older fiber-descent primitives
   `complexRealFiberTranslateSchwartzCLM`,
   `complexRealFiberIntegral_fiberTranslate`,
   `complexRealFiberIntegral_schwartzTensorProduct₂`,
   `translateSchwartz_translateSchwartz`,
   `complexTranslateSchwartz_complexTranslateSchwartz`,
   `shearedProductKernelFunctional`, and
   `IsComplexRealFiberTranslationInvariant`, plus the sheared tensor identity
   `complexRealFiberTranslate_shearedTensor_eq`.  The mixed fiber quotient and
   normalized-cutoff factorization are now checked in
   `DistributionalEOWKernelTransport.lean` and
   `DistributionalEOWKernelFactorization.lean`; they remain useful background
   infrastructure but are no longer the active theorem-2 product-kernel route.

   The `realConvolutionTest` construction must be implemented by the following
   exact Lean route, not by an informal convolution placeholder.

   1. Define the real-direction shear as a real continuous linear equivalence:
      ```lean
      def realConvolutionShearCLE (m : ℕ) :
          (ComplexChartSpace m × (Fin m -> ℝ)) ≃L[ℝ]
            (ComplexChartSpace m × (Fin m -> ℝ))
      ```
      with pointwise equations
      ```lean
      realConvolutionShearCLE m (z, t) = (z - realEmbed t, t)
      (realConvolutionShearCLE m).symm (w, t) = (w + realEmbed t, t)
      ```
      The proof is elementary `ext`/`simp`: addition, subtraction, and real
      scalar multiplication commute with `realEmbed`.  This step is checked in
      `SCV/DistributionalEOWKernel.lean`.

   2. Define the raw fiber integral
      ```lean
      noncomputable def complexRealFiberIntegralRaw
          {m : ℕ}
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (z : ComplexChartSpace m) : V :=
        ∫ t : Fin m -> ℝ, F (z, t)
      ```
      The raw definition and its apply theorem are checked in
      `SCV/DistributionalEOWKernel.lean`; the remaining work is the analytic
      package proving that this raw function is Schwartz in the `V = ℂ` case.
      The generic codomain is necessary: the first derivative of a scalar-valued
      Schwartz map is valued in a continuous-linear-map space, and the induction
      for smoothness/decay integrates those derivative fields fiberwise.

   3. Prove pointwise integrability of every fiber:
      ```lean
      lemma integrable_complexRealFiber
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (z : ComplexChartSpace m) :
          Integrable (fun t : Fin m -> ℝ => F (z, t))
      ```
      This lemma is checked.  Its proof applies mathlib's
      `integrable_of_le_of_pow_mul_le` to
      `f t := F (z,t)` with the temperate-growth measure `volume` on
      `Fin m -> ℝ`.  The two required pointwise bounds are:
      ```lean
      ‖F (z,t)‖ ≤ SchwartzMap.seminorm ℝ 0 0 F
      ‖t‖ ^ volume.integrablePower * ‖F (z,t)‖ ≤
        SchwartzMap.seminorm ℝ volume.integrablePower 0 F
      ```
      The second bound uses `‖t‖ ≤ ‖(z,t)‖` for the product norm and
      `SchwartzMap.le_seminorm`.  This is the first place where the theorem-2
      docs must not hide a gap: the majorant is the standard temperate-measure
      radial tail supplied by mathlib, not a compact-support shortcut.

   4. Prove differentiation under the fiber integral:
      ```lean
      def baseFDerivSchwartz
          {m : ℕ}
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V) :
          SchwartzMap
            (ComplexChartSpace m × (Fin m -> ℝ))
            (ComplexChartSpace m ->L[ℝ] V) :=
        (SchwartzMap.postcompCLM
          ((ContinuousLinearMap.inl ℝ
            (ComplexChartSpace m) (Fin m -> ℝ)).precomp V))
          (SchwartzMap.fderivCLM ℝ
            (ComplexChartSpace m × (Fin m -> ℝ)) V F)

      theorem baseFDerivSchwartz_apply
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
          baseFDerivSchwartz F (z,t) =
            (fderiv ℝ
              (F :
                (ComplexChartSpace m × (Fin m -> ℝ)) -> V)
              (z,t)).comp
              (ContinuousLinearMap.inl ℝ
                (ComplexChartSpace m) (Fin m -> ℝ))

      lemma exists_integrable_bound_baseFDerivSchwartz
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V) :
          ∃ bound : (Fin m -> ℝ) -> ℝ,
            Integrable bound ∧
            ∀ z t, ‖baseFDerivSchwartz F (z,t)‖ ≤ bound t

      lemma hasFDerivAt_complexRealFiberIntegralRaw
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (z : ComplexChartSpace m) :
          HasFDerivAt (complexRealFiberIntegralRaw F)
            (complexRealFiberIntegralRaw (baseFDerivSchwartz F) z)
            z
      ```
      The definition and apply theorem for `baseFDerivSchwartz` are checked.
      The uniform bound `exists_integrable_bound_baseFDerivSchwartz` and the
      derivative theorem `hasFDerivAt_complexRealFiberIntegralRaw` are also
      checked.

      The product-inclusion CLM is exactly
      `ContinuousLinearMap.inl ℝ (ComplexChartSpace m) (Fin m -> ℝ)`, and
      `.precomp V` is the continuous linear map
      `(ComplexChartSpace m × (Fin m -> ℝ) ->L[ℝ] V) ->L[ℝ]
       (ComplexChartSpace m ->L[ℝ] V)`.

      The dominated-convergence call should instantiate
      `hasFDerivAt_integral_of_dominated_of_fderiv_le` with
      ```lean
      α  := Fin m -> ℝ
      H  := ComplexChartSpace m
      E  := V
      s  := Set.univ
      F  := fun z' t => F (z', t)
      F' := fun z' t => baseFDerivSchwartz F (z', t)
      ```
      The term `hF_int` is exactly `integrable_complexRealFiber F z`;
      `hF'_meas` follows from `integrable_complexRealFiber
      (baseFDerivSchwartz F) z`; `h_bound` and `bound_integrable` are supplied
      by `exists_integrable_bound_baseFDerivSchwartz`; and `h_diff` is the
      chain rule for the map `z' ↦ F (z',t)` through
      `ContinuousLinearMap.inl`.  This is the direct product-space analogue of
      `SliceIntegral.hasFDerivAt_sliceIntegralRaw`, but with the head/tail CLM
      replaced by `ContinuousLinearMap.inl`.

   5. Bootstrap to smoothness and decay:
      ```lean
      theorem fderiv_complexRealFiberIntegralRaw_eq
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V) :
          fderiv ℝ (complexRealFiberIntegralRaw F) =
            complexRealFiberIntegralRaw (baseFDerivSchwartz F)

      theorem contDiff_complexRealFiberIntegralRaw :
          ContDiff ℝ ⊤ (complexRealFiberIntegralRaw F)

      theorem exists_norm_pow_mul_complexRealFiberIntegralRaw_le
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) V)
          (k : ℕ) :
          ∃ C, ∀ z,
            ‖z‖ ^ k * ‖complexRealFiberIntegralRaw F z‖ ≤ C

      theorem decay_complexRealFiberIntegralRaw :
          ∀ k n, ∃ C, ∀ z,
            ‖z‖ ^ k *
              ‖iteratedFDeriv ℝ n
                (complexRealFiberIntegralRaw F) z‖ ≤ C
      ```
      The `fderiv` equality and smoothness theorems are checked.  The `fderiv`
      equality is `hasFDerivAt_complexRealFiberIntegralRaw F z` plus
      extensionality of `fderiv`.  Smoothness follows by the same successor step as
      `SliceIntegral.contDiff_nat_sliceIntegralRaw`: apply
      `contDiff_succ_iff_hasFDerivAt`, use the derivative theorem at every
      point, and recurse on `baseFDerivSchwartz F`, whose codomain is again a
      complete real normed space.

      Zeroth-order decay is not a new theorem: apply
      `integral_pow_mul_le_of_le_of_pow_mul_le` to the fiber function
      `t ↦ (‖z‖ ^ k : ℝ) • F (z,t)`.  The required two bounds are
      `‖z‖^k * ‖F(z,t)‖ ≤ seminorm k 0 F` and
      `‖t‖^volume.integrablePower * (‖z‖^k * ‖F(z,t)‖) ≤
       seminorm (k + volume.integrablePower) 0 F`, both from
      `‖z‖ ≤ ‖(z,t)‖`, `‖t‖ ≤ ‖(z,t)‖`, and
      `SchwartzMap.le_seminorm`.  This theorem is checked as
      `exists_norm_pow_mul_complexRealFiberIntegralRaw_le`.

      Higher-order decay is the induction used in
      `SliceIntegral.decay_sliceIntegralRaw`: for `n+1`, rewrite
      `iteratedFDeriv ℝ (n+1)` as `iteratedFDeriv ℝ n` of the `fderiv`,
      replace the `fderiv` by
      `complexRealFiberIntegralRaw (baseFDerivSchwartz F)` using
      `fderiv_complexRealFiberIntegralRaw_eq`, and apply the induction
      hypothesis to `baseFDerivSchwartz F`.

   6. Package the Schwartz map:
      ```lean
      noncomputable def complexRealFiberIntegral
          {m : ℕ}
          (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
          SchwartzMap (ComplexChartSpace m) ℂ where
        toFun := complexRealFiberIntegralRaw F
        smooth' := contDiff_complexRealFiberIntegralRaw F
        decay' := decay_complexRealFiberIntegralRaw F
      ```

   7. Define `realConvolutionTest` by pulling the tensor product through the
      shear and then integrating out the real fiber:
      ```lean
      noncomputable def realConvolutionTest
          {m : ℕ}
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
          SchwartzMap (ComplexChartSpace m) ℂ :=
        complexRealFiberIntegral
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realConvolutionShearCLE m))
            (schwartzTensorProduct₂ φ ψ))
      ```
      This definition and its apply theorem are checked in
      `SCV/DistributionalEOWKernel.lean`; the checked apply theorem reduces by
      simp to `∫ t, φ (z - realEmbed t) * ψ t`.  This fixes the sign convention
      used later in `ProductKernelRealTranslationCovariantGlobal` and its local
      cutoff corollary.

   8. Prove the exact translation identity consumed by the descent layer:
      ```lean
      theorem realConvolutionTest_complexTranslate_eq_translateSchwartz
          (a : Fin m -> ℝ)
          (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
          realConvolutionTest (complexTranslateSchwartz a φ) ψ =
            realConvolutionTest φ (translateSchwartz a ψ)
      ```
      The proof is the Haar/Lebesgue change of variables
      `t ↦ t + a` in the real fiber:
      rewrite the left integral by
      `integral_add_right_eq_self a`, then simplify
      `realEmbed (t + a) = realEmbed t + realEmbed a`.  This identity is not a
      wrapper: it is the sign-sensitive algebraic bridge that makes the
      covariance hypothesis
      `K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
       K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))`
      compatible with the quotient map
      `(φ, ψ) ↦ realConvolutionTest φ ψ`.
3. The proof transcript for `regularizedEnvelope_kernelRecovery` is now
   corrected to separate checked infrastructure from the remaining kernel
   theorem:
   build the cutoff CLM; prove value CLMs by continuous-EOW uniqueness; prove
   translation covariance by identity theorem/uniqueness; prove or consume the
   still-unchecked mixed two-space product-density/kernel-extension theorem;
   descend the translation-covariant product kernel by
   `translationCovariantProductKernel_descends`; use distributional
   Cauchy-Riemann regularity to get a holomorphic function; then apply the
   approximate identity theorem already present in
   `SCV/DistributionalUniqueness.lean`.

Detailed kernel-recovery proof transcript:

1. For compactly supported complex-chart tests `φ` with
   `tsupport φ ⊆ Ucore` and real kernels `ψ`, define the bilinear pairing
   ```lean
   regularizedEnvelopeBilinear φ ψ :=
     ∫ z : ComplexChartSpace m,
       G (SchwartzMap.smulLeftCLM ℂ
            (χ : (Fin m -> ℝ) -> ℂ) ψ) z * φ z
   ```
   The support condition on `φ` keeps the integral inside `Ucore`.
2. Prove `regularizedEnvelopeBilinear` is separately continuous:
   continuity in `ψ` uses `regularizedEnvelope_valueCLM_of_cutoff` plus
   integration against the compactly supported `φ`; continuity in `φ` uses
   holomorphy/continuity of `G (χr • ψ)` on compact subsets of `Ucore`.
3. Promote the separately continuous bilinear map to the product-kernel
   distribution:
   ```lean
   lemma regularizedEnvelope_productKernel_from_bilinear
       :
       ∃ K :
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) Ucore ->
             K (schwartzTensorProduct₂ φ ψ) =
               regularizedEnvelopeBilinear φ ψ
   ```
   Do not use the existing homogeneous `SchwartzMap.productTensor ![φ, ψ]`
   here: that API tensors functions on repeated copies of one space.  The EOW
   kernel is on `ComplexChartSpace m × (Fin m -> ℝ)`, so the implementation
   needs the two-space tensor product `schwartzTensorProduct₂`.
4. Prove product-kernel translation covariance.  The covariance identity for
   `G` gives, after changing variables in the compactly supported `φ`
   integral,
   ```lean
   K((complexTranslateSchwartz a φ)(z), ψ(t)) =
     K(φ(z), (translateSchwartz a ψ)(t))
   ```
   with the exact signs matching `translateSchwartz a ψ x = ψ (x + a)`.
5. Descend the product kernel to a diagonal complex distribution:
   ```lean
   def ProductKernelRealTranslationCovariantGlobal
       {m : ℕ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
       Prop :=
     ∀ a φ ψ,
       K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
         K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))

   theorem translationCovariantProductKernel_descends
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)
   ```
   Here `realConvolutionTest φ ψ` is the complex-chart Schwartz test
   `z ↦ ∫ t, φ (z - realEmbed t) * ψ t`.  This is the precise Lean object
   replacing the informal phrase "the kernel depends only on `z + t`."

   Historical note, now superseded by the local-descent route above: the
   support-restricted theorem must **not** be treated as a corollary of global
   descent after inserting a fixed complex-chart cutoff.  That cutoff breaks
   `ProductKernelRealTranslationCovariantGlobal`.  The active theorem-2 route
   proves only the product-test local descent needed by the regularized
   envelope, using the normalized fiber cutoff and local product covariance
   under explicit support/margin hypotheses.  The checked global descent theorem
   remains available only for a genuinely globally covariant kernel.

Exact product-kernel/descent subpackage:

1. The remaining product-kernel theorem is a mixed two-space Schwartz kernel
   theorem, not the QFT-facing Wightman axiom.  It is not currently checked in
   Lean; the checked product-density/descent files supply uniqueness/descent
   consequences, not this existence theorem:
   ```lean
   theorem productKernel_from_continuous_bilinear_family
       {m : ℕ}
       (B : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         (SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)) :
       ∃! K :
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ, K (schwartzTensorProduct₂ φ ψ) = B φ ψ
   ```
   The proof obligations are:
   - product tensors are dense in the mixed product Schwartz space;
   - the separately continuous bilinear map `B` gives a continuous functional
     on the completed projective tensor product;
   - nuclearity of the two Schwartz spaces identifies the completed projective
     tensor product with the concrete mixed product Schwartz space;
   - uniqueness is exactly agreement on `schwartzTensorProduct₂` product tests.
   This is the pure-SCV analogue of the existing Wightman
   `schwartz_nuclear_extension` axiom, but it must not import that axiom or be
   cited under a non-existent checked name.

2. Convert product covariance into fiber-translation invariance by shearing:
   ```lean
   noncomputable def complexRealFiberTranslateSchwartzCLM
       {m : ℕ} (a : Fin m -> ℝ) :
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ :=
     SchwartzMap.compSubConstCLM ℂ ((0 : ComplexChartSpace m), -a)

   theorem complexRealFiberTranslateSchwartzCLM_apply
       (a : Fin m -> ℝ)
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       complexRealFiberTranslateSchwartzCLM a F (z,t) = F (z, t + a)

   theorem complexRealFiberIntegral_fiberTranslate
       (a : Fin m -> ℝ)
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       complexRealFiberIntegral (complexRealFiberTranslateSchwartzCLM a F) =
         complexRealFiberIntegral F

   theorem complexRealFiberIntegral_schwartzTensorProduct₂
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       complexRealFiberIntegral (schwartzTensorProduct₂ φ ψ) =
         (∫ t : Fin m -> ℝ, ψ t) • φ

   theorem translateSchwartz_translateSchwartz
       (a b : Fin m -> ℝ) (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       translateSchwartz a (translateSchwartz b ψ) =
         translateSchwartz (a + b) ψ

   theorem complexTranslateSchwartz_complexTranslateSchwartz
       (a b : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       complexTranslateSchwartz a (complexTranslateSchwartz b φ) =
         complexTranslateSchwartz (a + b) φ

   noncomputable def shearedProductKernelFunctional
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ :=
     K.comp
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
         (realConvolutionShearCLE m).symm)

   def IsComplexRealFiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
       Prop :=
     ∀ a, T.comp (complexRealFiberTranslateSchwartzCLM a) = T

   theorem shearedProductKernel_fiberInvariant_of_productCovariant
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       IsComplexRealFiberTranslationInvariant
         (shearedProductKernelFunctional K)

   theorem complexRealFiberTranslate_shearedTensor_eq
       (a : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       complexRealFiberTranslateSchwartzCLM a
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m))
           (schwartzTensorProduct₂ φ ψ)) =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m))
           (schwartzTensorProduct₂
             (complexTranslateSchwartz (-a) φ)
             (translateSchwartz a ψ))
   ```
   The proof first checks the equality on tensors
   `(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m))
    (schwartzTensorProduct₂ φ ψ)`, where the already checked identity
   `realConvolutionTest_complexTranslate_eq_translateSchwartz` fixes the sign.
   Then uniqueness/density from the mixed product-tensor theorem promotes the
   tensor equality to CLM equality on the full mixed Schwartz space.

   The tensor-level covariance consequence is a separate checked theorem and
   should be implemented before the density theorem:

   ```lean
   theorem translateSchwartz_zero
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       translateSchwartz (0 : Fin m -> ℝ) ψ = ψ

   theorem shearedProductKernel_fiberTranslate_shearedTensor_eq_self_of_productCovariant
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K)
       (a : Fin m -> ℝ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       shearedProductKernelFunctional K
         (complexRealFiberTranslateSchwartzCLM a
           ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
               (realConvolutionShearCLE m))
             (schwartzTensorProduct₂ φ ψ))) =
       shearedProductKernelFunctional K
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m))
           (schwartzTensorProduct₂ φ ψ))
   ```

   Lean proof transcript:

   ```lean
   rw [complexRealFiberTranslate_shearedTensor_eq]
   simp [shearedProductKernelFunctional, ContinuousLinearMap.comp_apply]
   have h := hcov (-a) φ (translateSchwartz a ψ)
   simpa [translateSchwartz_translateSchwartz] using h
   ```

   This theorem is not a substitute for
   `shearedProductKernel_fiberInvariant_of_productCovariant`; it proves exactly
   the sign-sensitive covariance calculation on the product-tensor generators.
   The remaining step is density/uniqueness: if two continuous functionals on
   the mixed product Schwartz space agree on the span of these sheared product
   tensors, then they agree everywhere.  That is precisely where
   mixed product-tensor density/kernel-extension theorem or the equivalent
   dense-span theorem is needed.

   The dense-span promotion layer should be implemented as an honest
   conditional theorem before the full nuclear/kernel theorem is proved:

   ```lean
   def shearedProductTensorSet (m : ℕ) :
       Set (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :=
     {F | ∃ φ ψ,
       F =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (realConvolutionShearCLE m))
           (schwartzTensorProduct₂ φ ψ)}

   def shearedProductTensorSpan (m : ℕ) :
       Submodule ℂ
         (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :=
     Submodule.span ℂ (shearedProductTensorSet m)

   def ShearedProductTensorDense (m : ℕ) : Prop :=
     Dense ((shearedProductTensorSpan m : Set
       (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ))

   theorem shearedProductKernel_fiberInvariant_of_productCovariant_of_shearedProductTensorDense
       (hdense : ShearedProductTensorDense m)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       IsComplexRealFiberTranslationInvariant
         (shearedProductKernelFunctional K)
   ```

   Proof transcript:

   ```lean
   intro a
   let L₁ :=
     (shearedProductKernelFunctional K).comp
       (complexRealFiberTranslateSchwartzCLM a)
   let L₂ := shearedProductKernelFunctional K

   have hspan : ∀ F ∈ shearedProductTensorSpan m, L₁ F = L₂ F := by
     intro F hF
     refine Submodule.span_induction ?gen ?zero ?add ?smul hF
     · intro G hG
       rcases hG with ⟨φ, ψ, rfl⟩
       exact
         shearedProductKernel_fiberTranslate_shearedTensor_eq_self_of_productCovariant
           K hcov a φ ψ
     · simp [L₁, L₂]
     · intro u v _ _ hu hv
       simpa [L₁, L₂] using congrArg₂ (fun x y => x + y) hu hv
     · intro c u _ hu
       simpa [L₁, L₂] using congrArg (fun x => c • x) hu

   exact continuousLinearMap_eq_of_eq_on_dense L₁ L₂ hdense hspan
   ```

   Here `continuousLinearMap_eq_of_eq_on_dense` is the standard closed-equalizer
   argument: `{F | L₁ F = L₂ F}` is closed because both maps are continuous, it
   contains the dense sheared product-tensor span, hence it is all of the mixed
   Schwartz space.  This theorem shrinks the remaining analytic blocker to the
   single dense-span theorem `ShearedProductTensorDense m`.

   With the checked normalized fiber factorization, the corresponding
   conditional product-kernel descent is also 100% Lean-ready:

   ```lean
   theorem translationCovariantProductKernel_descends_of_shearedProductTensorDense
       (hdense : ShearedProductTensorDense m)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη : ∫ t : Fin m -> ℝ, η t = 1) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)
   ```

   Proof transcript:

   ```lean
   let T := shearedProductKernelFunctional K
   let Hdist := complexRealFiberTranslationDescentCLM T η
   have hT : IsComplexRealFiberTranslationInvariant T :=
     shearedProductKernel_fiberInvariant_of_productCovariant_of_shearedProductTensorDense
       hdense K hcov

   refine ⟨Hdist, ?_⟩
   intro φ ψ
   let F :=
     (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m))
       (schwartzTensorProduct₂ φ ψ)
   have hfac :=
     map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant
       T hT η hη F
   simpa [T, Hdist, F, realConvolutionTest, shearedProductKernelFunctional,
     ContinuousLinearMap.comp_apply] using hfac
   ```

   This is not the final unqualified
   `translationCovariantProductKernel_descends`: it retains the dense-span
   hypothesis explicitly.  The unqualified theorem follows only after proving
   `ShearedProductTensorDense m`, equivalently the mixed two-space
   mixed product-density/kernel-extension theorem.

   The conditional promotion/descent package is now checked in
   `SCV/DistributionalEOWProductKernel.lean`.  The remaining unproved theorem
   at this layer is exactly `ShearedProductTensorDense m` (or the stronger
   mixed product-density/kernel-extension theorem from which it follows).

   The checked coordinate-transport reduction is the pure shear part of that
   blocker.  It does **not** prove the Schwartz nuclear/product theorem; it
   proves that the sheared dense-span hypothesis follows from the standard
   unsheared product-tensor dense-span theorem by applying the checked shear
   continuous linear equivalence:

   ```lean
   def productTensorSet (m : ℕ) :
       Set (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :=
     {F | ∃ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
         (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
       F = schwartzTensorProduct₂ φ ψ}

   def productTensorSpan (m : ℕ) :
       Submodule ℂ
         (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :=
     Submodule.span ℂ (productTensorSet m)

   def ProductTensorDense (m : ℕ) : Prop :=
     Dense ((productTensorSpan m : Set
       (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)))
   ```

   The image comparison is exact:

   ```lean
   theorem shearedProductTensorSet_eq_image_productTensorSet :
       shearedProductTensorSet m =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (realConvolutionShearCLE m)) '' productTensorSet m

   theorem shearedProductTensorSpan_eq_productTensorSpan_map :
       shearedProductTensorSpan m =
         (productTensorSpan m).map
           ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m) :
               SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ]
                 SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ).toLinearMap)
   ```

   Lean proof transcript:

   ```lean
   -- set image
   ext F
   constructor
   · rintro ⟨φ, ψ, rfl⟩
     exact ⟨schwartzTensorProduct₂ φ ψ, ⟨φ, ψ, rfl⟩, rfl⟩
   · rintro ⟨G, ⟨φ, ψ, rfl⟩, rfl⟩
     exact ⟨φ, ψ, rfl⟩

   -- span image
   rw [shearedProductTensorSpan, productTensorSpan,
     shearedProductTensorSet_eq_image_productTensorSet,
     Submodule.map_span]
   rfl
   ```

   The density transport theorem is:

   ```lean
   theorem shearedProductTensorDense_of_productTensorDense
       (hdense : ProductTensorDense m) :
       ShearedProductTensorDense m
   ```

   Proof transcript:

   ```lean
   change Dense ((productTensorSpan m : Set
     (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ))) at hdense
   change Dense ((shearedProductTensorSpan m : Set
     (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)))
   rw [Submodule.dense_iff_topologicalClosure_eq_top] at hdense ⊢
   let shear : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ]
       SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ :=
     SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m)
   have hsurj : Function.Surjective shear := by
     intro F
     refine ⟨(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m).symm) F, ?_⟩
     change shear ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m).symm) F) = F
     exact compCLMOfContinuousLinearEquiv_symm_left_inv
       (e := realConvolutionShearCLE m) F
   have hmap_dense :
       (((productTensorSpan m).map shear.toLinearMap).topologicalClosure) = ⊤ := by
     exact hsurj.denseRange.topologicalClosure_map_submodule
       (f := shear) hdense
   rw [shearedProductTensorSpan_eq_productTensorSpan_map]
   exact hmap_dense
   ```

   The corresponding consumer-facing corollary can now expose the standard
   unsheared density blocker directly:

   ```lean
   theorem translationCovariantProductKernel_descends_of_productTensorDense
       (hdense : ProductTensorDense m)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη : ∫ t : Fin m -> ℝ, η t = 1) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)
   ```

   This is a strict reduction of the live blocker: after this checked transport
   step, the remaining mathematical theorem is the standard QFT-free statement
   `ProductTensorDense m`, equivalent to the mixed two-space Schwartz
   kernel/product-density theorem.  No Wightman import or existing Wightman
   nuclear axiom is used in this SCV layer.

   The remaining product-density theorem is now Lean-planned through the
   pure GaussianField product-Hermite density theorem, not through the Wightman
   nuclear axiom.  The route is:

   1. add a pure-SCV complex Schwartz decomposition file, with no Wightman
      imports:

      ```lean
      def SCV.schwartzRealPartCLM :
          SchwartzMap D ℂ ->L[ℝ] SchwartzMap D ℝ

      def SCV.schwartzImagPartCLM :
          SchwartzMap D ℂ ->L[ℝ] SchwartzMap D ℝ

      def SCV.schwartzOfRealCLM :
          SchwartzMap D ℝ ->L[ℝ] SchwartzMap D ℂ

      def SCV.complexSchwartzDecomposeCLE :
          SchwartzMap D ℂ ≃L[ℝ]
            (SchwartzMap D ℝ × SchwartzMap D ℝ)
      ```

      Proof transcript: copy the real/imaginary estimates from the local
      Wightman `ComplexSchwartz.lean` source pattern, but place them in
      `OSReconstruction/SCV/ComplexSchwartz.lean` importing only Mathlib/SCV
      prerequisites.  `realPartCLM` and `imagPartCLM` use
      `SchwartzMap.mkCLM` and
      `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`; `ofRealCLM` uses
      `Complex.ofRealLI.norm_iteratedFDeriv_comp_left`.  The equivalence is
      `ContinuousLinearEquiv.equivOfInverse` with pointwise proof
      `Complex.re_add_im`.

   2. flatten the mixed chart in the existing fiber-first order:

      ```lean
      def flatMixedCLM (m : ℕ) :
          SchwartzMap (Fin (m + m * 2) -> ℝ) ℂ ->L[ℂ]
            SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mixedChartFiberFirstCLE m)

      def flattenMixedFunctional (m : ℕ)
          (L : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ) :
          SchwartzMap (Fin (m + m * 2) -> ℝ) ℂ ->L[ℂ] ℂ :=
        L.comp (flatMixedCLM m)
      ```

      Here `mixedChartFiberFirstCLE m (z,t) = Fin.append t
      (complexChartRealFlattenCLE m z)`, already checked as
      `mixedChartFiberFirstCLE_apply_finAppend`.  This exact order matters:
      the first `m` real coordinates are the real fiber and the last `m*2`
      real coordinates are the real/imaginary complex-chart coordinates.

   3. expose the generic external product and prove the pointwise bridge from
      flat two-block products to mixed `schwartzTensorProduct₂` tests:

      ```lean
      def schwartzExternalProduct
          {E₁ E₂ : Type*}
          [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
          [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
          (φ : SchwartzMap E₁ ℂ) (ψ : SchwartzMap E₂ ℂ) :
          SchwartzMap (E₁ × E₂) ℂ

      def twoBlockProductSchwartz {m n : ℕ}
          (B : SchwartzMap (Fin m -> ℝ) ℂ)
          (A : SchwartzMap (Fin n -> ℝ) ℂ) :
          SchwartzMap (Fin (m + n) -> ℝ) ℂ :=
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finAppendCLE m n).symm)
          (schwartzExternalProduct B A)

      theorem flatTwoBlockProduct_eq_mixedProduct
          {m : ℕ}
          (A : SchwartzMap (Fin (m * 2) -> ℝ) ℂ)
          (B : SchwartzMap (Fin m -> ℝ) ℂ) :
          (flatMixedCLM m)
            (twoBlockProductSchwartz (m := m) (n := m * 2) B A) =
          schwartzTensorProduct₂
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (complexChartRealFlattenCLE m)) A)
            B
      ```

      `SCV.schwartzExternalProduct` is the checked local product estimate for
      `(x,y) ↦ φ x * ψ y`, and `twoBlockProductSchwartz B A` pulls it back to
      the flat append domain.  The bridge proof is pointwise:

      ```lean
      ext p
      rcases p with ⟨z,t⟩
      simp [flatMixedCLM, twoBlockProductSchwartz,
        schwartzTensorProduct₂_apply,
        mixedChartFiberFirstCLE_apply_finAppend,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      ring
      ```

      This slice is now implemented in
      `OSReconstruction/SCV/SchwartzExternalProduct.lean` and
      `OSReconstruction/SCV/ProductDensity.lean`.

   4. consume GaussianField's checked one-dimensional product-Hermite theorem
      on the flat real domain.  For `0 < m`, set `N := m + m * 2` and apply

      ```lean
      GaussianField.productHermite_schwartz_dense
        (D := ℝ) N (by omega)
      ```

      to any real continuous linear functional on
      `SchwartzMap (Fin N -> ℝ) ℝ`.  The hypothesis required by that theorem is
      vanishing on functions of the form
      `fun x => ∏ i : Fin N, DyninMityaginSpace.basis (ks i) (x i)`.
      To get that hypothesis from vanishing on mixed two-block product tests,
      split the one-dimensional Hermite product into the fiber block and the
      complex-chart block:

      ```lean
      have hsplit :
          fullHermiteProduct ks =
            twoBlockProductSchwartz
              (fiberHermiteProduct (fun i : Fin m => ks (Fin.castAdd (m*2) i)))
              (chartHermiteProduct
                (fun j : Fin (m*2) => ks (Fin.natAdd m j))) := by
        ext x
        rw [Fin.prod_univ_add]
        simp [twoBlockProductSchwartz, fiberHermiteProduct,
          chartHermiteProduct]
        ring
      ```

      `fiberHermiteProduct` and `chartHermiteProduct` are built by
      `GaussianField.schwartzProductTensor_schwartz (D := ℝ)` for the
      positive dimensions `m` and `m*2`; for `m = 0`, use the zero-dimensional
      base case below instead of this product-Hermite split.

   5. prove complex flat functional uniqueness from the real product-Hermite
      theorem:

      ```lean
      theorem flatComplexCLM_zero_of_zero_on_twoBlockProducts
          {m : ℕ} (hm : 0 < m)
          (Lflat : SchwartzMap (Fin (m + m * 2) -> ℝ) ℂ ->L[ℂ] ℂ)
          (hL : ∀ A B,
            Lflat (twoBlockProductSchwartz (m := m) (n := m * 2) B A) = 0) :
          Lflat = 0
      ```

      Proof transcript:

      ```lean
      let Lre : SchwartzMap (Fin (m + m*2) -> ℝ) ℝ ->L[ℝ] ℝ :=
        Complex.reCLM.comp
          ((Lflat.restrictScalars ℝ).comp SCV.schwartzOfRealCLM)
      let Lim : SchwartzMap (Fin (m + m*2) -> ℝ) ℝ ->L[ℝ] ℝ :=
        Complex.imCLM.comp
          ((Lflat.restrictScalars ℝ).comp SCV.schwartzOfRealCLM)
      have hre : Lre = 0 := by
        apply GaussianField.productHermite_schwartz_dense
        intro ks F hF
        -- split F into fiber/chart Hermite products and use hL
      have him : Lim = 0 := by
        apply GaussianField.productHermite_schwartz_dense
        intro ks F hF
        -- same split
      ext F
      let R := (SCV.complexSchwartzDecomposeCLE F).1
      let I := (SCV.complexSchwartzDecomposeCLE F).2
      have hdecomp :
          F = SCV.schwartzOfRealCLM R +
            (Complex.I : ℂ) • SCV.schwartzOfRealCLM I := by
        exact (SCV.complexSchwartzDecomposeCLE.symm_apply_apply F).symm
      have hR : Lflat (SCV.schwartzOfRealCLM R) = 0 := by
        apply Complex.ext
        · change Lre R = 0
          rw [hre]
          rfl
        · change Lim R = 0
          rw [him]
          rfl
      have hI : Lflat (SCV.schwartzOfRealCLM I) = 0 := by
        apply Complex.ext
        · change Lre I = 0
          rw [hre]
          rfl
        · change Lim I = 0
          rw [him]
          rfl
      rw [hdecomp, map_add, map_smul, hR, hI]
      simp
      ```

      The only nontrivial local lemma in this transcript is the `hsplit`
      block-product identity from step 4.

   6. pull the flat uniqueness back to the mixed chart:

      ```lean
      theorem mixedProductCLM_zero_of_zero_on_productTensor
          {m : ℕ} (hm : 0 < m)
          (L : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
          (hL : ∀ φ ψ, L (schwartzTensorProduct₂ φ ψ) = 0) :
          L = 0 := by
        have hflat :
            flattenMixedFunctional m L = 0 :=
          flatComplexCLM_zero_of_zero_on_twoBlockProducts hm
            (flattenMixedFunctional m L) (by
              intro A B
              rw [flatTwoBlockProduct_eq_mixedProduct]
              exact hL _ _)
        ext F
        have hinv :
            (flatMixedCLM m)
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (mixedChartFiberFirstCLE m).symm) F) = F :=
          compCLMOfContinuousLinearEquiv_symm_left_inv
            (e := mixedChartFiberFirstCLE m) F
        simpa [flattenMixedFunctional, hinv] using
          congrArg (fun T => T
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (mixedChartFiberFirstCLE m).symm) F)) hflat
      ```

   7. convert CLM uniqueness into topological density with the same
      Hahn-Banach argument already checked in
      `Wightman/Reconstruction/DenseCLM.lean`, but with the new pure-SCV
      uniqueness theorem:

      ```lean
      theorem ProductTensorDense_of_pos {m : ℕ} (hm : 0 < m) :
          ProductTensorDense m := by
        rw [ProductTensorDense,
          Submodule.dense_iff_topologicalClosure_eq_top]
        by_contra hM
        let M := productTensorSpan m
        obtain ⟨x, hx⟩ : ∃ x, x ∉ M.topologicalClosure := by
          -- same `Submodule.eq_top_iff'` contradiction as DenseCLM
        have hconv :
            Convex ℝ (M.topologicalClosure :
              Set (SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)) := by
          simpa using (M.topologicalClosure.restrictScalars ℝ).convex
        obtain ⟨f, u, hleft, hright⟩ :=
          RCLike.geometric_hahn_banach_closed_point
            (𝕜 := ℂ) (E := SchwartzMap
              (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
            (x := x) (s := (M.topologicalClosure : Set _))
            hconv M.isClosed_topologicalClosure hx
        -- scaling by real scalars and then by `Complex.I` proves
        -- `f` vanishes on `M.topologicalClosure`, hence on `M`.
        have hf_prod : ∀ φ ψ,
            f (schwartzTensorProduct₂ φ ψ) = 0 := by
          intro φ ψ
          exact hfS _ (Submodule.subset_span ⟨φ, ψ, rfl⟩)
        have hf_zero : f = 0 :=
          mixedProductCLM_zero_of_zero_on_productTensor hm f hf_prod
        -- contradict strict separation of x from M.topologicalClosure
      ```

   8. handle `m = 0` separately.  The domain
      `ComplexChartSpace 0 × (Fin 0 -> ℝ)` is a singleton finite-dimensional
      real normed space.  The proof should use evaluation at the unique point
      and the constant-one product tensor:

      ```lean
      theorem ProductTensorDense_zero : ProductTensorDense 0 := by
        -- show every Schwartz function on the singleton is a scalar multiple
        -- of `schwartzTensorProduct₂ 1 1`, hence lies in `productTensorSpan 0`

      theorem ProductTensorDense_all (m : ℕ) : ProductTensorDense m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact ProductTensorDense_zero
        · exact ProductTensorDense_of_pos hm
      ```

      This base case must be proved directly and should not be hidden behind
      GaussianField's positive-dimensional product theorem, whose hypotheses
      require `1 ≤ n`.

      This product-density route is now implemented in
      `OSReconstruction/SCV/ProductDensity.lean`.  The checked declarations are:

      ```lean
      def SCV.realHermiteBasis
      def SCV.singletonConstantSchwartz
      def SCV.flatMixedCLM
      def SCV.flattenMixedFunctional
      def SCV.twoBlockProductSchwartz
      theorem SCV.schwartzOfRealCLM_eq_twoBlockProduct_of_forall_append
      theorem SCV.exists_hermite_twoBlockFactors
      theorem SCV.flatTwoBlockProduct_eq_mixedProduct
      theorem SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts
      theorem SCV.mixedProductCLM_zero_of_zero_on_productTensor
      theorem SCV.ProductTensorDense_of_pos
      theorem SCV.ProductTensorDense_zero
      theorem SCV.ProductTensorDense_all
      theorem SCV.translationCovariantProductKernel_descends
      ```

      The proof uses `GaussianField.productHermite_schwartz_dense` only after
      building the exact Hermite split bridge from full flat products to the
      two mixed blocks, and it imports no Wightman nuclear theorem.

   Lean proof details for the checked first slice of this step:

   - `complexRealFiberTranslateSchwartzCLM` should not reprove a custom affine
     temperate-growth lemma.  Mathlib already supplies
     `SchwartzMap.compSubConstCLM`, so the fiber translation is the pullback by
     subtracting the constant `(0,-a)` in the product space:
     `F (p - (0,-a)) = F (z,t+a)`.
   - The apply theorem is one `simp` after unfolding the definition.
   - `complexRealFiberIntegral_fiberTranslate` is exactly invariance of
     Lebesgue/Haar measure under addition:
     ```lean
     ext z
     simp [complexRealFiberIntegral_apply]
     simpa using
       (MeasureTheory.integral_add_right_eq_self
         (μ := (volume : Measure (Fin m -> ℝ)))
         (fun t : Fin m -> ℝ => F (z,t)) a)
     ```
   - `complexRealFiberIntegral_schwartzTensorProduct₂` is the normalized-tensor
     computation used later to define the descent map with a fixed real cutoff:
     ```lean
     ext z
     simp [complexRealFiberIntegral_apply]
     calc
       ∫ t : Fin m -> ℝ, φ z * ψ t =
           φ z * ∫ t : Fin m -> ℝ, ψ t := by
         simpa [smul_eq_mul] using
           (integral_const_mul
             (μ := (volume : Measure (Fin m -> ℝ)))
             (r := φ z) (f := fun t : Fin m -> ℝ => ψ t))
       _ = (∫ t : Fin m -> ℝ, ψ t) * φ z := by ring
     ```

   The next tensor-level identity before the density promotion is:

   ```lean
   ext p
   rcases p with ⟨z, t⟩
   have hz : z - realEmbed (a + t) =
       z - realEmbed t + realEmbed (-a) := by
     ext i
     simp [realEmbed, sub_eq_add_neg, add_comm, add_left_comm]
   simp [hz, add_comm]
   ```

   This proves `complexRealFiberTranslate_shearedTensor_eq`.  It is the exact
   sign bridge used when applying `ProductKernelRealTranslationCovariantGlobal`
   with `-a` and then simplifying
   `translateSchwartz (-a) (translateSchwartz a ψ)` by
   `translateSchwartz_translateSchwartz`.

3. Prove the fiber-factorization theorem:
   ```lean
   noncomputable def schwartzTensorProduct₂CLMRight
       {m : ℕ} (η : SchwartzMap (Fin m -> ℝ) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ

   theorem schwartzTensorProduct₂CLMRight_apply
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       schwartzTensorProduct₂CLMRight η φ (z,t) = φ z * η t

   theorem map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hT : IsComplexRealFiberTranslationInvariant T)
       (F G : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (hFG : complexRealFiberIntegral F = complexRealFiberIntegral G) :
       T F = T G

   noncomputable def complexRealFiberTranslationDescentCLM
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (η : SchwartzMap (Fin m -> ℝ) ℂ) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ :=
     T.comp (schwartzTensorProduct₂CLMRight η)

   theorem map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hT : IsComplexRealFiberTranslationInvariant T)
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (hη : ∫ t : Fin m -> ℝ, η t = 1)
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       T F =
         complexRealFiberTranslationDescentCLM T η
           (complexRealFiberIntegral F)
   ```

   After `agents_chat.md` #1328, the hard quotient theorem
   `map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant` is
   checked in production.  Therefore the immediate Lean target is now the
   normalized-cutoff factorization above, not the full product-kernel descent.
   This is a genuine mathematical consumer of the quotient theorem: it
   constructs the descended continuous functional explicitly by embedding a
   complex-chart test `φ` as the product test `(z,t) ↦ φ z * η t` and uses
   `∫ η = 1` to identify its fiber integral with `φ`.

   The exact implementation route is:

   ```lean
   theorem schwartzTensorProduct₂_add_left
       (φ φ' : SchwartzMap (ComplexChartSpace m) ℂ)
       (η : SchwartzMap (Fin m -> ℝ) ℂ) :
       schwartzTensorProduct₂ (φ + φ') η =
         schwartzTensorProduct₂ φ η + schwartzTensorProduct₂ φ' η

   theorem schwartzTensorProduct₂_smul_left
       (c : ℂ) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (η : SchwartzMap (Fin m -> ℝ) ℂ) :
       schwartzTensorProduct₂ (c • φ) η =
         c • schwartzTensorProduct₂ φ η

   theorem schwartzTensorProduct₂CLMRight_eq
       (η : SchwartzMap (Fin m -> ℝ) ℂ)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       schwartzTensorProduct₂CLMRight η φ =
         schwartzTensorProduct₂ φ η
   ```

   The continuity proof for `schwartzTensorProduct₂CLMRight` is the product
   Schwartz seminorm estimate specialized to a fixed right factor.  For every
   output seminorm `(p,l)`, use

   ```lean
   s =
     (Finset.range (l + 1)).image (fun i => (p,i)) ∪
     (Finset.range (l + 1)).image (fun i => (0,i))

   C =
     (2 : ℝ) ^ p *
       ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
         (SchwartzMap.seminorm ℂ 0 (l - i) η +
          SchwartzMap.seminorm ℂ p (l - i) η)
   ```

   and prove

   ```lean
   ‖x‖ ^ p *
     ‖iteratedFDeriv ℝ l (fun y => φ y.1 * η y.2) x‖
     ≤ C * (s.sup
       (schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ)) φ.
   ```

   The derivative estimate is exactly the already checked product-rule
   estimate used in `schwartzTensorProductRaw`: split
   `‖x‖ ≤ ‖x.1‖ + ‖x.2‖`, use
   `(a+b)^p ≤ 2^p(a^p+b^p)`, bound the pullback derivatives through
   `ContinuousLinearMap.fst` and `ContinuousLinearMap.snd`, then absorb the
   variable `φ` seminorms into the finite sup over `s`.  The fixed `η`
   seminorms are part of `C`, so this gives a true continuous linear map, not
   a new assumption.

   The factorization proof then has no remaining mathematical gap:

   ```lean
   let G := schwartzTensorProduct₂ (complexRealFiberIntegral F) η
   have hFG :
       complexRealFiberIntegral F = complexRealFiberIntegral G := by
     rw [G, complexRealFiberIntegral_schwartzTensorProduct₂, hη, one_smul]

   have hquot :
       T F = T G :=
     map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
       T hT F G hFG

   calc
     T F = T G := hquot
     _ =
       complexRealFiberTranslationDescentCLM T η
         (complexRealFiberIntegral F) := by
       simp [complexRealFiberTranslationDescentCLM,
         schwartzTensorProduct₂CLMRight_eq, G]
   ```

   This package is now checked in
   `SCV/DistributionalEOWKernelFactorization.lean`, including the fixed-right
   tensor CLM, the explicit descended CLM, and
   `map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant`.

   What this does *not* yet prove: it does not derive
   `IsComplexRealFiberTranslationInvariant (shearedProductKernelFunctional K)`
   from `ProductKernelRealTranslationCovariantGlobal K` on all mixed tests.
   The existing covariance predicate is an equality on product tensors; to
  promote it to all of `SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ`
  still requires the mixed product-tensor density/kernel-extension theorem or
  an equivalent uniqueness principle.  That density theorem is the next
  mathematical blocker after the normalized factorization is checked.

   This is the mixed chart analogue of the already checked
   `HeadBlockTranslationInvariant` factorization theorem.  The proof cannot be
   a wrapper around the Wightman file because the domain is
   `ComplexChartSpace m × (Fin m -> ℝ)`, not a pure `Fin n -> ℝ` space.
   The mathematical proof is the same:
   - fiber-translation invariance kills every real-fiber directional derivative;
   - a Schwartz function with zero real-fiber integral is a finite sum of
     real-fiber directional derivatives, using the same zero-mean/antiderivative
     construction as `SliceIntegral.lean` iterated over the `Fin m -> ℝ`
     fiber;
   - therefore `T` depends only on `complexRealFiberIntegral F`;
   - a normalized real-fiber cutoff `η` gives an explicit descended CLM by
     tensoring the base test with `η`.

   Lean-ready extraction plan for this factorization:

   The proof should be moved into a pure SCV coordinate package rather than
   imported from `Wightman/Reconstruction/HeadBlockTranslationInvariant.lean`.
   The Wightman file is a source pattern, not a dependency, because importing it
   into SCV would reverse the project layering and would also pull the
   Wightman tensor-product package into the theorem-2 SCV layer.

   The exact SCV transport objects should be the following.  The complex
   coordinates are flattened as `Fin (m * 2)`, not `Fin (2 * m)`, because the
   existing Mathlib equivalence `finProdFinEquiv : Fin m × Fin 2 ≃ Fin
   (m * 2)` is the definitional order that makes the apply lemmas `rfl`/`simp`.
   Do not insert a commuted `2 * m` target unless a separate cast equivalence is
   mathematically needed downstream.

   ```lean
   def headBlockShift (m n : ℕ) (a : Fin m -> ℝ) : Fin (m + n) -> ℝ

   theorem headBlockShift_apply_head
       (a : Fin m -> ℝ) (i : Fin m) :
       headBlockShift m n a (Fin.castAdd n i) = a i

   theorem headBlockShift_apply_tail
       (a : Fin m -> ℝ) (i : Fin n) :
       headBlockShift m n a (Fin.natAdd m i) = 0

   private def realBlockUncurryLinearEquiv (n d : ℕ) (R : Type*)
       [CommSemiring R] :
       (Fin n -> Fin d -> R) ≃ₗ[R] (Fin n × Fin d -> R)

   private def realBlockFlattenLinearEquiv (n d : ℕ) (R : Type*)
       [CommSemiring R] :
       (Fin n -> Fin d -> R) ≃ₗ[R] (Fin (n * d) -> R)

   def realBlockFlattenCLE (n d : ℕ) :
       (Fin n -> Fin d -> ℝ) ≃L[ℝ] (Fin (n * d) -> ℝ)

   theorem realBlockFlattenCLE_apply
       (f : Fin n -> Fin d -> ℝ) (k : Fin (n * d)) :
       realBlockFlattenCLE n d f k =
         f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

   theorem realBlockFlattenCLE_symm_apply
       (w : Fin (n * d) -> ℝ) (i : Fin n) (j : Fin d) :
       (realBlockFlattenCLE n d).symm w i j =
         w (finProdFinEquiv (i, j))

   noncomputable def complexToFinTwoCLE : ℂ ≃L[ℝ] (Fin 2 -> ℝ)

   theorem complexToFinTwoCLE_apply_zero (z : ℂ) :
       complexToFinTwoCLE z 0 = z.re

   theorem complexToFinTwoCLE_apply_one (z : ℂ) :
       complexToFinTwoCLE z 1 = z.im

   noncomputable def complexChartRealBlockCLE (m : ℕ) :
       ComplexChartSpace m ≃L[ℝ] (Fin m -> Fin 2 -> ℝ)

   noncomputable def complexChartRealFlattenCLE (m : ℕ) :
       ComplexChartSpace m ≃L[ℝ] (Fin (m * 2) -> ℝ)

   theorem complexChartRealFlattenCLE_apply_re
       (z : ComplexChartSpace m) (i : Fin m) :
       complexChartRealFlattenCLE m z (finProdFinEquiv (i, (0 : Fin 2))) =
         (z i).re

   theorem complexChartRealFlattenCLE_apply_im
       (z : ComplexChartSpace m) (i : Fin m) :
       complexChartRealFlattenCLE m z (finProdFinEquiv (i, (1 : Fin 2))) =
         (z i).im

   private def finAppendLinearEquiv (m n : ℕ) :
       ((Fin m -> ℝ) × (Fin n -> ℝ)) ≃ₗ[ℝ] (Fin (m + n) -> ℝ)

   noncomputable def finAppendCLE (m n : ℕ) :
       ((Fin m -> ℝ) × (Fin n -> ℝ)) ≃L[ℝ] (Fin (m + n) -> ℝ)

   theorem finAppendCLE_apply_head
       (p : (Fin m -> ℝ) × (Fin n -> ℝ)) (i : Fin m) :
       finAppendCLE m n p (Fin.castAdd n i) = p.1 i

   theorem finAppendCLE_apply_tail
       (p : (Fin m -> ℝ) × (Fin n -> ℝ)) (i : Fin n) :
       finAppendCLE m n p (Fin.natAdd m i) = p.2 i

   noncomputable def mixedChartFiberFirstCLE (m : ℕ) :
       (ComplexChartSpace m × (Fin m -> ℝ)) ≃L[ℝ]
         (Fin (m + m * 2) -> ℝ)

   theorem mixedChartFiberFirstCLE_apply_head
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) (i : Fin m) :
       mixedChartFiberFirstCLE m (z,t) (Fin.castAdd (m * 2) i) = t i

   theorem mixedChartFiberFirstCLE_apply_tail_re
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) (i : Fin m) :
       mixedChartFiberFirstCLE m (z,t)
         (Fin.natAdd m (finProdFinEquiv (i, (0 : Fin 2)))) = (z i).re

   theorem mixedChartFiberFirstCLE_apply_tail_im
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) (i : Fin m) :
       mixedChartFiberFirstCLE m (z,t)
         (Fin.natAdd m (finProdFinEquiv (i, (1 : Fin 2)))) = (z i).im

   theorem mixedChartFiberFirstCLE_symm_headBlockShift
       (a : Fin m -> ℝ) :
       (mixedChartFiberFirstCLE m).symm (headBlockShift m (m * 2) a) =
         (0, a)
   ```

   `mixedChartFiberFirstCLE` must put the real fiber in the **head block** and
   the real/imaginary coordinates of the complex chart in the tail block.  With
   this ordering, `complexRealFiberTranslateSchwartzCLM a` transports exactly
   to head-block translation by `a`:

   ```lean
   theorem mixedChartFiberFirstCLE_translate
       (a : Fin m -> ℝ) :
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
         (mixedChartFiberFirstCLE m).symm).comp
         (complexRealFiberTranslateSchwartzCLM a) =
       (SCV.translateSchwartzCLM
          (headBlockShift m (m * 2) a)).comp
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mixedChartFiberFirstCLE m).symm)
   ```

   The verified proof transcript is:
   - prove `mixedChartFiberFirstCLE_symm_headBlockShift`, reducing the head
     shift under the inverse chart to `(0, a)` in
     `ComplexChartSpace m × (Fin m -> ℝ)`;
   - for a real-coordinate point `x`, set
     `y := (mixedChartFiberFirstCLE m).symm x`;
   - use linearity of `(mixedChartFiberFirstCLE m).symm` to rewrite
     `(mixedChartFiberFirstCLE m).symm (x + headBlockShift m (m * 2) a)` as
     `y + (0, a)`;
   - case-split `y = (z,t)` and reduce both sides by `simp` to
     `F (z, t + a)`.

   Here `headBlockShift` is the pure-SCV extraction of the existing
   `zeroTailBlockShift` idea: the first `m` coordinates are `a`, and the final
   `n` coordinates are zero.  Extract this definition and its apply lemmas into
   the SCV package; do not import the Wightman file that currently contains the
   source-pattern version.

   The transported fiber integral must also be an exact theorem, not an
   informal identification:

   ```lean
   -- in namespace SCV, after extracting the QFT-free block-integration
   -- machinery out of the Wightman namespace
   theorem complexRealFiberIntegral_eq_transport_integrateHeadBlock
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       complexRealFiberIntegral F =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (complexChartRealFlattenCLE m))
           (integrateHeadBlock (m := m) (n := m * 2)
             ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
               (mixedChartFiberFirstCLE m).symm) F))
   ```

   The proof is Fubini-free: both sides are the same single integral over the
   real fiber after expanding `mixedChartFiberFirstCLE`; the finite-dimensional
   linear equivalence only reorders the non-integrated real coordinates.
   The outer chart transport uses `complexChartRealFlattenCLE m`, not its
   inverse: `compCLMOfContinuousLinearEquiv ℂ (complexChartRealFlattenCLE m)`
   has type
   `SchwartzMap (Fin (m * 2) -> ℝ) ℂ ->L[ℂ]
    SchwartzMap (ComplexChartSpace m) ℂ`.

   Because `DistributionalEOWKernel.lean` is now above 1000 lines and is
   sorry-free, Stage 3.1+ implementation should not continue growing that file.
   The next implementation file should be a pure-SCV companion:

   ```lean
   -- OSReconstruction/SCV/HeadBlockIntegral.lean
   import OSReconstruction.SCV.DistributionalEOWKernel

   namespace SCV

   def realFiberIntegralRaw
       (F : SchwartzMap ((Fin n -> ℝ) × (Fin m -> ℝ)) V)
       (u : Fin n -> ℝ) : V :=
     ∫ t : Fin m -> ℝ, F (u, t)

   def realFiberBaseFDerivSchwartz
       (F : SchwartzMap ((Fin n -> ℝ) × (Fin m -> ℝ)) V) :
       SchwartzMap ((Fin n -> ℝ) × (Fin m -> ℝ))
         ((Fin n -> ℝ) ->L[ℝ] V)

   def realFiberIntegral
       (F : SchwartzMap ((Fin n -> ℝ) × (Fin m -> ℝ)) ℂ) :
       SchwartzMap (Fin n -> ℝ) ℂ

   def headTailAppendCLE (m n : ℕ) :
       ((Fin n -> ℝ) × (Fin m -> ℝ)) ≃L[ℝ] (Fin (m + n) -> ℝ)

   theorem headTailAppendCLE_apply
       (u : Fin n -> ℝ) (t : Fin m -> ℝ) :
       headTailAppendCLE m n (u, t) = Fin.append t u

   noncomputable def integrateHeadBlock :
       SchwartzMap (Fin (m + n) -> ℝ) ℂ ->
       SchwartzMap (Fin n -> ℝ) ℂ

   theorem integrateHeadBlock_apply_finAppend
       (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ) (u : Fin n -> ℝ) :
       integrateHeadBlock (m := m) (n := n) F u =
         ∫ t : Fin m -> ℝ, F (Fin.append t u)

   end SCV
   ```

   The checked implementation uses the direct finite-dimensional real fiber
   integral rather than the older recursive `sliceIntegral` source pattern.
   This is mathematically the same head-block integral, but the theorem needed
   by the mixed-chart transport is Fubini-free:
   `integrateHeadBlock F u` is definitionally the integral of `F` over
   `Fin.append t u` after the continuous-linear equivalence
   `headTailAppendCLE m n`.

   `HeadBlockIntegral.lean` is extracted by adapting the QFT-free Schwartz
   estimates already checked for `complexRealFiberIntegral` in
   `SCV/DistributionalEOWKernel.lean`: fixed-fiber integrability, dominated
   differentiation under the fiber integral, smoothness, and higher derivative
   Schwartz decay.  It imports only SCV/Mathlib infrastructure.  The Wightman
   `SliceIntegral.lean` and `BlockIntegral.lean` files remain historical source
   patterns and are not imported.

   Minimal dependency ledger for `integrateHeadBlock_apply_finAppend`:

   | Lemma | Source pattern | Role |
   |---|---|---|
   | `integrable_realFiber` | adapted from `integrable_complexRealFiber` | fixed-base Bochner integrability over `Fin m -> ℝ` |
   | `realFiberBaseFDerivSchwartz` | adapted from `baseFDerivSchwartz` | base-variable derivative field for dominated differentiation |
   | `hasFDerivAt_realFiberIntegralRaw` | adapted from `hasFDerivAt_complexRealFiberIntegralRaw` | differentiating under the finite real fiber integral |
   | `decay_realFiberIntegralRaw` | adapted from `decay_complexRealFiberIntegralRaw` | Schwartz decay of all base derivatives |
   | `headTailAppendCLE_apply` | `finAppendCLE` | coordinate identity `(u,t) ↦ Fin.append t u` |
   | `integrateHeadBlock_apply_finAppend` | direct definition | public apply theorem consumed by mixed-chart transport |

   Lean proof transcript for `integrateHeadBlock_apply_finAppend`:

   ```lean
   theorem integrateHeadBlock_apply_finAppend
       (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (u : Fin n -> ℝ) :
       integrateHeadBlock (m := m) (n := n) F u =
         ∫ t : Fin m -> ℝ, F (Fin.append t u)
     simp [integrateHeadBlock,
       SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
       headTailAppendCLE_apply]
   ```

   After `integrateHeadBlock_apply_finAppend`, the transported mixed fiber
   integral proof is mechanical.  Add the following chart lemma in the file that
   imports both `HeadBlockIntegral.lean` and `DistributionalEOWKernel.lean`:

   ```lean
   -- OSReconstruction/SCV/DistributionalEOWKernelTransport.lean
   import OSReconstruction.SCV.HeadBlockIntegral
   import OSReconstruction.SCV.DistributionalEOWKernel

   namespace SCV

   theorem mixedChartFiberFirstCLE_apply_finAppend
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       mixedChartFiberFirstCLE m (z, t) =
         Fin.append t (complexChartRealFlattenCLE m z)

   theorem mixedChartFiberFirstCLE_symm_finAppend
       (z : ComplexChartSpace m) (t : Fin m -> ℝ) :
       (mixedChartFiberFirstCLE m).symm
         (Fin.append t (complexChartRealFlattenCLE m z)) = (z, t)

   theorem complexRealFiberIntegral_eq_transport_integrateHeadBlock
       (F : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ) :
       complexRealFiberIntegral F =
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (complexChartRealFlattenCLE m))
           (integrateHeadBlock (m := m) (n := m * 2)
             ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
               (mixedChartFiberFirstCLE m).symm) F))
   ```

   Proof transcript for the final theorem:

   ```lean
   ext z
   rw [complexRealFiberIntegral_apply]
   simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
   rw [integrateHeadBlock_apply_finAppend]
   apply integral_congr_ae
   filter_upwards with t
   rw [mixedChartFiberFirstCLE_symm_finAppend]
   ```

   If the exact simp theorem for `compCLMOfContinuousLinearEquiv` has a
   different generated name, first prove and use local apply lemmas for
   `complexChartRealFlattenCLE` and `mixedChartFiberFirstCLE` composition; do
   not change the theorem statement or the chart direction.

   After these transport lemmas, prove the pure theorem behind
   `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant` in SCV
   as a real-coordinate theorem.  The production target is the recursive
   quotient descent used by the checked Wightman source pattern: first prove
   the one-coordinate quotient through `sliceIntegral` using the
   `headFiberAntideriv` theorem, then induct over the head block.  The
   zero-fiber-integral Poincare decomposition is useful intuition, but it
   should not be introduced as a separate public theorem unless a later proof
   consumes it directly.

   ```lean
   theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hFG : integrateHeadBlock (m := m) (n := n) F =
         integrateHeadBlock (m := m) (n := n) G) :
       T F = T G
   ```

   Proof transcript for this decomposition:

   1. `m = 0`: use `integrateHeadBlock_apply_finAppend` and
      `Measure.volume_pi_eq_dirac` / `integral_dirac` to reduce `hF` to
      `F = 0`; the empty sum is zero.
   2. `m = k + 1`: expose the first head coordinate by an explicit continuous
      linear equivalence
      `(Fin n -> ℝ) × (Fin (k + 1) -> ℝ) ≃L[ℝ]
       ((Fin n -> ℝ) × (Fin k -> ℝ)) × ℝ`, not by importing the Wightman
      reindexing file.
   3. Let
      `g(s,u) = ∫ x : ℝ, F (Fin.append (Fin.cons x s) u)`.  This is a checked
      instance of `realFiberIntegral` with base
      `(Fin k -> ℝ) × (Fin n -> ℝ)`.
   4. Pick one fixed normalized one-dimensional Schwartz bump `φ` and define
      `F₀(x,s,u) = F(x,s,u) - φ x * g(s,u)`.  Then
      `∫ x, F₀(x,s,u) = 0` for every `(s,u)`.
   5. Apply the one-coordinate fiberwise antiderivative theorem to `F₀`,
      obtaining `H₀` with `∂_{firstHead} H₀ = F₀`.
   6. The remaining term `φ x * g(s,u)` has zero integral over the remaining
      `k` head coordinates because `integrateHeadBlock F = 0`.  Apply the
      induction hypothesis to `g`, then prepend each primitive with `φ`.
   7. Reassemble the sum of derivatives and transport it back through the
      head-tail append equivalence.

   The direct quotient map now has the basic checked algebra needed by this
   induction:

   ```lean
   theorem integrateHeadBlock_add
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       integrateHeadBlock (m := m) (n := n) (F + G) =
         integrateHeadBlock (m := m) (n := n) F +
           integrateHeadBlock (m := m) (n := n) G

   theorem integrateHeadBlock_sub
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       integrateHeadBlock (m := m) (n := n) (F - G) =
         integrateHeadBlock (m := m) (n := n) F -
           integrateHeadBlock (m := m) (n := n) G
   ```

   The one-coordinate antiderivative theorem is the large analytic extraction
   still needed here.  Do not start with a general Banach-space parameter `E`;
   the first production theorem should be the finite-dimensional real product
   statement below, which is exactly what the induction consumes:

   ```lean
   noncomputable def headFiberAntiderivRaw {n : ℕ}
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
       (Fin (n + 1) -> ℝ) -> ℂ :=
     fun v => ∫ t in Set.Iic (v 0), F (Fin.cons t (Fin.tail v))

   noncomputable def headFiberAntideriv {n : ℕ}
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hF : ∀ y : Fin n -> ℝ, ∫ x : ℝ, F (Fin.cons x y) = 0) :
       SchwartzMap (Fin (n + 1) -> ℝ) ℂ

   theorem lineDeriv_headFiberAntideriv {n : ℕ}
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hF : ∀ y : Fin n -> ℝ, ∫ x : ℝ, F (Fin.cons x y) = 0) :
       LineDeriv.lineDerivOp
         ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) -> ℝ)
         (headFiberAntideriv F hF) = F

   theorem exists_headFiberAntideriv_of_integral_eq_zero
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hF : ∀ y : Fin n -> ℝ, ∫ x : ℝ, F (Fin.cons x y) = 0) :
       ∃ H : SchwartzMap (Fin (n + 1) -> ℝ) ℂ,
         LineDeriv.lineDerivOp
           ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) -> ℝ) H = F
   ```

   Proof transcript for this extraction:

   1. Extract the QFT-free definitions underlying
      `Wightman/Reconstruction/SliceIntegral.lean` into a new SCV companion
      file, with names `SCV.headFiberAntiderivRaw` and
      `SCV.headFiberAntideriv`.  The true dependency range is not only lines
      1713-2639: the proof also consumes the earlier slice-integral,
      `iicZeroSlice`, and `intervalPiece` derivative machinery.
   2. Also extract the elementary coordinate maps used by that proof:
      `tailInsertCLM`, `tailInsertCLM_apply`, `tailInsertCLM_opNorm_le`,
      `SCV.tailCLM`, and the `Fin.cons`/`Fin.tail` coordinate identities.  These
      are finite-dimensional real-coordinate lemmas, not Wightman objects.
   3. Keep the two analytic representations explicit:
      `headFiberAntiderivRaw F v = ∫ t in Set.Iic (v 0), ...`, and under
      `hF`,
      `headFiberAntiderivRaw F v = -(∫ t in Set.Ioi (v 0), ...)`.
   4. Prove the head-direction FTC lemma first:
      `lineDeriv ℝ (headFiberAntiderivRaw F) v (Pi.single 0 1) = F v`.
   5. Prove smoothness by the interval/Iic decomposition and parameterized
      FTC, then prove Schwartz decay by the negative/positive half-line split.
      The decay induction must retain the tail-derivative formula
      `fderiv headFiberAntiderivRaw = head term + tail antiderivatives`.
   6. Wrap the raw map as a `SchwartzMap` only after smoothness and decay are
      checked; no `sorry` or arbitrary choice is allowed in the definition.
   7. The existential theorem is then a one-line `refine ⟨headFiberAntideriv F
      hF, ?_⟩; ext v; simpa [SchwartzMap.lineDerivOp_apply] using
      lineDeriv_headFiberAntideriv F hF v`.

   Do not import `Wightman/Reconstruction/SliceIntegral.lean` into SCV.  The
   source file is a proof pattern only; the production dependency must be
   QFT-free.

   First extract the small pure product-coordinate substrate from
   `Wightman/SchwartzTensorProduct.lean` into
   `SCV/SchwartzPrependField.lean`; do not import the Wightman file into SCV.
   This file is genuine Schwartz infrastructure, not a wrapper.  The
   declarations must live under `namespace SCV`, not as global `tailCLM` or
   `SchwartzMap.prependField`, because the old Wightman source already defines
   those global names.  The Stage 3.5 consumer only needs the finite-dimensional
   real-coordinate case:

   ```lean
   import OSReconstruction.SCV.DistributionalEOWKernel

   namespace SCV

   noncomputable def tailCLM (n : ℕ) :
       (Fin (n + 1) -> ℝ) ->L[ℝ] (Fin n -> ℝ)
   @[simp] theorem tailCLM_apply
   theorem tailCLM_opNorm_le
   theorem norm_le_head_add_tail

   def prependField
       (f : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ) :
       SchwartzMap (Fin (n + 1) -> ℝ) ℂ
   @[simp] theorem prependField_apply
   theorem prependField_add_right
   theorem prependField_sub_right
   theorem prependField_smul_right
   theorem prependField_seminorm_le
   theorem prependField_isBounded_right
   theorem prependField_continuous_right
   def prependFieldCLMRight
   @[simp] theorem prependFieldCLMRight_apply

   end SCV
   ```

   The proof should not port the full old tensor-product continuity package.
   Prove fixed-head continuity directly from the Schwartz seminorm estimate:

   ```lean
   theorem prependField_seminorm_le {n : ℕ}
       (f : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ)
       (p l : ℕ) :
       SchwartzMap.seminorm ℝ p l (SCV.prependField f g) ≤
         (2 : ℝ) ^ p * ∑ i in Finset.range (l + 1), (l.choose i : ℝ) *
           (SchwartzMap.seminorm ℝ p i f *
              SchwartzMap.seminorm ℝ 0 (l - i) g +
            SchwartzMap.seminorm ℝ 0 i f *
              SchwartzMap.seminorm ℝ p (l - i) g)
   ```

   For each target seminorm `(p,l)`, take the finite source index set
   `{(0,l-i), (p,l-i) | i ∈ range (l+1)}` and the real constant
   `(2 : ℝ)^p * ∑ i, choose(l,i) *
     (seminorm p i f + seminorm 0 i f)`.  Since each source seminorm is bounded
   by the finite supremum over that set, `WithSeminorms.continuous_of_isBounded`
   gives `SCV.prependField_continuous_right`.  This is the exact fixed-head
   CLM needed by the descent proof.  The left and joint continuity lemmas from
   the old source should stay unported unless a named later proof consumes them.

   Lean proof transcript for `SCV/SchwartzPrependField.lean`:

   1. Define `SCV.tailCLM n` as the projection `x ↦ fun i => x i.succ`, prove
      `tailCLM_apply` by `rfl`, and prove `tailCLM_opNorm_le` from the pi
      norm projection bound.  Prove `norm_le_head_add_tail` by `Fin.cases` on
      the coordinate index.
   2. Define `SCV.prependField f g` by
      `toFun x = f (x 0) * g (fun i => x i.succ)`.  Smoothness is
      `ContDiff.mul` after composing `f.smooth'` with the head projection and
      `g.smooth'` with `SCV.tailCLM n`.
   3. Prove the `decay'` field directly from the old source estimate:
      compose iterated derivatives through the head and tail CLMs, apply
      `norm_iteratedFDeriv_mul_le`, use
      `norm_le_head_add_tail` and `(a+b)^p ≤ 2^p(a^p+b^p)`, and finish with
      the Schwartz decay constants for `f` and `g`.
   4. Prove the algebra lemmas by `ext x; simp [SCV.prependField, mul_add,
      mul_sub, mul_left_comm]`.
   5. Prove `prependField_seminorm_le` by repeating the decay estimate with
      `SchwartzMap.le_seminorm ℝ` in place of chosen decay constants.  This
      theorem is the non-wrapper mathematical input for continuity.
   6. Prove `prependField_isBounded_right f` for the real restricted linear
      map `g ↦ SCV.prependField f g` using `Seminorm.IsBounded.of_real`.  For
      target `(p,l)`, use
      `s = image (fun i => (0,l-i)) range ∪ image (fun i => (p,l-i)) range`
      and the constant described above; each source seminorm is controlled by
      `Finset.le_sup` at the corresponding image member.
   7. Prove `prependField_continuous_right f` by applying
      `WithSeminorms.continuous_of_isBounded` to
      `schwartz_withSeminorms ℝ (Fin n -> ℝ) ℂ` and
      `schwartz_withSeminorms ℝ (Fin (n+1) -> ℝ) ℂ`.
   8. Define `SCV.prependFieldCLMRight f` as the complex continuous linear map
      whose `toLinearMap` is `g ↦ SCV.prependField f g`, with complex add/smul
      laws from step 4 and continuity from step 7.

   Lean-ready extraction order for `SCV/HeadFiberAntideriv.lean`:

   ```lean
   import OSReconstruction.SCV.SchwartzPrependField
   import OSReconstruction.SCV.HeadBlockIntegral
   import Mathlib.Analysis.Calculus.ParametricIntegral
   import Mathlib.Analysis.Asymptotics.Lemmas
   import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
   import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
   import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
   import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
   import Mathlib.MeasureTheory.Integral.IntegralEqImproper
   import Mathlib.MeasureTheory.Integral.Prod
   ```

   The declarations should be ported in this order, and each batch should be
   checked by `lake env lean` on the exact touched file.  Current status:
	   batches 1-7 below are now checked across the pure-SCV files.  To
	   keep the frontier below the harness file-size threshold, the remaining
	   antiderivative extraction was split into coherent companion files:

   1. `SCV/HeadFiberAntideriv.lean` — checked slice-integral substrate,
      including `iicZeroSlice` and its derivative/`ContDiff` package.
   2. `SCV/HeadFiberAntiderivInterval.lean` — checked `intervalPiece`,
      `headFiberAntiderivRaw`, and the head-direction FTC.
	   3. `SCV/HeadFiberAntiderivDecay.lean` — checked zero-slice preservation,
	      decay induction, and final Schwartz packaging.

   The split is organizational only: each file contains genuine analytic
   content and no forwarding wrapper layer.

   1. Coordinate insertion and one-dimensional slice integral:

      ```lean
      noncomputable def tailInsertCLM (n : ℕ) :
          (Fin n -> ℝ) ->L[ℝ] (Fin (n + 1) -> ℝ)

      @[simp] theorem tailInsertCLM_apply ...
      theorem tailInsertCLM_opNorm_le ...

      def sliceIntegralRaw {n : ℕ}
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (Fin (n + 1) -> ℝ) V)
          (y : Fin n -> ℝ) : V :=
        ∫ x : ℝ, F (Fin.cons x y)

      @[simp] theorem sliceIntegralRaw_prependField
          (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ)
          (y : Fin n -> ℝ) :
          sliceIntegralRaw (SCV.prependField φ g) y =
            (∫ x : ℝ, φ x) * g y

      theorem integral_sliceIntegralRaw
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (Fin (n + 1) -> ℝ) V) :
          ∫ y : Fin n -> ℝ, sliceIntegralRaw F y =
            ∫ z : Fin (n + 1) -> ℝ, F z

      theorem exists_one_add_norm_pow_mul_sliceIntegralRaw_le
          {n k : ℕ} {V : Type*} [NormedAddCommGroup V]
          [NormedSpace ℝ V] [CompleteSpace V] :
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ (F : SchwartzMap (Fin (n + 1) -> ℝ) V)
              (y : Fin n -> ℝ),
              (1 + ‖y‖) ^ k * ‖sliceIntegralRaw F y‖ ≤
                C * ((Finset.Iic (k + 2, 0)).sup
                  (schwartzSeminormFamily ℝ (Fin (n + 1) -> ℝ) V)) F

      theorem norm_sliceSection_le_inv_one_add_sq
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (y : Fin n -> ℝ) (x : ℝ) :
          ‖F (Fin.cons x y)‖ ≤
            ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) -> ℝ) ℂ)) F) *
              (1 + x ^ 2)⁻¹

      theorem integrable_sliceSection
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) (y : Fin n -> ℝ) :
          Integrable (fun x : ℝ => F (Fin.cons x y))

      theorem decay_sliceIntegralRaw
          (k m : ℕ)
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (Fin (n + 1) -> ℝ) V) :
          ∃ C : ℝ, ∀ y : Fin n -> ℝ,
            ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (sliceIntegralRaw F) y‖ ≤ C

      noncomputable def sliceIntegral
          {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
          [CompleteSpace V]
          (F : SchwartzMap (Fin (n + 1) -> ℝ) V) :
          SchwartzMap (Fin n -> ℝ) V

      @[simp] theorem sliceIntegral_apply
      theorem integral_sliceIntegral

      -- Complex-valued algebra needed by descent:
      theorem sliceIntegral_add
          (F G : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
          sliceIntegral (F + G) = sliceIntegral F + sliceIntegral G
      theorem sliceIntegral_sub
          (F G : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
          sliceIntegral (F - G) = sliceIntegral F - sliceIntegral G
      theorem sliceIntegral_smul
          (c : ℂ) (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
          sliceIntegral (c • F) = c • sliceIntegral F
      theorem sliceIntegral_prependField
          (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ) :
          sliceIntegral (SCV.prependField φ g) =
            (∫ x : ℝ, φ x) • g
      theorem sliceIntegral_prependField_eq_self
          (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n -> ℝ) ℂ)
          (hφ : ∫ x : ℝ, φ x = 1) :
          sliceIntegral (SCV.prependField φ g) = g

      theorem sliceIntegral_translateSchwartz_head
      ```

      Proof transcript for this batch:

      1. `tailInsertCLM` is the linear map `y ↦ Fin.cons 0 y`; prove its
         operator norm bound by the pi-norm supremum.
      2. `sliceIntegralRaw_prependField` is
         `MeasureTheory.integral_mul_const` after unfolding
         `SCV.prependField_apply`.
      3. `integral_sliceIntegralRaw` uses
         `MeasurableEquiv.piFinSuccAbove` at coordinate `0`,
         `volume_preserving_piFinSuccAbove`, integrability of Schwartz maps,
         `integral_prod_symm`, and the measure-preserving integral-change
         theorem.
      4. `exists_one_add_norm_pow_mul_sliceIntegralRaw_le` is the first
         genuine estimate: with
         `S = (Finset.Iic (k+2,0)).sup schwartzSeminormFamily F`, prove
         `(1+‖y‖)^k * ‖F (Fin.cons x y)‖ ≤
          (2^(k+2) * S) * (1+x^2)⁻¹`, integrate against
         `integrable_inv_one_add_sq`, and take
         `C = 2^(k+2) * ∫ x, (1+x^2)⁻¹`.
      5. `norm_sliceSection_le_inv_one_add_sq` is the `k=0` pointwise majorant
         from the same seminorm estimate.  `integrable_sliceSection` follows
         by `Integrable.mono'`.
      6. `decay_sliceIntegralRaw` is by induction on the iterated derivative
         order: the base case uses the estimate in step 4; the successor step
         uses `fderiv_sliceIntegralRaw_eq`, composition by
         `ContinuousLinearMap.compL ... (SCV.tailInsertCLM n)`, and the
         induction hypothesis for `SchwartzMap.fderivCLM`.
      7. Package `sliceIntegral` only after `contDiff_sliceIntegralRaw` and
         `decay_sliceIntegralRaw` are proved.  The add/sub/smul and
         prepend-field theorems are then pointwise integral algebra; they are
         not a substitute for the decay proof.

      `sliceIntegral` is not an optional convenience wrapper: it is the
      quotient map used by the one-coordinate descent theorem and the recursive
      head-block descent induction.

   2. Derivatives of the raw slice integral:

      ```lean
      theorem hasFDerivAt_sliceSection
      theorem norm_fderiv_fullSlice_le_inv_one_add_sq
      theorem norm_fderiv_sliceSection_le_inv_one_add_sq
      theorem hasFDerivAt_sliceIntegralRaw
      theorem fderiv_sliceIntegralRaw_eq
      theorem continuous_fderiv_sliceIntegralRaw
      theorem contDiff_nat_sliceIntegralRaw
      theorem contDiff_sliceIntegralRaw
      ```

      These are needed only for the zero-slice preservation lemma below.  The
      proof is dominated differentiation under the integral with derivative
      field
      `(fun x => (fderiv ℝ F (Fin.cons x y)).comp (tailInsertCLM n))`.

   3. Fixed lower half-line slice:

      ```lean
      def iicZeroSlice {n : ℕ}
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) (y : Fin n -> ℝ) : ℂ :=
        ∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y)

      theorem hasFDerivAt_iicZeroSlice
      theorem fderiv_iicZeroSlice_eq
      theorem contDiff_nat_iicZeroSlice
      theorem contDiff_iicZeroSlice
      ```

      This is the restricted-measure version of the slice-integral derivative
      theorem.  It supplies the tail-smooth fixed-boundary term in
      `headFiberAntiderivRaw_eq_interval_add_iic`.

   4. Variable finite interval piece:

      ```lean
      def intervalPiece {n : ℕ}
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (v : Fin (n + 1) -> ℝ) : ℂ :=
        ∫ t in (0 : ℝ)..(v 0), F (Fin.cons t (Fin.tail v))

      theorem hasDerivAt_intervalPiece_head
      theorem hasFDerivAt_intervalPiece_tailFixed
      theorem intervalPiece_split_at
      theorem hasFDerivAt_intervalPiece_tailFixed_prod
      theorem hasFDerivAt_intervalPiece_headFixed_prod
      def intervalPieceShortTailError
      theorem intervalPiece_prod_split
      theorem norm_intervalPieceShortTailError_le
      theorem hasFDerivAt_intervalPieceShortTailError
      noncomputable def headTailCLM
      theorem hasFDerivAt_intervalPiece_prod
      theorem hasFDerivAt_intervalPiece
      theorem contDiff_intervalPiece
      ```

      The only hard point here is the product differentiability proof:
      split simultaneous head/tail variation into a head-fixed piece plus a
      short tail-error integral and use the uniform derivative bound from the
      old source proof.

   5. Raw antiderivative, FTC, and split formulas:

      ```lean
      def headFiberAntiderivRaw
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
          (Fin (n + 1) -> ℝ) -> ℂ :=
        fun v => ∫ t in Set.Iic (v 0), F (Fin.cons t (Fin.tail v))

      theorem headFiberAntiderivRaw_eq_interval_add_iic
      theorem lineDeriv_headFiberAntiderivRaw
      theorem headFiberAntiderivRaw_eq_neg_ioi
      ```

      `lineDeriv_headFiberAntiderivRaw` is the one-dimensional FTC:
      fix the tail `y = Fin.tail v`, set `G s = F (Fin.cons s y)`, use
      `hasDerivAt_integral_Iic`, and identify
      `Fin.tail (v + t • Pi.single 0 1) = y`.

   6. Tail-derivative recursion and decay:

      ```lean
      theorem zeroSlice_lineDerivOp_tailInsert
      theorem fderiv_iicZeroSlice_comp_tail_tailInsert_eq
      theorem fderiv_intervalPiece_tailInsert_eq
      theorem head_tail_decomposition_sliceIntegral
      theorem fderiv_iicZeroSlice_comp_tail_apply
      theorem contDiff_headFiberAntiderivRaw
      theorem fderiv_headFiberAntiderivRaw_apply
      theorem exists_norm_pow_mul_headFiberAntiderivRaw_le
      theorem headFiberAntiderivRaw_add
      theorem headFiberAntiderivRaw_smul
      theorem headFiberAntiderivRaw_finset_sum
      theorem fderiv_headFiberAntiderivRaw_eq_sum
      theorem decay_headFiberAntiderivRaw
      ```

      The zero-slice preservation theorem is:

      ```lean
      theorem zeroSlice_lineDerivOp_tailInsert
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (hzero : ∀ y : Fin n -> ℝ,
            ∫ t : ℝ, F (Fin.cons t y) = 0)
          (w : Fin n -> ℝ) :
          ∀ y : Fin n -> ℝ,
            ∫ t : ℝ,
              (LineDeriv.lineDerivOp (tailInsertCLM n w) F)
                (Fin.cons t y) = 0
      ```

      Its proof is not optional: rewrite `sliceIntegralRaw F = 0`, take the
      line derivative in the tail direction, rewrite the derivative of
      `sliceIntegralRaw` by differentiating under the integral, and conclude
      the new slice integral is zero.

      The decay proof is by induction on the iterated-derivative order `p`.
      At `p = 0`, split into cases `0 <= v 0` and `v 0 <= 0`, using the
      `Set.Ioi` representation in the first case and the original `Set.Iic`
      representation in the second.  In the successor step, use
      `fderiv_headFiberAntiderivRaw_eq_sum` and the induction hypotheses for
      the tail derivatives supplied by `zeroSlice_lineDerivOp_tailInsert`.

      The compact-support theorem
      `hasCompactSupport_fiberwiseAntiderivRaw` from the old source is not
      consumed by the Stage 3.5 descent proof and should not be ported unless a
      later named proof step needs it.

   7. Schwartz packaging:

      ```lean
      noncomputable def headFiberAntideriv
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (hzero : ∀ y : Fin n -> ℝ,
            ∫ t : ℝ, F (Fin.cons t y) = 0) :
          SchwartzMap (Fin (n + 1) -> ℝ) ℂ :=
        SchwartzMap.mk (headFiberAntiderivRaw F)
          (contDiff_headFiberAntiderivRaw F)
          (decay_headFiberAntiderivRaw F hzero)

      theorem lineDeriv_headFiberAntideriv
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (hzero : ∀ y : Fin n -> ℝ,
            ∫ t : ℝ, F (Fin.cons t y) = 0)
          (v : Fin (n + 1) -> ℝ) :
          lineDeriv ℝ (headFiberAntideriv F hzero) v
            (Pi.single 0 1) = F v

      theorem lineDerivOp_headFiberAntideriv
          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
          (hzero : ∀ y : Fin n -> ℝ,
            ∫ t : ℝ, F (Fin.cons t y) = 0) :
          LineDeriv.lineDerivOp
            ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) -> ℝ)
            (headFiberAntideriv F hzero) = F
      ```

	      The last theorem is an `ext v` wrapper over the pointwise line-derivative
	      theorem and is the exact consumer surface for head-translation descent.

	   Lean-ready transcript for `SCV/HeadFiberAntiderivDecay.lean`:

	   ```lean
	   import OSReconstruction.SCV.HeadFiberAntiderivInterval

	   noncomputable section

	   open scoped SchwartzMap Topology
	   open MeasureTheory SchwartzMap LineDeriv

	   namespace SCV
	   ```

	   This file is a direct QFT-free extraction of the checked source block
	   `Wightman/Reconstruction/SliceIntegral.lean`, lines 1945-2639, with
	   `fiberwiseAntiderivRaw` renamed to `headFiberAntiderivRaw` and the
	   collision-free `SCV.tailCLM` used in place of the old global `tailCLM`.
	   Do not port lines 1808-1940
	   (`hasCompactSupport_fiberwiseAntiderivRaw`): compact support of the raw
	   primitive is not consumed by the Stage 3.5 quotient descent and would only
	   enlarge the frontier.

	   1. Zero-slice preservation:

	      ```lean
	      theorem zeroSlice_lineDerivOp_tailInsert {n : ℕ}
	          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
	          (hzero : ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ, F (Fin.cons t y) = 0)
	          (w : Fin n -> ℝ) :
	          ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ,
	              (∂_{tailInsertCLM n w} F) (Fin.cons t y) = 0
	      ```

	      Proof:
	      define `hzeroFun : sliceIntegralRaw F = 0` by extensionality and
	      `hzero`.  The line derivative of the zero function is zero.  Rewrite
	      `lineDeriv ℝ (sliceIntegralRaw F) y w` using
	      `hasFDerivAt_sliceIntegralRaw`, move evaluation through
	      `ContinuousLinearMap.integral_apply`, and simplify with
	      `SchwartzMap.lineDerivOp_apply_eq_fderiv` and `tailInsertCLM_apply`.
	      The integrability input is exactly the differentiated-slice majorant
	      `norm_fderiv_sliceSection_le_inv_one_add_sq`.

	   2. Tail-derivative identities for the raw primitive:

	      ```lean
	      theorem fderiv_iicZeroSlice_comp_tail_tailInsert_eq
	      theorem fderiv_intervalPiece_tailInsert_eq
	      theorem head_tail_decomposition_sliceIntegral
	      theorem fderiv_iicZeroSlice_comp_tail_apply
	      theorem contDiff_headFiberAntiderivRaw
	      theorem fderiv_headFiberAntiderivRaw_apply
	      theorem headFiberAntiderivRaw_eq_neg_ioi
	      ```

	      Proof:
	      `fderiv_iicZeroSlice_comp_tail_tailInsert_eq` is the chain rule for
	      `iicZeroSlice F ∘ SCV.tailCLM n`, plus restricted-measure dominated
	      differentiation under the `Set.Iic 0` integral.  The dominating
	      function is again
	      `C * (1 + t^2)⁻¹`, with
	      `C = 4 * ((Finset.Iic (2,1)).sup schwartzSeminormFamily) F`.
	      `fderiv_intervalPiece_tailInsert_eq` evaluates the derivative formula
	      from `hasFDerivAt_intervalPiece` on the pure tail vector
	      `tailInsertCLM n w`; the head projection term vanishes and
	      `ContinuousLinearMap.intervalIntegral_apply` turns the remaining CLM
	      integral into the interval piece of the tail derivative.
	      `head_tail_decomposition_sliceIntegral` is the coordinate identity
	      `y = y 0 • Pi.single 0 1 + tailInsertCLM n (tailCLM n y)`.
	      `fderiv_iicZeroSlice_comp_tail_apply` reduces an arbitrary direction
	      to its tail component using the chain-rule derivative above.
	      Smoothness is the sum of `contDiff_intervalPiece F` and
	      `(contDiff_iicZeroSlice F).comp (tailCLM n).contDiff`.
	      The derivative formula for `headFiberAntiderivRaw` rewrites the raw
	      primitive as `intervalPiece + iicZeroSlice ∘ Fin.tail`; the head term
	      comes from `intervalPiece`, and the tail terms combine back into
	      `headFiberAntiderivRaw` for the line derivative
	      `∂_{tailInsertCLM n (tailCLM n y)} F`.  The `Set.Ioi` representation is
	      the complement split
	      `∫_{Iic a} f = ∫ f - ∫_{Ioi a} f` plus `hzero`.

	   3. Zeroth-order decay:

	      ```lean
	      theorem exists_norm_pow_mul_headFiberAntiderivRaw_le {n : ℕ}
	          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
	          (hzero : ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ, F (Fin.cons t y) = 0)
	          (k : ℕ) :
	          ∃ C : ℝ, ∀ v : Fin (n + 1) -> ℝ,
	            ‖v‖ ^ k * ‖headFiberAntiderivRaw F v‖ ≤ C
	      ```

	      Proof:
	      set
	      `S = ((Finset.Iic (k+2,0)).sup schwartzSeminormFamily) F`,
	      `M = 2^(k+2) * S`, and
	      `C = ∫ t, M * (1 + t^2)⁻¹`.  For
	      `zfun t = Fin.cons t (Fin.tail v)`, prove the pointwise estimate
	      `‖zfun t‖^k * ‖F (zfun t)‖ ≤ M * (1+t^2)⁻¹` from the Schwartz seminorm.
	      If `0 <= v 0`, rewrite the primitive by the `Set.Ioi` formula and use
	      `v`'s coordinates bounded by `zfun t` on `t ∈ Ioi (v 0)`.  If
	      `v 0 <= 0`, use the defining `Set.Iic` formula and the analogous
	      coordinate bound on `t ∈ Iic (v 0)`.  Both cases finish by
	      `setIntegral_mono_on` and `setIntegral_le_integral` against
	      `integrable_inv_one_add_sq`.

	   4. Linearity and derivative-basis decomposition:

	      ```lean
	      theorem headFiberAntiderivRaw_add
	      theorem headFiberAntiderivRaw_smul
	      theorem headFiberAntiderivRaw_finset_sum
	      theorem fderiv_headFiberAntiderivRaw_eq_sum
	      ```

	      Proof:
	      additivity and scalar-linearity are integral algebra over `Set.Iic`.
	      The finite-sum lemma is induction over `Finset`.  For the derivative
	      sum, expand `tailCLM n h` in the standard basis of `Fin n`, map that
	      decomposition through `tailInsertCLM n`, use linearity of
	      `SchwartzMap.lineDerivOp`, then apply finite-sum linearity of the raw
	      antiderivative to the tail part in
	      `fderiv_headFiberAntiderivRaw_apply`.

	   5. Full Schwartz decay and packaging:

	      ```lean
	      theorem decay_headFiberAntiderivRaw {n : ℕ}
	          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
	          (hzero : ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ, F (Fin.cons t y) = 0)
	          (k p : ℕ) :
	          ∃ C : ℝ, ∀ v : Fin (n + 1) -> ℝ,
	            ‖v‖ ^ k *
	              ‖iteratedFDeriv ℝ p (headFiberAntiderivRaw F) v‖ ≤ C

	      noncomputable def headFiberAntideriv {n : ℕ}
	          (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
	          (hzero : ∀ y : Fin n -> ℝ,
	            ∫ t : ℝ, F (Fin.cons t y) = 0) :
	          SchwartzMap (Fin (n + 1) -> ℝ) ℂ

	      theorem lineDeriv_headFiberAntideriv
	      theorem lineDerivOp_headFiberAntideriv
	      theorem exists_headFiberAntideriv_of_integral_eq_zero
	      ```

	      Proof:
	      induct on derivative order `p`.  The base case is
	      `exists_norm_pow_mul_headFiberAntiderivRaw_le`.  In the successor,
	      use `fderiv_headFiberAntiderivRaw_eq_sum` to write the derivative as
	      one head coefficient term plus finitely many tail-antiderivative terms.
	      The head coefficient uses `F.decay' k p`; the tail terms use the
	      induction hypothesis applied to
	      `∂_{tailInsertCLM n (Pi.single i 1)} F`, whose zero-slice hypothesis is
	      supplied by `zeroSlice_lineDerivOp_tailInsert`.  Push iterated
	      derivatives through the continuous linear maps with
	      `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`, sum the bounds, and
	      take
	      `C_total = ‖L₀‖ * C_head + ∑ i, ‖Lᵢ i‖ * C_tail i`.
	      Package the raw map by `SchwartzMap.mk` only after
	      `contDiff_headFiberAntiderivRaw` and `decay_headFiberAntiderivRaw`.
	      The pointwise line-derivative theorem is inherited from the checked raw
	      FTC lemma, and the `LineDeriv.lineDerivOp` theorem is an extensional
	      restatement for the descent consumer.

	   After `SCV/HeadFiberAntiderivDecay.lean`, the next file should be
	   `SCV/HeadBlockDescent.lean`.  It ports the QFT-free proof pattern from
	   `Wightman/Reconstruction/HeadTranslationInvariant.lean` and
	   `Wightman/Reconstruction/HeadBlockTranslationInvariant.lean`, but with
	   `SCV.headBlockShift`, `SCV.integrateHeadBlock`, and the new
   `SCV.sliceIntegral` package.  The production proof should use this
   recursive quotient descent rather than introducing an unconsumed explicit
   decomposition theorem.

	   Current checked status:

	   `SCV/HeadBlockDescent.lean` now checks the one-coordinate descent layer:
	   `IsHeadTranslationInvariantSchwartzCLM`,
	   `map_lineDeriv_eq_zero_of_headTranslationInvariant`,
	   `map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant`,
	   `map_eq_of_sliceIntegral_eq_of_headTranslationInvariant`,
	   `normedUnitBumpSchwartz`, `integral_normedUnitBumpSchwartz`,
	   `headTranslationDescentCLM`, and
	   `map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant`.
	   This is genuine descent content: it uses the checked
	   `headFiberAntideriv` package, not a wrapper around the old Wightman files.

	   The general block descent has one additional SCV-specific bridge compared
	   with the old source.  The old Wightman `integrateHeadBlock` was a
	   recursive definition, so the induction step reduced by
	   `simp [integrateHeadBlock]`.  The SCV `integrateHeadBlock` in
	   `SCV/HeadBlockIntegral.lean` is instead the direct finite-dimensional
	   block integral through `realFiberIntegral`.  The recursive induction now
	   proves the direct/recursive Fubini bridge explicitly; the bridge is not
	   hidden behind the induction theorem.

	   The same file now checks the general head-block descent layer:
	   `castFinCLE_apply`, `headBlockShift_zero`,
	   `finAppend_zero_castFinCLE`,
	   `reindexSchwartzFin_translate_headBlockShift_succ`,
	   `reindexSchwartzFin_symm_translate_headBlockShift`,
	   `prependField_translate_headBlockShift`,
	   `headTranslationDescentCLM_headBlockInvariant`,
	   `integrateHeadBlock_sliceIntegral_reindex`, and
	   `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV`.

	   Implemented declaration order for `SCV/HeadBlockDescent.lean`:

   ```lean
	   import OSReconstruction.SCV.HeadFiberAntiderivDecay
	   import OSReconstruction.SCV.DistributionalEOWKernelTransport
	   import Mathlib.Analysis.Calculus.BumpFunction.Normed

   def IsHeadTranslationInvariantSchwartzCLM
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ) : Prop :=
     ∀ a : ℝ, T.comp (translateSchwartzCLM (Fin.cons a 0)) = T

   theorem map_lineDeriv_eq_zero_of_headTranslationInvariant
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadTranslationInvariantSchwartzCLM T)
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
       T (LineDeriv.lineDerivOp
         ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) -> ℝ) F) = 0

   theorem map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadTranslationInvariantSchwartzCLM T)
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hzero : sliceIntegral F = 0) :
       T F = 0

   theorem map_eq_of_sliceIntegral_eq_of_headTranslationInvariant
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadTranslationInvariantSchwartzCLM T)
       (F G : SchwartzMap (Fin (n + 1) -> ℝ) ℂ)
       (hFG : sliceIntegral F = sliceIntegral G) :
       T F = T G
   ```

   The one-coordinate proof is now mechanically specified:

   1. `map_lineDeriv_eq_zero_of_headTranslationInvariant` is the already
      checked difference-quotient argument specialized to the vector
      `Pi.single 0 1`.
   2. `map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant` turns
      `sliceIntegral F = 0` into the pointwise zero-slice hypothesis for
      `headFiberAntideriv`, rewrites
      `LineDeriv.lineDerivOp (Pi.single 0 1) (headFiberAntideriv F hzero') = F`,
      and applies the previous derivative-annihilation theorem.
   3. `map_eq_of_sliceIntegral_eq_of_headTranslationInvariant` applies the
      zero theorem to `F - G`; the only algebra needed is
      `sliceIntegral_sub`, which is proved by the same integral-sub template
      as `integrateHeadBlock_sub`.

   Then add the descended tail functional:

   ```lean
   noncomputable def normedUnitBumpSchwartz : SchwartzMap ℝ ℂ
   theorem integral_normedUnitBumpSchwartz :
       ∫ x : ℝ, normedUnitBumpSchwartz x = 1

   noncomputable def headTranslationDescentCLM
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (φ : SchwartzMap ℝ ℂ) :
       SchwartzMap (Fin n -> ℝ) ℂ ->L[ℂ] ℂ :=
     T.comp (SCV.prependFieldCLMRight φ)

   theorem map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
       (T : SchwartzMap (Fin (n + 1) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadTranslationInvariantSchwartzCLM T)
       (φ : SchwartzMap ℝ ℂ)
       (hφ : ∫ x : ℝ, φ x = 1)
       (F : SchwartzMap (Fin (n + 1) -> ℝ) ℂ) :
       T F = headTranslationDescentCLM T φ (sliceIntegral F)
   ```

	   Direct/recursive bridge:

	   ```lean
	   abbrev castFinCLE (h : a = b) : (Fin a -> ℝ) ≃L[ℝ] (Fin b -> ℝ)
	   abbrev reindexSchwartzFin (h : a = b) :
	       SchwartzMap (Fin a -> ℝ) ℂ ->L[ℂ] SchwartzMap (Fin b -> ℝ) ℂ
	   @[simp] theorem reindexSchwartzFin_apply
	   @[simp] theorem castFinCLE_symm_apply

	   theorem integrateHeadBlock_sliceIntegral_reindex {m n : ℕ}
	       (F : SchwartzMap (Fin ((m + 1) + n) -> ℝ) ℂ) :
	       integrateHeadBlock (m := m) (n := n)
	         (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F)) =
	       integrateHeadBlock (m := m + 1) (n := n) F
	   ```

	   Proof transcript for `integrateHeadBlock_sliceIntegral_reindex`:

	   1. Work pointwise in `u : Fin n -> ℝ`.
	   2. The target reduces to
	      `∫ s : Fin m -> ℝ, ∫ x : ℝ,
	         F (Fin.append (Fin.cons x s) u)
	       =
	       ∫ t : Fin (m+1) -> ℝ, F (Fin.append t u)`.
	   3. Prove the fixed-tail head section as a Schwartz map without importing
	      `Wightman/Reconstruction/SchwartzPartialEval.lean`.  Extract the
	      QFT-free `partialEval₂` proof into a pure SCV file:

	      ```lean
	      theorem iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl
	          (f : SchwartzMap (E₁ × E₂) F) (y : E₂) (l : ℕ) (x : E₁) :
	          iteratedFDeriv ℝ l (fun x' => f (x', y)) x =
	            (iteratedFDeriv ℝ l (⇑f) (x, y)).compContinuousLinearMap
	              (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)

	      theorem norm_iteratedFDeriv_partialEval_le
	          (f : SchwartzMap (E₁ × E₂) F) (y : E₂) (l : ℕ) (x : E₁) :
	          ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖ ≤
	            ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖

	      def schwartzPartialEval₂
	          (f : SchwartzMap (E₁ × E₂) F) (y : E₂) :
	          SchwartzMap E₁ F

	      @[simp] theorem schwartzPartialEval₂_apply :
	          schwartzPartialEval₂ f y x = f (x, y)
	      ```

	      The decay proof is the standard product-space estimate:
	      choose `C` from `f.decay' k l`, bound the partial-evaluation
	      derivative by the full product derivative via `inl`, and use
	      `‖x‖ ≤ ‖(x,y)‖`.  This is the exact QFT-free mathematical content of
	      the old `partialEval₂` source, with no reconstruction imports.

	      Then define the fixed-tail section by partially evaluating the
	      product-coordinate pullback through `finAppendCLE`:

	      ```lean
	      def fixedTailHeadSection
	          (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
	          (u : Fin n -> ℝ) :
	          SchwartzMap (Fin m -> ℝ) ℂ :=
	        schwartzPartialEval₂
	          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
	            (finAppendCLE m n)) F) u

	      @[simp] theorem fixedTailHeadSection_apply :
	          fixedTailHeadSection F u t = F (Fin.append t u)
	      ```

	      The apply lemma is just
	      `change F (finAppendCLE m n (t,u)) = F (Fin.append t u); congr 1`,
	      using the definitional/product-coordinate behavior already checked for
	      `finAppendCLE`.
	   4. Apply the checked theorem `integral_sliceIntegralRaw` to
	      `fixedTailHeadSection F u`.  Its left side is the nested
	      `∫ s, ∫ x, ...`; its right side is the direct `m+1` head integral.
	   5. Finish by `reindexSchwartzFin_apply`, `sliceIntegral_apply`,
	      `sliceIntegralRaw`, `integrateHeadBlock_apply_finAppend`, and the
	      coordinate identity
	      `(castFinCLE (Nat.succ_add m n)).symm (Fin.cons x (Fin.append s u))
	       = Fin.append (Fin.cons x s) u`.
	      The identity is Lean-ready by `ext i`, `Fin.addCases` on
	      `i : Fin ((m + 1) + n)`, then `Fin.cases` on the head part.  The three
	      index casts needed in the branches are:

	      ```lean
	      (finCongr (Nat.succ_add m n)) (Fin.castAdd n (0 : Fin (m + 1))) = 0
	      (finCongr (Nat.succ_add m n)) (Fin.castAdd n k.succ) =
	        (Fin.castAdd n k).succ
	      (finCongr (Nat.succ_add m n)) (Fin.natAdd (m + 1) j) =
	        (Fin.natAdd m j).succ
	      ```

	      Each is proved by `apply Fin.ext; simp` (`omega` only for the final
	      tail branch).  With these, rewrite `castFinCLE_symm_apply` and close
	      by `simp [Fin.append]`.

	   Finally port the recursive head-block theorem.  The helper lemmas are
	   exactly the reindexing and prepend-field transport lemmas from
	   `HeadBlockTranslationInvariant.lean`, rewritten from the old
	   `zeroTailBlockShift` convention to `headBlockShift`:

   ```lean
   abbrev castFinCLE (h : a = b) : (Fin a -> ℝ) ≃L[ℝ] (Fin b -> ℝ)
   def reindexSchwartzFin (h : a = b)
       (F : SchwartzMap (Fin a -> ℝ) ℂ) :
       SchwartzMap (Fin b -> ℝ) ℂ
   @[simp] theorem castFinCLE_apply
   @[simp] theorem reindexSchwartzFin_apply
   @[simp] theorem castFinCLE_symm_apply

   @[simp] theorem headBlockShift_zero
   private theorem integral_fin_zero
   @[simp] theorem finAppend_zero_castFinCLE
   theorem reindexSchwartzFin_translate_headBlockShift_succ
   theorem reindexSchwartzFin_symm_translate_headBlockShift
   theorem prependField_translate_headBlockShift
   theorem headTranslationDescentCLM_headBlockInvariant
   theorem integrateHeadBlock_sliceIntegral_reindex

   theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       {m n : ℕ}
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hFG : integrateHeadBlock (m := m) (n := n) F =
         integrateHeadBlock (m := m) (n := n) G) :
       T F = T G
   ```

   Proof transcript for the recursive theorem:

   1. Induct on `m`.
   2. For `m = 0`, evaluate `hFG` at the cast of each tail coordinate and use
      `integrateHeadBlock_apply_finAppend` to prove `F = G`.  Because the SCV
      block integral is direct rather than recursive, this base case must
      explicitly use the zero-dimensional volume identity
      `(volume : Measure (Fin 0 -> ℝ)) = Measure.dirac default`, via
      `Measure.volume_pi_eq_dirac`, and the coordinate identity
      `Fin.append default (castFinCLE (Nat.zero_add n) x) = x`.  The coordinate
      identity is proved by `Fin.addCases`: the head branch is `Fin.elim0`, and
      the tail branch uses `Fin.append_right` plus
      `castFinCLE_apply` and
      `(finCongr (Nat.zero_add n)).symm j = Fin.natAdd 0 j`.
   3. For `m + 1`, reindex `F` and `G` by `Nat.succ_add m n` so the active
      head coordinate is first.
   4. Define `T' = T.comp (reindexSchwartzFin (Nat.succ_add m n).symm)`.
      Prove `T'` is one-coordinate head-translation invariant by rewriting the
      reindexed translate with
      `reindexSchwartzFin_symm_translate_headBlockShift` and applying `hT`.
      In the special vector `Fin.cons a 0`, write the zero tail as
      `fun _ : Fin m => 0`, then use `headBlockShift_zero` to rewrite
      `Fin.cons a (headBlockShift m n 0)` back to `Fin.cons a 0`.
   5. Use
      `map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant`
      to replace `T' F'` and `T' G'` by the descended functional evaluated on
      `sliceIntegral F'` and `sliceIntegral G'`.
   6. Prove the descended functional is invariant under the remaining `m`
      head translations using `prependField_translate_headBlockShift` and
      `hT`.
   7. Convert `hFG` into equality of the remaining block integrals of the two
      slices by the calculation
      `integrateHeadBlock (sliceIntegral F') =
       integrateHeadBlock (m := m + 1) F =
       integrateHeadBlock (m := m + 1) G =
       integrateHeadBlock (sliceIntegral G')`,
      using `integrateHeadBlock_sliceIntegral_reindex` in the first and last
      steps; apply the induction hypothesis.
   8. Reindex back by the inverse `castFinCLE` identities.

   After this theorem checked, the already verified transport proof from
   `test/proofideas_fiber_translation_descent.lean` was moved into production.
   `SCV/DistributionalEOWKernelTransport.lean` now checks:
   `liftToFlatChart_apply_liftMixedToFlat`,
   `liftToFlatChart_headBlockTranslationInvariant`,
   `integrateHeadBlock_liftMixedToFlat_eq_of_complexRealFiberIntegral_eq`, and:

   ```lean
   theorem map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hT : IsComplexRealFiberTranslationInvariant T)
       (F G : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (hFG : complexRealFiberIntegral F = complexRealFiberIntegral G) :
       T F = T G
   ```

   The checked derivative-annihilation theorem plus the recursive descent
   theorem give these consumer corollaries.  Add the zero corollary only if a
   downstream proof consumes it directly; the equality theorem above is the
   main Stage 3.5 surface:

   ```lean
   theorem map_lineDeriv_headBlockShift_eq_zero
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (i : Fin m)
       (H : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       T (LineDeriv.lineDerivOp
         (headBlockShift m n (Pi.single i (1 : ℝ))) H) = 0

   theorem map_eq_zero_of_integrateHeadBlock_eq_zero_of_headBlockTranslationInvariant
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hF : integrateHeadBlock (m := m) (n := n) F = 0) :
       T F = 0

   theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hFG : integrateHeadBlock (m := m) (n := n) F =
         integrateHeadBlock (m := m) (n := n) G) :
       T F = T G
   ```

   The derivative-annihilation lemma is now checked in
   `SCV/HeadBlockIntegral.lean`:

   ```lean
   def IsHeadBlockTranslationInvariantSchwartzCLM
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ) : Prop :=
     ∀ a : Fin m -> ℝ,
       T.comp (translateSchwartzCLM (headBlockShift m n a)) = T

   theorem map_lineDeriv_headBlockShift_eq_zero
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (i : Fin m)
       (H : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       T (LineDeriv.lineDerivOp
         (headBlockShift m n (Pi.single i (1 : ℝ))) H) = 0
   ```

   Its proof uses the checked difference-quotient theorem for
   `translateSchwartz`, now extracted to pure SCV from the QFT-free part of
   `Wightman/Reconstruction/TranslationInvariantSchwartz.lean`.  The checked
   SCV surface in `SCV/TranslationDifferentiation.lean` is:

   ```lean
   theorem exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le
       (f : SchwartzMap (Fin m -> ℝ) ℂ)
       (v : Fin m -> ℝ) (k n : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ t : ℝ, t ≠ 0 -> |t| ≤ 1 ->
           SchwartzMap.seminorm ℝ k n
             (t⁻¹ • (translateSchwartz (t • v) f - f) -
               LineDeriv.lineDerivOp v f) ≤ C * |t|

   theorem tendsto_diffQuotient_translateSchwartz_zero
       (f : SchwartzMap (Fin m -> ℝ) ℂ)
       (v : Fin m -> ℝ) :
       Filter.Tendsto
         (fun t : ℝ => t⁻¹ • (translateSchwartz (t • v) f - f))
         (nhdsWithin (0 : ℝ) ({0}ᶜ))
         (𝓝 (LineDeriv.lineDerivOp v f))
   ```

   The proof is the QFT-free content of
   `Wightman/Reconstruction/TranslationInvariantSchwartz.lean` lines
   1045-2660.  It was extracted without Wightman imports and without a
   file-level `set_option maxHeartbeats`.  The one long quantitative theorem
   uses a local `set_option maxHeartbeats 1200000 in`, matching the cost of
   the old source proof while keeping the override scoped to the theorem.

   Scratch support status after `agents_chat.md` #1312/#1313, now partly
   superseded by production:

   1. `test/proofideas_fiber_translation_descent.lean` checks with exactly one
      deliberate `sorry`, namely the pure real head-block descent theorem
      `map_eq_of_integrateHeadBlock_eq_of_isHeadBlockTranslationInvariantSCV`.
      Its proved content is the mixed-chart transport corollary from pure
      head-block descent to `complexRealFiberIntegral` descent.  That transport
      corollary is now in production, using
      `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV`
      instead of the scratch `sorry`; the remaining useful scratch material is
      only the elementary tensor-product linearity lemmas for
      `schwartzTensorProduct₂`.
   2. `test/proofideas_head_block_helpers.lean` checks with zero `sorry`s and
      zero warnings.  The file declares 19 theorem helpers, not the 15 stated
      in #1313: `integrateHeadBlock_smul`, `headBlockShift_zero`,
      `headBlockShift_add`, `translateSchwartz_zero`,
      `translateSchwartzCLM_zero`, the four
      `complexRealFiberIntegral_*` linearity lemmas, the six
      `realConvolutionTest_*` linearity lemmas, the three
      `complexRealFiberTranslateSchwartzCLM` / tensor-translate identities,
      and `isHeadBlockTranslationInvariantSCV_of_m_zero`.

   These helpers may be ported only when they are the next named proof step in
   the antiderivative/descent proof.  They are an algebra inventory, not a
   replacement for the genuine finite-dimensional antiderivative theorem.

   The checked quotient-map invariance now available in
   `SCV/HeadBlockIntegral.lean` is:

   ```lean
   theorem integrateHeadBlock_translate_head
       (a : Fin m -> ℝ) (F : SchwartzMap (Fin (m + n) -> ℝ) ℂ) :
       integrateHeadBlock (m := m) (n := n)
         (translateSchwartzCLM (headBlockShift m n a) F) =
       integrateHeadBlock (m := m) (n := n) F
   ```

   The mixed factorization theorem then follows by transporting `T`, `F`, and
   `G` through `mixedChartFiberFirstCLE`, applying the SCV head-block theorem,
   and transporting the equality of `integrateHeadBlock` back through
   `complexRealFiberIntegral_eq_transport_integrateHeadBlock`.

   The proof must not stop at this sentence.  The exact mixed theorem package
   is:

   ```lean
   def IsHeadBlockTranslationInvariantSchwartzCLM
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ) : Prop :=
     ∀ a : Fin m -> ℝ,
       T.comp (translateSchwartzCLM (headBlockShift m n a)) = T

   theorem compCLMOfContinuousLinearEquiv_injective
       (e : E ≃L[ℝ] F) :
       Function.Injective
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e :
           SchwartzMap F ℂ ->L[ℂ] SchwartzMap E ℂ)

   theorem compCLMOfContinuousLinearEquiv_symm_left_inv
       (e : E ≃L[ℝ] F) (f : SchwartzMap E ℂ) :
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) f) = f

   theorem compCLMOfContinuousLinearEquiv_symm_right_inv
       (e : E ≃L[ℝ] F) (f : SchwartzMap F ℂ) :
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) f) = f

   theorem mixedChartFiberFirstCLE_translate_inv
       (a : Fin m -> ℝ) :
       (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
         (mixedChartFiberFirstCLE m)).comp
         (translateSchwartzCLM (headBlockShift m (m * 2) a)) =
       (complexRealFiberTranslateSchwartzCLM a).comp
         (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
           (mixedChartFiberFirstCLE m))

   theorem map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       (T : SchwartzMap (Fin (m + n) -> ℝ) ℂ ->L[ℂ] ℂ)
       (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
       (F G : SchwartzMap (Fin (m + n) -> ℝ) ℂ)
       (hFG : integrateHeadBlock (m := m) (n := n) F =
         integrateHeadBlock (m := m) (n := n) G) :
       T F = T G

   theorem map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
       (T : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hT : IsComplexRealFiberTranslationInvariant T)
       (F G : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ)
       (hFG : complexRealFiberIntegral F = complexRealFiberIntegral G) :
       T F = T G
   ```

   Lean proof transcript for `mixedChartFiberFirstCLE_translate_inv`:

   ```lean
   ext H p
   rcases p with ⟨z, t⟩
   -- LHS evaluates `H` at
   --   `mixedChartFiberFirstCLE m (z,t) + headBlockShift m (m*2) a`.
   -- RHS evaluates `H` at
   --   `mixedChartFiberFirstCLE m (z,t+a)`.
   -- Prove the coordinate equality by extensionality:
   have hcoord :
       mixedChartFiberFirstCLE m (z, t) + headBlockShift m (m * 2) a =
         mixedChartFiberFirstCLE m (z, t + a) := by
     ext k
     -- split `k` into head/tail cases and use
     -- `mixedChartFiberFirstCLE_apply_head`,
     -- `mixedChartFiberFirstCLE_apply_tail_re/im`, and
     -- `headBlockShift_apply_head/tail`.
   simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hcoord]
   ```

   Lean proof transcript for the mixed factorization theorem:

   ```lean
   let pullFlat :=
     SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (mixedChartFiberFirstCLE m).symm
   let pushMixed :=
     SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (mixedChartFiberFirstCLE m)
   let Tflat : SchwartzMap (Fin (m + m * 2) -> ℝ) ℂ ->L[ℂ] ℂ :=
     T.comp pushMixed
   let Fflat := pullFlat F
   let Gflat := pullFlat G

   have hTflat :
       IsHeadBlockTranslationInvariantSchwartzCLM
         (m := m) (n := m * 2) Tflat := by
     intro a
     ext H
     -- use `mixedChartFiberFirstCLE_translate_inv a`
     -- and `hT a`.

   have hInt :
       integrateHeadBlock (m := m) (n := m * 2) Fflat =
         integrateHeadBlock (m := m) (n := m * 2) Gflat := by
     apply compCLMOfContinuousLinearEquiv_injective
       (complexChartRealFlattenCLE m)
     -- rewrite both sides by
     -- `complexRealFiberIntegral_eq_transport_integrateHeadBlock`
     -- and use `hFG`.

   have hflat :
       Tflat Fflat = Tflat Gflat :=
     map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
       Tflat hTflat Fflat Gflat hInt

   -- identify `pushMixed Fflat = F` and `pushMixed Gflat = G` by the
   -- left-inverse theorem for `compCLMOfContinuousLinearEquiv`.
   simpa [Tflat, Fflat, Gflat, pullFlat, pushMixed,
     compCLMOfContinuousLinearEquiv_symm_left_inv] using hflat
   ```

   The proof of
   `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV` is a
   direct extraction of the existing QFT-free induction in
   `Wightman/Reconstruction/HeadBlockTranslationInvariant.lean`, but with these
   replacements:

   | Existing source object | SCV extraction |
   |---|---|
   | `zeroTailBlockShift` | `headBlockShift` |
   | `OSReconstruction.integrateHeadBlock` | `SCV.integrateHeadBlock` |
   | `OSReconstruction.sliceIntegral` | `SCV.sliceIntegral` |
   | `headTranslationDescentCLM` | `SCV.headTranslationDescentCLM` |
   | Wightman namespace imports | pure SCV imports only |

   The one-coordinate descent step also requires extracting these QFT-free
   lemmas from `HeadTranslationInvariant.lean`,
   `SliceIntegral.lean`, and `TranslationInvariantSchwartz.lean`:

   ```lean
   def IsHeadTranslationInvariantSchwartzCLM
   theorem tendsto_diffQuotient_translateSchwartz_zero
   theorem map_lineDeriv_eq_zero_of_headTranslationInvariant
   theorem fiberwiseAntideriv
   theorem lineDeriv_fiberwiseAntideriv
   theorem map_eq_zero_of_sliceIntegral_eq_zero_of_headTranslationInvariant
   theorem map_eq_of_sliceIntegral_eq_of_headTranslationInvariant
   def headTranslationDescentCLM
   theorem map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
   ```

   Each of these is pure Schwartz analysis.  None may mention Wightman
   functions, Schwinger functions, OS positivity, Hilbert spaces, or boundary
   values.

4. Finish global descent:
   ```lean
   theorem translationCovariantProductKernel_descends
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (hcov : ProductKernelRealTranslationCovariantGlobal K) :
       ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
         ∀ φ ψ,
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ)
   ```
   Let `T := shearedProductKernelFunctional K`.  Apply the fiber-factorization
   theorem to `T`; then for product tensors use
   `complexRealFiberIntegral` of the sheared tensor product, which is exactly
   `realConvolutionTest φ ψ`.  This proves the Streater-Wightman statement
   that the kernel depends only on the translated complex point.
6. Prove `Hdist` is distributionally holomorphic by a three-lemma
   integration-by-parts package, not by a one-line appeal to holomorphy.

   The Lean-facing statements are:

   The support-preservation precursor lives in a small companion file
   `SCV/DistributionalEOWSupport.lean`, because
   `SCV/DistributionalEOWKernel.lean` is already a checked, stable support
   file.  Its declarations and proof transcript are:

   ```lean
   theorem directionalDerivSchwartzCLM_tsupport_subset
       {m : ℕ} (v : ComplexChartSpace m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport
         ((directionalDerivSchwartzCLM v φ :
           SchwartzMap (ComplexChartSpace m) ℂ) :
             ComplexChartSpace m -> ℂ) ⊆
       tsupport (φ : ComplexChartSpace m -> ℂ) := by
     simpa [directionalDerivSchwartzCLM] using
       (SchwartzMap.tsupport_lineDerivOp_subset (m := v) (f := φ))

   theorem directionalDerivSchwartzCLM_supportsInOpen
       {m : ℕ} {U : Set (ComplexChartSpace m)}
       {φ : SchwartzMap (ComplexChartSpace m) ℂ}
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (v : ComplexChartSpace m) :
       SupportsInOpen
         ((directionalDerivSchwartzCLM v φ :
           SchwartzMap (ComplexChartSpace m) ℂ) :
             ComplexChartSpace m -> ℂ) U := by
     constructor
     · exact hφ.1.mono'
         ((subset_tsupport _).trans
           (directionalDerivSchwartzCLM_tsupport_subset v φ))
     · exact
         (directionalDerivSchwartzCLM_tsupport_subset v φ).trans hφ.2

   theorem dbarSchwartzCLM_tsupport_subset
       {m : ℕ} (j : Fin m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport
         ((dbarSchwartzCLM j φ :
           SchwartzMap (ComplexChartSpace m) ℂ) :
             ComplexChartSpace m -> ℂ) ⊆
       tsupport (φ : ComplexChartSpace m -> ℂ)

   theorem SupportsInOpen.dbar
       {m : ℕ} {U : Set (ComplexChartSpace m)}
       {φ : SchwartzMap (ComplexChartSpace m) ℂ}
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (j : Fin m) :
       SupportsInOpen
         ((dbarSchwartzCLM j φ :
           SchwartzMap (ComplexChartSpace m) ℂ) :
             ComplexChartSpace m -> ℂ) U
   ```

   The `dbarSchwartzCLM_tsupport_subset` proof expands `dbarSchwartzCLM j φ`
   into the sum of two scalar multiples of real directional derivatives, uses
   `tsupport_add` and `tsupport_smul_subset_right`, and then applies
   `SchwartzMap.tsupport_lineDerivOp_subset` to the real and imaginary
   coordinate directions.  This is genuine infrastructure for the integration
   by parts package: it proves that applying `dbarSchwartzCLM` to a test
   supported in `U0` is still an admissible compactly supported test in `U0`.

   The next checked `∂bar` precursor is the Schwartz-Schwartz integration by
   parts package in `SCV/DistributionalEOWDbar.lean`.  It intentionally proves
   only the global Schwartz identity; the later local holomorphic factor still
   needs a cutoff/localization theorem before it can be applied to a merely
   holomorphic `G ψ`.

   ```lean
   theorem integral_mul_directionalDerivSchwartzCLM_right_eq_neg_left
       {m : ℕ}
       (f g : SchwartzMap (ComplexChartSpace m) ℂ)
       (v : ComplexChartSpace m) :
       (∫ z : ComplexChartSpace m,
           f z * (directionalDerivSchwartzCLM v g) z) =
         -∫ z : ComplexChartSpace m,
           (directionalDerivSchwartzCLM v f) z * g z

   theorem integral_mul_dbarSchwartzCLM_right_eq_neg_left
       {m : ℕ}
       (f g : SchwartzMap (ComplexChartSpace m) ℂ)
       (j : Fin m) :
       (∫ z : ComplexChartSpace m,
           f z * (dbarSchwartzCLM j g) z) =
         -∫ z : ComplexChartSpace m,
           (dbarSchwartzCLM j f) z * g z

   theorem integral_mul_dbarSchwartzCLM_right_eq_zero_of_dbar_eq_zero
       {m : ℕ}
       (f g : SchwartzMap (ComplexChartSpace m) ℂ)
       (j : Fin m)
       (hf : dbarSchwartzCLM j f = 0) :
       (∫ z : ComplexChartSpace m,
           f z * (dbarSchwartzCLM j g) z) = 0
   ```

   Proof transcript: the directional theorem is exactly
   `SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left` after unfolding
   `directionalDerivSchwartzCLM`.  The `∂bar` theorem applies the integral
   continuous linear map to the Schwartz pairing `f * g`, expands
   `dbarSchwartzCLM` as
   `(1/2) * (∂_real + I * ∂_imag)`, rewrites the two directional terms by the
   directional integration-by-parts theorem, and closes by ring
   normalization.  The zero corollary rewrites the left factor's
   `dbarSchwartzCLM` to zero.

   The next checked algebraic localization slice is:

   ```lean
   theorem integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz
       {m : ℕ}
       (F : ComplexChartSpace m -> ℂ)
       (G φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (j : Fin m)
       (hFG :
         ∀ z ∈ tsupport
             ((dbarSchwartzCLM j φ :
               SchwartzMap (ComplexChartSpace m) ℂ) :
               ComplexChartSpace m -> ℂ),
           F z = G z)
       (hG_dbar_zero :
         ∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
           (dbarSchwartzCLM j G) z = 0) :
       (∫ z : ComplexChartSpace m, F z * (dbarSchwartzCLM j φ) z) = 0
   ```

   Proof transcript: first replace `F` by `G` under the integral.  This is
   valid because `F = G` on `tsupport (dbarSchwartzCLM j φ)` and
   `dbarSchwartzCLM j φ` is pointwise zero off that topological support.  Then
   apply `integral_mul_dbarSchwartzCLM_right_eq_neg_left G φ j`.  The resulting
   integral is zero because `dbarSchwartzCLM j G = 0` on `tsupport φ`, while
   `φ` is pointwise zero off its topological support.  This lemma is the exact
   algebraic endpoint of the cutoff construction; it does not assert the
   cutoff exists.

   The cutoff/localization bridge is now checked in
   `OSReconstruction/SCV/DistributionalEOWRepresentative.lean`:

   ```lean
   theorem exists_local_dbarClosed_schwartz_representative
       {m : ℕ}
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (F : ComplexChartSpace m -> ℂ)
       (hF_holo : DifferentiableOn ℂ F U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (j : Fin m) :
       ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
         (∀ z ∈ tsupport
             ((dbarSchwartzCLM j φ :
               SchwartzMap (ComplexChartSpace m) ℂ) :
               ComplexChartSpace m -> ℂ),
             F z = G z) ∧
         (∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
             (dbarSchwartzCLM j G) z = 0)
   ```

   The representative theorem is implemented through smaller theorem
   surfaces.  The compact cutoff theorem is checked in
   `OSReconstruction/SCV/DistributionalEOWCutoff.lean`:

   ```lean
   theorem exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen
       {m : ℕ}
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U) :
       ∃ χ : ComplexChartSpace m -> ℝ,
         ContDiff ℝ (⊤ : ℕ∞) χ ∧
         HasCompactSupport χ ∧
         tsupport χ ⊆ U ∧
         Set.range χ ⊆ Set.Icc 0 1 ∧
         ∃ V : Set (ComplexChartSpace m),
           IsOpen V ∧
           tsupport (φ : ComplexChartSpace m -> ℂ) ⊆ V ∧
           V ⊆ U ∧
           Set.EqOn χ (fun _ => 1) V
   ```

   The zero-extension/smooth-to-Schwartz theorem is also checked:

   ```lean
   theorem exists_local_schwartz_representative_eq_on_open
       {m : ℕ}
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (F : ComplexChartSpace m -> ℂ)
       (hF_holo : DifferentiableOn ℂ F U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U) :
       ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
         ∃ V : Set (ComplexChartSpace m),
           IsOpen V ∧
           tsupport (φ : ComplexChartSpace m -> ℂ) ⊆ V ∧
           V ⊆ U ∧
           Set.EqOn (G : ComplexChartSpace m -> ℂ) F V
   ```

   The local Cauchy-Riemann theorem is checked as
   `dbarSchwartzCLM_eq_zero_on_of_eqOn_holomorphic`: if a Schwartz
   representative agrees with a holomorphic function on an open set `V ⊆ U`,
   then its `dbarSchwartzCLM j` value is zero on `V`.  It unfolds
   `dbarSchwartzCLM`, rewrites line derivatives as real Fréchet derivatives,
   uses eventual equality on `V`, and applies complex-linearity of
   `fderiv ℂ F z` after restricting scalars to `ℝ`.

   Lean-level construction plan for the cutoff and representative:

   1. From `hφ`, obtain compactness of `K = tsupport φ` and `K ⊆ U`.
      Since `dbarSchwartzCLM_tsupport_subset` is checked, the smaller support
      `tsupport (dbarSchwartzCLM j φ)` is also contained in `K`.
   2. The cutoff construction is now checked: build a cutoff equal to one on
      an open neighborhood of `K` using nested
      thickenings, not by applying the pointwise bump theorem directly to
      `K`.  Use `IsCompact.exists_cthickening_subset_open` to choose a closed
      thickening of `K` inside `U`, and
      finite-dimensional properness to keep that thickening compact.  Choose
      radii `0 < r₁ < r₂` such that `cthickening r₂ K` is compact and
      contained in `U`; set
      `V₁ = thickening r₁ K` and `V₂ = thickening r₂ K`.  Then
      `K ⊆ V₁`, `closure V₁ ⊆ V₂`, and
      `closure V₂ ⊆ cthickening r₂ K ⊆ U`.
   3. The checked cutoff theorem applies the smooth support theorem
      `exists_contMDiff_support_eq_eq_one_iff` to the open set `V₂` and the
      closed set `closure V₁`.  Convert the resulting manifold-smooth real
      function to a Euclidean `ContDiff ℝ ∞` function.  This yields
      `χ : ComplexChartSpace m -> ℝ` with range in `[0,1]`,
      `χ = 1` on `closure V₁`, `Function.support χ = V₂`, and hence
      `HasCompactSupport χ` plus `tsupport χ ⊆ U`.
   4. The representative theorem defines the compactly supported smooth
      function `H z = (χ z : ℂ) * F z`.  The support containment
      `tsupport χ ⊆ U` makes this independent of arbitrary values of `F` off
      `U`: outside `U`, `χ` is locally zero.  On a neighborhood of `K`,
      `H = F` because `χ = 1`.
   5. `H` is a Schwartz function by the compact-support smooth-to-
      Schwartz conversion already used in `SCV.DistributionalUniqueness`:
      compact support comes from `tsupport χ`, and smoothness comes from
      `ContDiffOn` multiplication with
      `(hF_holo.analyticOnNhd_of_finiteDimensional hU_open)
        .contDiffOn_of_completeSpace`
      on `U`, restricted from `ℂ` to `ℝ`, and zero smoothness on
      `(tsupport χ)ᶜ`.  The open cover
      `U ∪ (tsupport χ)ᶜ = univ` follows from `tsupport χ ⊆ U`.
   6. Let `G` be that Schwartz representative.  Agreement on
      `tsupport (dbarSchwartzCLM j φ)` follows from Step 1 and `χ = 1` on
      the neighborhood `V₁` of `K`.  The identity
      `(dbarSchwartzCLM j G) z = 0` on `K` follows because `G = F` on the
      same open neighborhood of `K`; after unfolding `dbarSchwartzCLM` and
      `SchwartzMap.lineDerivOp_apply_eq_fderiv`, holomorphicity of `F` gives
      the coordinate Cauchy-Riemann equation in direction `j`.

   The full local theorem is now checked and follows immediately from the
   checked algebraic localization lemma:

   ```lean
   theorem integral_holomorphic_mul_dbarSchwartz_eq_zero
       {m : ℕ}
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (F : ComplexChartSpace m -> ℂ)
       (hF_holo : DifferentiableOn ℂ F U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (j : Fin m) :
       (∫ z : ComplexChartSpace m, F z * (dbarSchwartzCLM j φ) z) = 0
   ```

   Pseudocode:

   ```lean
   obtain ⟨G, hFG, hG_dbar_zero⟩ :=
     exists_local_dbarClosed_schwartz_representative
       U hU_open F hF_holo φ hφ j
   exact
     integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz
       F G φ j hFG hG_dbar_zero
   ```

   The product-kernel consumer is now checked in the same file.  It rewrites
   the kernel by the checked product-kernel representation on the supported
   test `dbarSchwartzCLM j φ`, then applies the local holomorphic integral
   theorem to the scalar kernel `G ψ`.

   ```lean
   theorem regularizedEnvelope_productKernel_dbar_eq_zero
       {m : ℕ} {r : ℝ}
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
       (U0 : Set (ComplexChartSpace m))
       (hU0_open : IsOpen U0)
       (hG_holo :
         ∀ ψ, KernelSupportWithin ψ r -> DifferentiableOn ℂ (G ψ) U0)
       (hK_rep :
         ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
           (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               ∫ z : ComplexChartSpace m, G ψ z * φ z)
       (j : Fin m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ : KernelSupportWithin ψ r) :
       K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0

   theorem translationCovariantKernel_distributionalHolomorphic
       {m : ℕ} {r : ℝ} {ι : Type*} {l : Filter ι} [NeBot l]
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (ψι : ι -> SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_support :
         ∀ᶠ i in l, KernelSupportWithin (ψι i) r)
       (hψ_approx :
         ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
           Tendsto
             (fun i => realConvolutionTest θ (ψι i))
             l
             (nhds θ))
       (hdesc :
         ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
           (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
           K (schwartzTensorProduct₂ φ ψ) =
             Hdist (realConvolutionTest φ ψ))
       (hK_dbar_zero :
         ∀ (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
           (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0) :
       IsDistributionalHolomorphicOn Hdist U0
   ```

   Lean proof of the first theorem:

   ```lean
   rw [hK_rep (dbarSchwartzCLM j φ) ψ (hφ.dbar j) hψ]
   exact
     integral_holomorphic_mul_dbarSchwartz_eq_zero
       U0 hU0_open (G ψ) (hG_holo ψ hψ) φ hφ j
   ```

   The distributional-holomorphicity theorem above is now checked under the
   displayed concrete approximate-identity hypotheses.  The genuine
   approximate-identity construction that supplies `hψ_support` and
   `hψ_approx` is also checked in
   `SCV/DistributionalEOWApproxIdentity.lean`, so this layer now has all inputs
   needed to feed `SCV.distributionalHolomorphic_regular`.

   Lean proof transcript for the checked continuity-passage theorem:

   ```lean
   intro j φ hφ
   let θ : SchwartzMap (ComplexChartSpace m) ℂ := dbarSchwartzCLM j φ
   have hlim :
       Tendsto (fun i => Hdist (realConvolutionTest θ (ψι i)))
         l (nhds (Hdist θ)) :=
     (Hdist.continuous.tendsto θ).comp (hψ_approx θ)
   have hzero_eventually :
       ∀ᶠ i in l, Hdist (realConvolutionTest θ (ψι i)) = 0 := by
     filter_upwards [hψ_support] with i hi
     have hK0 := hK_dbar_zero j φ (ψι i) hφ hi
     have hdesc_i := hdesc θ (ψι i)
     rw [← hdesc_i]
     exact hK0
   have heq :
       (fun i => Hdist (realConvolutionTest θ (ψι i))) =ᶠ[l]
         fun _ => (0 : ℂ) :=
     hzero_eventually
   have hlim0 :
       Tendsto (fun i => Hdist (realConvolutionTest θ (ψι i)))
         l (nhds (0 : ℂ)) :=
     tendsto_const_nhds.congr' heq.symm
   exact tendsto_nhds_unique hlim hlim0
   ```

   The concrete theorem is:

   ```lean
   theorem exists_realConvolutionTest_approxIdentity
       {m : ℕ} {r : ℝ} (hr : 0 < r) :
       ∃ ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1) ∧
         (∀ n,
           KernelSupportWithin (ψn n)
             (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
         (∀ n, KernelSupportWithin (ψn n) r) ∧
         (∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
           Tendsto
             (fun n => realConvolutionTest θ (ψn n))
             atTop
             (nhds θ))
   ```

   With `SCV.distributionalHolomorphic_regular` now checked, the next honest
   assembly theorem in this chain is also checked in
   `SCV/DistributionalEOWKernelRecovery.lean`.  It turns a
   translation-covariant product kernel with holomorphic regularized scalar
   kernels into a holomorphic distribution representative:

   ```lean
   theorem regularizedEnvelope_holomorphicDistribution_from_productKernel
       {m : ℕ} {r : ℝ}
       (hm : 0 < m)
       (hr : 0 < r)
       (K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ)
       (G : SchwartzMap (Fin m -> ℝ) ℂ -> ComplexChartSpace m -> ℂ)
       (U0 : Set (ComplexChartSpace m))
       (hU0_open : IsOpen U0)
       (hcov : ProductKernelRealTranslationCovariantGlobal K)
       (hG_holo :
         ∀ ψ, KernelSupportWithin ψ r -> DifferentiableOn ℂ (G ψ) U0)
       (hK_rep :
         ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
           (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
           KernelSupportWithin ψ r ->
             K (schwartzTensorProduct₂ φ ψ) =
               ∫ z : ComplexChartSpace m, G ψ z * φ z) :
       ∃ H : ComplexChartSpace m -> ℂ,
         DifferentiableOn ℂ H U0 ∧
         ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ,
           RepresentsDistributionOnComplexDomain Hdist H U0 ∧
           ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
             (ψ : SchwartzMap (Fin m -> ℝ) ℂ),
             K (schwartzTensorProduct₂ φ ψ) =
               Hdist (realConvolutionTest φ ψ)
   ```

   Lean transcript:

   ```lean
   obtain ⟨ψn, hψ_norm, _hψ_small, hψ_support, hψ_approx⟩ :=
     exists_realConvolutionTest_approxIdentity (m := m) hr
   obtain ⟨Hdist, hdesc⟩ :=
     translationCovariantProductKernel_descends K hcov (ψn 0) (hψ_norm 0)
   have hK_dbar_zero :
       ∀ j φ ψ,
         SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
         KernelSupportWithin ψ r ->
           K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0 := by
     intro j φ ψ hφ hψ
     exact regularizedEnvelope_productKernel_dbar_eq_zero
       K G U0 hU0_open hG_holo hK_rep j φ hφ ψ hψ
   have hCR : IsDistributionalHolomorphicOn Hdist U0 :=
     translationCovariantKernel_distributionalHolomorphic
       (Hdist := Hdist) (K := K) (ψι := ψn)
       (hψ_support := Filter.Eventually.of_forall hψ_support)
       (hψ_approx := hψ_approx)
       (hdesc := hdesc)
       (hK_dbar_zero := hK_dbar_zero)
   obtain ⟨H, hH_holo, hRep⟩ :=
     distributionalHolomorphic_regular Hdist hm hU0_open hCR
   exact ⟨H, hH_holo, Hdist, hRep, hdesc⟩
   ```

   This theorem is not the final local distributional EOW envelope: it does
   not yet prove `H = Fplus/Fminus` on wedge pieces.  It is the exact
   Streater-Wightman kernel-recovery midpoint: the product kernel has descended
   to a distributional-holomorphic chart distribution, and the checked Weyl/CR
   regularity package converts that distribution into a holomorphic function.
   The downstream delta-limit agreement theorem
   `regularizedEnvelope_deltaLimit_agreesOnWedges` is now checked in
   `SCV/DistributionalEOWKernelRecovery.lean`; the remaining mathematical
   content is the upstream regularized-family construction plus local
   continuous EOW extraction/patching.

   The proof must be split into two honest pieces:

   ```lean
   theorem exists_normalized_schwartz_bump_kernelSupportWithin
       {m : ℕ} (ε : ℝ) (hε : 0 < ε) :
       ∃ ψ : SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ t, 0 ≤ (ψ t).re) ∧
         (∀ t, (ψ t).im = 0) ∧
         (∫ t : Fin m -> ℝ, ψ t = 1) ∧
         KernelSupportWithin ψ ε
   ```

   This theorem is now checked in
   `SCV/DistributionalEOWApproxIdentity.lean`.  It is the centered
   finite-dimensional version of the Wightman source theorem
   `exists_approx_identity_schwartz`, but ported into pure SCV rather than
   imported.  The proof uses `ContDiffBump (0 : Fin m -> ℝ)` with radii
   `ε / 4` and `ε / 2`, converts the real bump to a complex-valued compact
   supported smooth function, and normalizes by the nonzero integral supplied
   by `ContDiffBump.integral_pos`.  The support proof is simpler than the
   positive-time Wightman source: after normalizing,
   `tsupport_smul_subset_right` and the bump support theorem give containment
   in `closedBall 0 (ε / 2)`, hence in `closedBall 0 ε`.

   The sequence-selection wrapper with explicit fields is also checked:

   ```lean
   theorem exists_shrinking_normalized_schwartz_bump_sequence
       {m : ℕ} {r : ℝ} (hr : 0 < r) :
       ∃ ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ n t, 0 ≤ (ψn n t).re) ∧
         (∀ n t, (ψn n t).im = 0) ∧
         (∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1) ∧
         (∀ n,
           KernelSupportWithin (ψn n)
             (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
         (∀ n, KernelSupportWithin (ψn n) r)
   ```

   It chooses the preceding bump at radius
   `min (r / 2) (1 / (n + 1 : ℝ))`.  This is still genuine content, not the
   difficult convergence theorem: it supplies normalized compact kernels with
   shrinking support and the fixed-radius support hypothesis needed by
   `translationCovariantKernel_distributionalHolomorphic`.

   ```lean
   theorem tendsto_realConvolutionTest_of_shrinking_normalized_support
       {m : ℕ}
       (ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
       (hψ_real : ∀ n t, (ψn n t).im = 0)
       (hψ_norm : ∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1)
       (hψ_support :
         ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
       ∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
         Tendsto
           (fun n => realConvolutionTest θ (ψn n))
           atTop
           (nhds θ)
   ```

   The convergence proof should use the Schwartz seminorm topology directly.
   The implementation belongs in the approximate-identity companion, not in
   `SCV/DistributionalEOWKernel.lean`.  The first line of the proof is the
   standard `WithSeminorms` reduction:

   ```lean
   rw [(schwartz_withSeminorms ℂ (ComplexChartSpace m) ℂ).tendsto_nhds_atTop _ _]
   intro ⟨k, l⟩ ε hε
   ```

   and the goal is to prove, eventually in `n`,

   ```lean
   SchwartzMap.seminorm ℂ k l
     (realConvolutionTest θ (ψn n) - θ) < ε
   ```

   The proof uses the following checked local theorem slots.  They remain
   documented here because they are the implementation transcript for the
   convergence theorem.

   ```lean
   theorem integral_norm_eq_one_of_real_nonneg_normalized
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_nonneg : ∀ t : Fin m -> ℝ, 0 ≤ (ψ t).re)
       (hψ_real : ∀ t : Fin m -> ℝ, (ψ t).im = 0)
       (hψ_norm : ∫ t : Fin m -> ℝ, ψ t = 1) :
       ∫ t : Fin m -> ℝ, ‖ψ t‖ = 1
   ```

   Proof transcript: prove pointwise
   `‖ψ t‖ = (ψ t).re` by `Complex.ext`, `Complex.norm_real`, and
   `Real.norm_eq_abs`; then use
   `integral_congr_ae`, `integral_re ψ.integrable`, and `hψ_norm`.

   ```lean
   theorem norm_realEmbed_le (t : Fin m -> ℝ) :
       ‖realEmbed t‖ ≤ ‖t‖
   ```

   Proof transcript: rewrite by `pi_norm_le_iff_of_nonneg`; each coordinate is
   `Complex.norm_real (t i)` and is bounded by `norm_le_pi_norm t i`.

   ```lean
   theorem continuous_realEmbed :
       Continuous (realEmbed : (Fin m -> ℝ) -> ComplexChartSpace m)
   ```

   Proof transcript: use `continuous_pi`; each coordinate is
   `Complex.continuous_ofReal.comp (continuous_apply i)`.

   ```lean
   theorem kernel_eq_zero_of_not_mem_closedBall
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) {r : ℝ} {t : Fin m -> ℝ}
       (hψ : KernelSupportWithin ψ r)
       (ht : t ∉ Metric.closedBall (0 : Fin m -> ℝ) r) :
       ψ t = 0
   ```

   Proof transcript: apply `image_eq_zero_of_notMem_tsupport`; membership in
   `tsupport ψ` would contradict `ht` through `hψ`.

   ```lean
   theorem iteratedFDeriv_sub_realEmbed_right
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (t : Fin m -> ℝ) (l : ℕ) (z : ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (fun z : ComplexChartSpace m => θ (z - realEmbed t)) z =
         iteratedFDeriv ℝ l
           (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t)
   ```

   Proof transcript: `simpa [sub_eq_add_neg]` using
   `iteratedFDeriv_comp_add_right` with translation vector `-(realEmbed t)`.

   ```lean
   theorem integrable_smul_iteratedFDeriv_translate
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (l : ℕ) (z : ComplexChartSpace m) :
       Integrable (fun t : Fin m -> ℝ =>
         (ψ t) • iteratedFDeriv ℝ l
           (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t))
   ```

   Proof transcript: set `C = SchwartzMap.seminorm ℂ 0 l θ`; dominate the
   norm by `C * ‖ψ t‖` using
   `SchwartzMap.norm_iteratedFDeriv_le_seminorm`; integrability is
   `ψ.integrable.norm.const_mul C`.  Measurability comes from
   `continuous_realEmbed`, continuity of
   `θ.smooth l |>.continuous_iteratedFDeriv`, and continuity of scalar
   multiplication.

   The base case of derivative-through-convolution is already an independent
   theorem:

   ```lean
   theorem iteratedFDeriv_zero_realConvolutionTest_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) :
       iteratedFDeriv ℝ 0
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z =
         ∫ t : Fin m -> ℝ,
           (ψ t) • iteratedFDeriv ℝ 0
             (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t)
   ```

   Proof transcript: extensionality on the `Fin 0` multilinear map, rewrite by
   `iteratedFDeriv_zero_apply`, move application through the integral by
   `ContinuousMultilinearMap.integral_apply`, using
   `integrable_smul_iteratedFDeriv_translate θ ψ 0 z`, and finish by
   `realConvolutionTest_apply`.

   The derivative-through-convolution theorem is the first nontrivial
   analytic bridge beyond that base case.  Its exact target is:

   ```lean
   theorem iteratedFDeriv_realConvolutionTest_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (l : ℕ) (z : ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z =
         ∫ t : Fin m -> ℝ,
           (ψ t) •
           iteratedFDeriv ℝ l
               (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t)
   ```

   Before the all-orders theorem, the first derivative must be checked as its
   own concrete package.  The required real-linear embedding is not an
   abstract route assumption; it is the coordinate map already used by the
   shear:

   ```lean
   private def realEmbedCLMApprox :
       (Fin m -> ℝ) ->L[ℝ] ComplexChartSpace m :=
     ContinuousLinearMap.pi fun i =>
       Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

   @[simp] private theorem realEmbedCLMApprox_apply
       (t : Fin m -> ℝ) :
       realEmbedCLMApprox t = realEmbed t
   ```

   Proof transcript: extensionality in `i`, then
   `simp [realEmbedCLMApprox, realEmbed]`.  Keeping this helper private in the
   approximate-identity file is acceptable: it exposes no new mathematical
   theorem surface and only gives Lean the continuous-linear structure needed
   to compute the derivative of the shear.

   The pointwise base derivative of the sheared tensor product is:

   ```lean
   theorem fderiv_shearedTensor_base_apply
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z v : ComplexChartSpace m) (t : Fin m -> ℝ) :
       fderiv ℝ
         (fun p : ComplexChartSpace m × (Fin m -> ℝ) =>
           θ (p.1 - realEmbed p.2) * ψ p.2)
         (z, t)
         ((ContinuousLinearMap.inl ℝ
           (ComplexChartSpace m) (Fin m -> ℝ)) v)
       =
       (ψ t) •
         fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
           (z - realEmbed t) v
   ```

   Lean proof transcript.  Set
   ```
   fstCLM := ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m -> ℝ)
   sndCLM := ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m -> ℝ)
   L := fstCLM - realEmbedCLMApprox.comp sndCLM
   A p := θ (p.1 - realEmbed p.2)
   B p := ψ p.2
   ```
   Prove `hL_apply : L p = p.1 - realEmbed p.2` by `simp`.  Rewrite
   `A = fun p => θ (L p)`, then get
   ```
   hA_deriv :
     HasFDerivAt A ((fderiv ℝ θ (z - realEmbed t)).comp L) (z,t)
   ```
   from `θ.differentiableAt.hasFDerivAt.comp`.
   Similarly,
   ```
   hB_deriv :
     HasFDerivAt B ((fderiv ℝ ψ t).comp sndCLM) (z,t)
   ```
   from `ψ.differentiableAt.hasFDerivAt.comp`.  Apply
   `hA_deriv.mul hB_deriv`, rewrite the original function as
   `fun p => A p * B p`, use `.fderiv`, and evaluate on `inl v`.  The
   `B`-derivative term vanishes because `sndCLM (inl v) = 0`; the shear term
   is `v` because `realEmbed 0 = 0`.  The final simplification is:
   ```lean
   have hreal_zero : realEmbed (0 : Fin m -> ℝ) = 0 := by
     ext i
     simp [realEmbed]
   simp [A, B, L, fstCLM, sndCLM, hreal_zero, smul_eq_mul, mul_comm]
   ```

   The corresponding checked bridge into the existing fiber-integral
   infrastructure is:

   ```lean
   theorem baseFDeriv_realConvolution_kernel_apply
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z v : ComplexChartSpace m) (t : Fin m -> ℝ) :
       baseFDerivSchwartz
         ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
             (realConvolutionShearCLE m))
           (schwartzTensorProduct₂ θ ψ)) (z, t) v =
       (ψ t) •
         fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
           (z - realEmbed t) v
   ```

   Proof transcript: rewrite `baseFDerivSchwartz_apply`, then `change` the
   differentiated function to
   `fun p => θ (p.1 - realEmbed p.2) * ψ p.2`; finish by
   `fderiv_shearedTensor_base_apply`.

   The first derivative of the convolution test is then:

   ```lean
   theorem fderiv_realConvolutionTest_apply_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z v : ComplexChartSpace m) :
       fderiv ℝ
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z v =
       ∫ t : Fin m -> ℝ,
         (ψ t) •
           fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
             (z - realEmbed t) v
   ```

   Proof transcript.  Let
   ```
   F :=
     (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (realConvolutionShearCLE m)) (schwartzTensorProduct₂ θ ψ)
   ```
   and rewrite the left side to
   `fderiv ℝ (complexRealFiberIntegralRaw F) z v`.  Use
   `congrFun (fderiv_complexRealFiberIntegralRaw_eq F) z` to replace the
   derivative by `complexRealFiberIntegralRaw (baseFDerivSchwartz F) z`.
   Change this to
   `(∫ t, baseFDerivSchwartz F (z,t)) v`, move evaluation through the
   Bochner integral by
   `ContinuousLinearMap.integral_apply
     (integrable_complexRealFiber (baseFDerivSchwartz F) z) v`,
   and close by `integral_congr_ae` plus
   `baseFDeriv_realConvolution_kernel_apply`.

   The unevaluated continuous-linear-map version is also part of this stage:

   ```lean
   theorem integrable_smul_fderiv_translate
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) :
       Integrable (fun t : Fin m -> ℝ =>
         (ψ t) •
           fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
             (z - realEmbed t))

   theorem fderiv_realConvolutionTest_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (z : ComplexChartSpace m) :
       fderiv ℝ
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z =
       ∫ t : Fin m -> ℝ,
         (ψ t) •
           fderiv ℝ (θ : ComplexChartSpace m -> ℂ)
             (z - realEmbed t)
   ```

   Proof transcript: for integrability, reuse
   `integrable_complexRealFiber (baseFDerivSchwartz F) z` for the same
   sheared tensor `F` and transfer by ae-equality, extensional in the
   continuous-linear-map argument, using
   `baseFDeriv_realConvolution_kernel_apply`.  For the equality, ext on a
   direction `v`, move evaluation through the integral using
   `ContinuousLinearMap.integral_apply`, and apply
   `fderiv_realConvolutionTest_apply_eq_integral`.

   The all-orders theorem should not be proved by fragile `Fin 1`
   curry/uncurry conversions.  The clean route is to commute **directional**
   derivatives through the convolution test, then use
   `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`.

   First prove:

   ```lean
   theorem lineDerivOp_realConvolutionTest
       (v : ComplexChartSpace m)
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       ∂_{v} (realConvolutionTest θ ψ) =
         realConvolutionTest (∂_{v} θ) ψ
   ```

   Proof transcript: ext on `z`; rewrite the left side with
   `SchwartzMap.lineDerivOp_apply_eq_fderiv`; use
   `fderiv_realConvolutionTest_apply_eq_integral`; rewrite the right side by
   `realConvolutionTest_apply`; close by `integral_congr_ae`,
   `SchwartzMap.lineDerivOp_apply_eq_fderiv`, and commutativity of complex
   multiplication.

   Then prove the iterated directional version:

   ```lean
   theorem iteratedLineDerivOp_realConvolutionTest
       {l : ℕ} (u : Fin l -> ComplexChartSpace m)
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ) :
       ∂^{u} (realConvolutionTest θ ψ) =
         realConvolutionTest (∂^{u} θ) ψ
   ```

   Proof transcript: induction on `l`.  The zero case is
   `LineDeriv.iteratedLineDerivOp_fin_zero`.  In the successor case rewrite
   both sides by `LineDeriv.iteratedLineDerivOp_succ_left`, apply the
   induction hypothesis to `Fin.tail u`, and finish with
   `lineDerivOp_realConvolutionTest (u 0) (∂^{Fin.tail u} θ) ψ`.

   The applied all-orders derivative-through-convolution theorem is then:

   ```lean
   theorem iteratedFDeriv_realConvolutionTest_eq_integral_apply
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (l : ℕ) (z : ComplexChartSpace m)
       (v : Fin l -> ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (realConvolutionTest θ ψ : ComplexChartSpace m -> ℂ) z v =
       ∫ t : Fin m -> ℝ,
         (ψ t) *
           iteratedFDeriv ℝ l
             (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) v
   ```

   Proof transcript: rewrite the left side to
   `(∂^{v} (realConvolutionTest θ ψ)) z` using
   `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`, then use
   `iteratedLineDerivOp_realConvolutionTest` and
   `realConvolutionTest_apply`.  Convert
   `(∂^{v} θ) (z - realEmbed t)` back to
   `iteratedFDeriv ℝ l θ (z - realEmbed t) v` pointwise by
   `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`; finish with
   commutativity of multiplication under `integral_congr_ae`.

   The non-applied continuous-multilinear theorem above is recovered by
   extensionality and `ContinuousMultilinearMap.integral_apply` using the
   already checked `integrable_smul_iteratedFDeriv_translate`.

   With `hψ_norm`, the exact consumer form is:

   ```lean
   theorem iteratedFDeriv_realConvolutionTest_sub_eq_integral_apply
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_norm : ∫ t : Fin m -> ℝ, ψ t = 1)
       (l : ℕ) (z : ComplexChartSpace m)
       (v : Fin l -> ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (realConvolutionTest θ ψ - θ : ComplexChartSpace m -> ℂ) z v =
       ∫ t : Fin m -> ℝ,
         (ψ t) *
           (iteratedFDeriv ℝ l
              (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) v -
            iteratedFDeriv ℝ l
              (θ : ComplexChartSpace m -> ℂ) z v)

   theorem iteratedFDeriv_realConvolutionTest_sub_eq_integral
       (θ : SchwartzMap (ComplexChartSpace m) ℂ)
       (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
       (hψ_norm : ∫ t : Fin m -> ℝ, ψ t = 1)
       (l : ℕ) (z : ComplexChartSpace m) :
       iteratedFDeriv ℝ l
         (realConvolutionTest θ ψ - θ : ComplexChartSpace m -> ℂ) z =
         ∫ t : Fin m -> ℝ,
           (ψ t) •
             (iteratedFDeriv ℝ l
                (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) -
              iteratedFDeriv ℝ l
                (θ : ComplexChartSpace m -> ℂ) z)
   ```

   Proof transcript for the non-applied theorem: rewrite the Schwartz-map
   subtraction as function addition with a negative term, apply
   `iteratedFDeriv_add_apply` and `iteratedFDeriv_neg_apply`, then insert
   `iteratedFDeriv_realConvolutionTest_eq_integral`.  Rewrite
   ```
   ∫ t, (ψ t) • iteratedFDeriv ℝ l θ z
   ```
   as `iteratedFDeriv ℝ l θ z` by `integral_smul_const` and `hψ_norm`.
   Use `integral_sub` at the continuous-multilinear-map level, with
   integrability from `integrable_smul_iteratedFDeriv_translate` and
   `ψ.integrable.smul_const`, and finish by pointwise `smul_sub`.  The applied
   theorem follows afterward by applying both sides to `v` and moving
   evaluation through the integral with `ContinuousMultilinearMap.integral_apply`;
   the final scalar simplification is `smul_eq_mul` and `mul_sub`.

   The global small-translation estimate is the real mathematical heart of
   the convergence proof.  The endorsed Lean route is the direct mean-value
   estimate below, not the older compact/tail split.  For Schwartz functions
   the mean-value proof is stronger and shorter: one derivative is spent, and
   the polynomial weight at `z` is compared to the polynomial weight at
   `z - s • realEmbed t` using `‖t‖ ≤ 1`.

   First prove the quantitative linear estimate:

   ```lean
   theorem exists_weighted_iteratedFDeriv_realTranslate_sub_le_linear
       (θ : SchwartzMap (ComplexChartSpace m) ℂ) (k l : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ (z : ComplexChartSpace m) (t : Fin m -> ℝ),
           ‖t‖ ≤ 1 ->
             ‖z‖ ^ k *
               ‖iteratedFDeriv ℝ l
                   (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) -
                 iteratedFDeriv ℝ l
                   (θ : ComplexChartSpace m -> ℂ) z‖ ≤ C * ‖t‖
   ```

   Lean proof transcript.  Let
   `D w = iteratedFDeriv ℝ l (θ : ComplexChartSpace m -> ℂ) w` and set
   ```
   C = 2 ^ (k - 1) *
     (SchwartzMap.seminorm ℂ k (l + 1) θ +
      SchwartzMap.seminorm ℂ 0 (l + 1) θ)
   ```
   (any nonnegative larger constant is fine).  For fixed `z,t`, define the
   one-variable path
   ```
   γ s = ‖z‖ ^ k • D (z - s • realEmbed t)
   ```
   and apply `norm_image_sub_le_of_norm_deriv_le_segment_01'` on `[0,1]`.
   The derivative is
   ```
   ‖z‖ ^ k •
     fderiv ℝ D (z - s • realEmbed t) (-(realEmbed t))
   ```
   by the chain rule.  Use `norm_fderiv_iteratedFDeriv` to rewrite
   `‖fderiv ℝ D w‖` as
   `‖iteratedFDeriv ℝ (l + 1) (θ : ComplexChartSpace m -> ℂ) w‖`.
   If `s ∈ Set.Ico 0 1` and `‖t‖ ≤ 1`, then
   `norm_realEmbed_le t` gives `‖s • realEmbed t‖ ≤ 1` and therefore
   ```
   ‖z‖ = ‖(z - s • realEmbed t) + s • realEmbed t‖
        ≤ ‖z - s • realEmbed t‖ + 1.
   ```
   The elementary inequality `add_pow_le` yields
   ```
   ‖z‖ ^ k * ‖D_{l+1} θ (z - s • realEmbed t)‖
     ≤ 2 ^ (k - 1) *
       (SchwartzMap.seminorm ℂ k (l + 1) θ +
        SchwartzMap.seminorm ℂ 0 (l + 1) θ).
   ```
   Multiplying by `‖realEmbed t‖ ≤ ‖t‖` gives the derivative bound required by
   the mean-value theorem.  Finally identify
   `γ 1 - γ 0` with
   `‖z‖ ^ k • (D (z - realEmbed t) - D z)` and remove the scalar norm.

   The qualitative small-translation theorem is then just this linear estimate
   with `δ = min 1 (ε / (C + 1))`:

   ```lean
   theorem weighted_iteratedFDeriv_realTranslate_sub_tendsto_zero
       (θ : SchwartzMap (ComplexChartSpace m) ℂ) (k l : ℕ) :
       ∀ ε > 0, ∃ δ > 0, ∀ (z : ComplexChartSpace m) (t : Fin m -> ℝ),
         ‖t‖ < δ ->
           ‖z‖ ^ k *
             ‖iteratedFDeriv ℝ l
                 (θ : ComplexChartSpace m -> ℂ) (z - realEmbed t) -
               iteratedFDeriv ℝ l
                 (θ : ComplexChartSpace m -> ℂ) z‖ < ε
   ```

   The convergence theorem then has a short transcript.  Given `k,l,ε`, take
   `δ` from the weighted translation theorem with `ε / 2`.  From
   `tendsto_one_div_add_atTop_nhds_zero_nat`, choose `N` so
   `1 / (n + 1 : ℝ) < δ` for `n ≥ N`.  For such `n`, if
   `ψn n t ≠ 0`, `hψ_support n` and
   `kernel_eq_zero_of_not_mem_closedBall` force `‖t‖ ≤ 1 / (n + 1) < δ`.
   Hence the weighted derivative difference is `< ε / 2` on the support and
   the integrand is zero off the support.  Using
   `iteratedFDeriv_realConvolutionTest_sub_eq_integral`,
   `norm_integral_le_integral_norm`, `norm_smul`, and
   `integral_norm_eq_one_of_real_nonneg_normalized`, prove for every `z`
   ```
   ‖z‖ ^ k *
     ‖iteratedFDeriv ℝ l
       (realConvolutionTest θ (ψn n) - θ : ComplexChartSpace m -> ℂ) z‖
       ≤ ε / 2.
   ```
   Then apply
   ```lean
   SchwartzMap.seminorm_le_bound ℂ k l
     (realConvolutionTest θ (ψn n) - θ)
   ```
   and finish with `half_lt_self hε`.

   Finally, package the checked bump sequence:

   ```lean
   theorem exists_realConvolutionTest_approxIdentity
       {m : ℕ} {r : ℝ} (hr : 0 < r) :
       ∃ ψn : ℕ -> SchwartzMap (Fin m -> ℝ) ℂ,
         (∀ n, ∫ t : Fin m -> ℝ, ψn n t = 1) ∧
         (∀ n,
           KernelSupportWithin (ψn n)
             (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
         (∀ n, KernelSupportWithin (ψn n) r) ∧
         (∀ θ : SchwartzMap (ComplexChartSpace m) ℂ,
           Tendsto
             (fun n => realConvolutionTest θ (ψn n))
             atTop
             (nhds θ))
   ```

   Its proof uses `exists_shrinking_normalized_schwartz_bump_sequence hr`;
   the nonnegativity and real-valuedness fields are kept internally to call
   `tendsto_realConvolutionTest_of_shrinking_normalized_support`, while the
   public theorem only exports the fields consumed by
   `translationCovariantKernel_distributionalHolomorphic`.

   This approximate-identity package is now checked in
   `SCV/DistributionalEOWApproxIdentity.lean`.  It is the concrete input
   consumed by the checked
   `translationCovariantKernel_distributionalHolomorphic`; no opaque
   approximate-identity assumption is used.
7. Apply `distributionalHolomorphic_regular` to obtain a genuine holomorphic
   function `H` on `U0` representing `Hdist`.

   Lean-ready transcript for `distributionalHolomorphic_regular`.  This is the
   standard local Weyl regularity theorem for the `∂bar` complex, specialized
   to the repo's complex-chart tempered-distribution surface.  It is pure SCV:
   no OS, Wightman, BHW, Hamiltonian, or boundary-value hypotheses enter this
   theorem.

   The public theorem surface remains:

   ```lean
   theorem distributionalHolomorphic_regular
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hCR : IsDistributionalHolomorphicOn Hdist U0) :
       ∃ H : ComplexChartSpace m -> ℂ,
         DifferentiableOn ℂ H U0 ∧
         RepresentsDistributionOnComplexDomain Hdist H U0
   ```

   The first calculus and chart-transport layers are checked in
   `SCV/DistributionalEOWRegularity.lean`.  The final theorem must now be
   implemented in a new downstream file, e.g.
   `SCV/DistributionalEOWHolomorphic.lean`, importing
   `SCV/DistributionalEOWRegularity.lean` and the checked open-set Weyl module
   `SCV/EuclideanWeylOpen.lean`.  Do not import `EuclideanWeylOpen.lean` back
   into `DistributionalEOWRegularity.lean`: `EuclideanWeylRepresentation.lean`
   already imports `DistributionalEOWRegularity.lean`, so doing that would
   create an import cycle.

   The first internal layer is the test-function `∂/∂z_j` operator, support
   preservation, commutation of the real coordinate derivatives, and the real
   Laplacian identity.  These are genuine finite-dimensional calculus facts,
   not wrappers.  The Lean implementation should be staged so that the
   support/commutation package is checked before the Laplacian and Weyl
   layers are attempted.

   ```lean
   def dzSchwartzCLM {m : ℕ} (j : Fin m) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ :=
     (1 / 2 : ℂ) •
       (directionalDerivSchwartzCLM (complexRealDir j) -
         Complex.I • directionalDerivSchwartzCLM (complexImagDir j))

   theorem dzSchwartzCLM_tsupport_subset
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
         ComplexChartSpace m -> ℂ) ⊆
       tsupport (φ : ComplexChartSpace m -> ℂ)

   theorem SupportsInOpen.dz
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0)
       (j : Fin m) :
       SupportsInOpen ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
         ComplexChartSpace m -> ℂ) U0

   theorem dbar_dzSchwartzCLM_comm
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       dbarSchwartzCLM j (dzSchwartzCLM j φ) =
         dzSchwartzCLM j (dbarSchwartzCLM j φ)
   ```

   The first checked slice of `SCV/DistributionalEOWRegularity.lean` now
   contains the following local calculus package:

   ```lean
   def dzSchwartzCLM {m : ℕ} (j : Fin m) :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ

   theorem dzSchwartzCLM_tsupport_subset
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       tsupport ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
         ComplexChartSpace m -> ℂ) ⊆
       tsupport (φ : ComplexChartSpace m -> ℂ)

   theorem SupportsInOpen.dz
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0)
       (j : Fin m) :
       SupportsInOpen ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
         ComplexChartSpace m -> ℂ) U0

   theorem lineDerivOp_comm_complex
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (v w : ComplexChartSpace m) :
       ∂_{v} ((∂_{w} φ : SchwartzMap (ComplexChartSpace m) ℂ)) =
         ∂_{w} ((∂_{v} φ : SchwartzMap (ComplexChartSpace m) ℂ))

   theorem directionalDerivSchwartzCLM_comm
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (v w : ComplexChartSpace m) :
       directionalDerivSchwartzCLM v (directionalDerivSchwartzCLM w φ) =
         directionalDerivSchwartzCLM w (directionalDerivSchwartzCLM v φ)

   theorem dbar_dzSchwartzCLM_comm
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       dbarSchwartzCLM j (dzSchwartzCLM j φ) =
         dzSchwartzCLM j (dbarSchwartzCLM j φ)
   ```

   Proof transcript for this first slice.  The definition of `dzSchwartzCLM`
   is the standard Wirtinger operator
   `1/2 (D_{x_j} - i D_{y_j})` on tests.  Its support lemma is literally the
   checked `dbarSchwartzCLM_tsupport_subset` proof with `Complex.I` replaced
   by `-Complex.I`: use `directionalDerivSchwartzCLM_tsupport_subset` for
   both real coordinate derivatives, then use `tsupport_smul_subset_right` and
   `tsupport_add` for the finite linear combination.  `SupportsInOpen.dz`
   follows by the same `subset_tsupport` argument as `SupportsInOpen.dbar`.
   The commutation lemma is copied from the checked
   `SCV.TranslationDifferentiation.lineDerivOp_comm` proof, with domain
   `ComplexChartSpace m`: at each point, `φ.contDiffAt 2` gives
   `isSymmSndFDerivAt`; converting both iterated line derivatives to
   `iteratedFDeriv ℝ 2` and swapping the two inputs proves equality.  Finally
   `dbar_dzSchwartzCLM_comm` expands the two continuous linear maps and uses
   the real-direction commutation for `complexRealDir j` and
   `complexImagDir j`.  The scalar algebra is the identity
   `(D_x + i D_y)(D_x - i D_y) = (D_x - i D_y)(D_x + i D_y)` after the two
   mixed derivatives have been identified.

   The second internal layer is now also checked, with one important Lean-side
   correction.  The repo's `ComplexChartSpace m` is the plain finite Pi chart
   carrying the existing Schwartz-space norm, not Mathlib's `PiLp 2`
   Euclidean type.  Therefore the production theorem must not impose a fake
   `InnerProductSpace ℝ (ComplexChartSpace m)` instance just to call
   `LineDeriv.laplacianCLM`.  Instead, define the honest coordinate Laplacian
   used by the SCV proof:

   ```lean
   def complexChartLaplacianSchwartzCLM {m : ℕ} :
       SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ]
         SchwartzMap (ComplexChartSpace m) ℂ :=
     ∑ j : Fin m,
       ((directionalDerivSchwartzCLM (complexRealDir j)).comp
           (directionalDerivSchwartzCLM (complexRealDir j)) +
         (directionalDerivSchwartzCLM (complexImagDir j)).comp
           (directionalDerivSchwartzCLM (complexImagDir j)))

   theorem complexChartLaplacianSchwartzCLM_apply
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       complexChartLaplacianSchwartzCLM φ =
         ∑ j : Fin m,
           (directionalDerivSchwartzCLM (complexRealDir j)
               (directionalDerivSchwartzCLM (complexRealDir j) φ) +
             directionalDerivSchwartzCLM (complexImagDir j)
               (directionalDerivSchwartzCLM (complexImagDir j) φ))

   theorem four_dbar_dzSchwartzCLM_eq_real_imag_second
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       (4 : ℂ) • dbarSchwartzCLM j (dzSchwartzCLM j φ) =
         directionalDerivSchwartzCLM (complexRealDir j)
             (directionalDerivSchwartzCLM (complexRealDir j) φ) +
           directionalDerivSchwartzCLM (complexImagDir j)
             (directionalDerivSchwartzCLM (complexImagDir j) φ)

   theorem complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       complexChartLaplacianSchwartzCLM φ =
         (4 : ℂ) •
           ∑ j : Fin m, dbarSchwartzCLM j (dzSchwartzCLM j φ)

   theorem local_laplacian_zero_of_distributionalHolomorphic
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hCR : IsDistributionalHolomorphicOn Hdist U0)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0) :
       Hdist (complexChartLaplacianSchwartzCLM φ) = 0
   ```

   Proof transcript for the checked coordinate Laplacian layer.  The apply
   theorem is just evaluation of a finite sum of continuous linear maps.
   For each coordinate, expand `dbarSchwartzCLM` and `dzSchwartzCLM`, use
   `directionalDerivSchwartzCLM_comm` to identify the mixed derivatives, and
   simplify the scalar identity `I^2 = -1`; this proves
   `four_dbar_dzSchwartzCLM_eq_real_imag_second`.  Summing over `Fin m` gives
   `complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz`.  The distributional
   harmonicity theorem then pushes `Hdist` through the scalar and finite sum
   and applies `hCR j (dzSchwartzCLM j φ) (hφ.dz j)`.

   The older candidate theorem below was intentionally rejected during
   implementation:

   ```lean
   theorem laplacianSchwartzCLM_eq_four_sum_dbar_dz
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       LineDeriv.laplacianCLM ℝ (ComplexChartSpace m)
           (SchwartzMap (ComplexChartSpace m) ℂ) φ =
           (4 : ℂ) •
           ∑ j : Fin m, dbarSchwartzCLM j (dzSchwartzCLM j φ)

   theorem local_laplacian_zero_of_distributionalHolomorphic
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hCR : IsDistributionalHolomorphicOn Hdist U0)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0) :
       Hdist
         (LineDeriv.laplacianCLM ℝ (ComplexChartSpace m)
               (SchwartzMap (ComplexChartSpace m) ℂ) φ) = 0
   ```

   It is mathematically equivalent only after transporting the plain chart to
   a Euclidean `PiLp 2` model, but it is not a Lean-ready statement on
   `ComplexChartSpace m` itself.  The Euclidean transport belongs in the Weyl
   theorem proof, where norm-equivalence and chart linear-equivalence
   bookkeeping are unavoidable and mathematically meaningful.

   The complex-chart Weyl theorem is now just the honest transport of the
   checked Euclidean open-set Weyl theorem through
   `complexChartEuclideanCLE`.  The theorem surface remains useful because it
   hides no mathematics: it packages the already checked coordinate-Laplacian
   identity, support transport, volume-preserving chart change, and Euclidean
   representative pullback.

   ```lean
   theorem weyl_laplacian_distribution_regular_on_open
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hm : 0 < m)
       (hΔ :
         ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
           SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
             T (complexChartLaplacianSchwartzCLM φ) = 0) :
       ∃ H : ComplexChartSpace m -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H U0 ∧
         RepresentsDistributionOnComplexDomain T H U0
   ```

   Lean proof transcript for this transported Weyl theorem:

   ```lean
   let e := complexChartEuclideanCLE m
   let V : Set (EuclideanSpace ℝ (Fin (m * 2))) := e '' U0
   let TE := transportedDistributionToEuclidean T

   have hV_open : IsOpen V :=
     e.toHomeomorph.isOpenMap U0 hU0_open

   have hΔE :
       ∀ ψ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ,
         SupportsInOpen (ψ : EuclideanSpace ℝ (Fin (m * 2)) -> ℂ) V ->
           TE (LineDeriv.laplacianCLM ℝ
             (EuclideanSpace ℝ (Fin (m * 2)))
             (SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) ψ) = 0 := by
     intro ψ hψ
     let ψc := (complexChartEuclideanSchwartzCLE m).symm ψ
     have hψc : SupportsInOpen (ψc : ComplexChartSpace m -> ℂ) U0 :=
       supportsInOpen_transport_to_euclidean hψ
     have hzero : T (complexChartLaplacianSchwartzCLM ψc) = 0 :=
       hΔ ψc hψc
     have htransport :
         (complexChartEuclideanSchwartzCLE m).symm
           (LineDeriv.laplacianCLM ℝ
             (EuclideanSpace ℝ (Fin (m * 2)))
             (SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) ψ)
           =
         complexChartLaplacianSchwartzCLM ψc := by
       apply (complexChartEuclideanSchwartzCLE m).injective
       simpa [ψc] using
         (complexChartLaplacianSchwartzCLM_transport ψc).symm
     simpa [TE, transportedDistributionToEuclidean, htransport] using hzero

   obtain ⟨HE, hHE_smooth, hHE_rep⟩ :=
     euclidean_weyl_laplacian_distribution_regular_on_open
       TE hV_open hΔE

   refine ⟨fun z => HE (e z), ?_, ?_⟩
   · exact hHE_smooth.comp
       (e.contDiff.contDiffOn)
       (fun z hz => Set.mem_image_of_mem e hz)
   · exact representsDistributionOnComplexDomain_of_euclidean
       T HE hHE_rep
   ```

   The `hm : 0 < m` hypothesis is the current positive-real-dimension entry
   point needed by the checked Euclidean Weyl bump primitive; internally it
   supplies `[Nonempty (Fin (m * 2))]` for the Euclidean theorem.  The theorem-2
   OS45 callers have positive chart dimension, so this does not weaken the
   active route.  A zero-dimensional bookkeeping theorem can be added later
   only if a dimension-free SCV caller actually appears.

   The chart equivalence, Schwartz-space equivalence, and their apply lemmas
   are checked in `SCV/DistributionalEOWRegularity.lean`; the coordinate-
   direction lemmas, Laplacian transport, support transport, and Euclidean
   representative pullback are checked there as well:

   ```lean
   noncomputable def complexChartEuclideanCLE (m : ℕ) :
       ComplexChartSpace m ≃L[ℝ] EuclideanSpace ℝ (Fin (m * 2)) :=
     (complexChartRealFlattenCLE m).trans
       (EuclideanSpace.equiv (Fin (m * 2)) ℝ).symm

   noncomputable def complexChartEuclideanSchwartzCLE (m : ℕ) :
       SchwartzMap (ComplexChartSpace m) ℂ ≃L[ℂ]
         SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ

   theorem complexChartEuclideanSchwartzCLE_apply
       (m : ℕ) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (x : EuclideanSpace ℝ (Fin (m * 2))) :
       complexChartEuclideanSchwartzCLE m φ x =
         φ ((complexChartEuclideanCLE m).symm x)

   theorem complexChartEuclideanSchwartzCLE_symm_apply
       (m : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ)
       (z : ComplexChartSpace m) :
       (complexChartEuclideanSchwartzCLE m).symm φ z =
         φ (complexChartEuclideanCLE m z)

   theorem complexChartEuclideanCLE_realDir
       (j : Fin m) :
       complexChartEuclideanCLE m (complexRealDir j) =
         (EuclideanSpace.equiv (Fin (m * 2)) ℝ).symm
           (fun k => if k = finProdFinEquiv (j, (0 : Fin 2)) then 1 else 0)

   theorem complexChartEuclideanCLE_imagDir
       (j : Fin m) :
       complexChartEuclideanCLE m (complexImagDir j) =
         (EuclideanSpace.equiv (Fin (m * 2)) ℝ).symm
           (fun k => if k = finProdFinEquiv (j, (1 : Fin 2)) then 1 else 0)

   theorem complexChartLaplacianSchwartzCLM_transport
       (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
       complexChartEuclideanSchwartzCLE m
           (complexChartLaplacianSchwartzCLM φ) =
         LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ (Fin (m * 2)))
           (SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ)
           (complexChartEuclideanSchwartzCLE m φ)

   def transportedDistributionToEuclidean
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ) :
       SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ ->L[ℂ] ℂ :=
     T.comp
       ((complexChartEuclideanSchwartzCLE m).symm :
         SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ ->L[ℂ]
           SchwartzMap (ComplexChartSpace m) ℂ)

   theorem supportsInOpen_transport_to_euclidean
       {φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ}
       {U0 : Set (ComplexChartSpace m)}
       (hφ : SupportsInOpen (φ : EuclideanSpace ℝ (Fin (m * 2)) -> ℂ)
         ((complexChartEuclideanCLE m) '' U0)) :
       SupportsInOpen
         (((complexChartEuclideanSchwartzCLE m).symm φ :
             SchwartzMap (ComplexChartSpace m) ℂ) :
           ComplexChartSpace m -> ℂ) U0

   theorem supportsInOpen_transport_from_euclidean
       {φ : SchwartzMap (ComplexChartSpace m) ℂ}
       {U0 : Set (ComplexChartSpace m)}
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0) :
       SupportsInOpen
         ((complexChartEuclideanSchwartzCLE m φ :
             SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) :
           EuclideanSpace ℝ (Fin (m * 2)) -> ℂ)
         ((complexChartEuclideanCLE m) '' U0)

   theorem euclidean_weyl_laplacian_distribution_regular_on_open
       {ι : Type*} [Fintype ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       {V : Set (EuclideanSpace ℝ ι)}
       (hV_open : IsOpen V)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T φ = ∫ x, H x * φ x

   theorem representsDistributionOnComplexDomain_of_euclidean
       (T : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (HE : EuclideanSpace ℝ (Fin (m * 2)) -> ℂ)
       (hHE :
         RepresentsEuclideanDistributionOn
           (transportedDistributionToEuclidean T) HE
           ((complexChartEuclideanCLE m) '' U0)) :
       RepresentsDistributionOnComplexDomain T
         (fun z => HE (complexChartEuclideanCLE m z)) U0
   ```

   Lean transcript for the Euclidean transport lemmas.

   1. `complexChartEuclideanCLE_realDir` and
      `complexChartEuclideanCLE_imagDir` are pure coordinate facts.  Prove
      each by extensionality on `k : Fin (m * 2)`, then write
      `k = finProdFinEquiv (i, b)` using
      `finProdFinEquiv.surjective k`, split `b : Fin 2` with `fin_cases`,
      and simplify with
      `complexChartRealFlattenCLE_apply_re`,
      `complexChartRealFlattenCLE_apply_im`,
      `complexRealDir`, `complexImagDir`, and
      `EuclideanSpace.single_apply`.  These lemmas are not wrappers: they are
      the exact basis-identification facts needed by the Laplacian transport.

   2. Introduce the Euclidean coordinate Laplacian as an internal proof
      adapter, not as a public theorem-2 surface:

      ```lean
      def euclideanCoordinateLaplacianSchwartzCLM
          {ι : Type*} [Fintype ι] [DecidableEq ι] :
          SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
            SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
        ∑ k : ι,
          (LineDeriv.lineDerivOpCLM ℂ
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
              (EuclideanSpace.single k (1 : ℝ))).comp
            (LineDeriv.lineDerivOpCLM ℂ
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
              (EuclideanSpace.single k (1 : ℝ)))

      theorem euclideanCoordinateLaplacianSchwartzCLM_eq_laplacianCLM
          {ι : Type*} [Fintype ι] [DecidableEq ι]
          (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          euclideanCoordinateLaplacianSchwartzCLM φ =
            LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ
      ```

      The proof uses `SchwartzMap.laplacian_eq_sum` with the standard
      Euclidean coordinate orthonormal basis; if Mathlib's
      `stdOrthonormalBasis` is not definitionally the `EuclideanSpace.single`
      basis, instantiate the sum theorem with the coordinate orthonormal basis
      generated by `PiLp.basisFun`/`EuclideanSpace.single` and reindex.  Do not
      assert a fake inner-product structure on `ComplexChartSpace m`.

   3. Prove first-derivative transport from the existing Mathlib theorem:

      ```lean
      theorem complexChartEuclidean_lineDeriv_realDir
          (φ : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
          LineDeriv.lineDerivOp
              (EuclideanSpace.single (finProdFinEquiv (j, (0 : Fin 2))) 1)
              (complexChartEuclideanSchwartzCLE m φ) =
            complexChartEuclideanSchwartzCLE m
              (directionalDerivSchwartzCLM (complexRealDir j) φ)

      theorem complexChartEuclidean_lineDeriv_imagDir
          (φ : SchwartzMap (ComplexChartSpace m) ℂ) (j : Fin m) :
          LineDeriv.lineDerivOp
              (EuclideanSpace.single (finProdFinEquiv (j, (1 : Fin 2))) 1)
              (complexChartEuclideanSchwartzCLE m φ) =
            complexChartEuclideanSchwartzCLE m
              (directionalDerivSchwartzCLM (complexImagDir j) φ)
      ```

      Proof skeleton: unfold `complexChartEuclideanSchwartzCLE`, view the
      forward map as `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (complexChartEuclideanCLE m).symm`, apply
      `SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv` with
      `g := (complexChartEuclideanCLE m).symm`, and simplify the transported
      direction using the preceding `realDir`/`imagDir` lemmas.  Apply the
      same theorem a second time for second derivatives.

   4. Prove `complexChartLaplacianSchwartzCLM_transport` by rewriting the
      left-hand side with `complexChartLaplacianSchwartzCLM_apply`, pushing
      `complexChartEuclideanSchwartzCLE m` through the finite sum and addition,
      using the two second-derivative transport identities, and reindexing
      `Fin (m * 2)` by `finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)`.  The
      two `Fin 2` cases produce exactly the real and imaginary coordinate
      summands; `euclideanCoordinateLaplacianSchwartzCLM_eq_laplacianCLM`
      finishes the comparison with Mathlib's Laplacian.

   5. `supportsInOpen_transport_to_euclidean` and
      `supportsInOpen_transport_from_euclidean` are topological-support
      transport lemmas for the two directions of the same homeomorphism.  Use
      `complexChartEuclideanSchwartzCLE_symm_apply` to identify the pulled-back
      function with `φ ∘ complexChartEuclideanCLE`; show compact support from
      `hφ.1.comp_homeomorph` or the corresponding compact-image/preimage
      theorem for the homeomorphism underlying `complexChartEuclideanCLE`; and
      show
      `tsupport (((complexChartEuclideanSchwartzCLE m).symm φ) : _ -> ℂ) ⊆ U0`
      by mapping any point in the support into
      `(complexChartEuclideanCLE m) '' U0` and applying injectivity of
      `complexChartEuclideanCLE m`.  The forward lemma is the same argument
      with `complexChartEuclideanSchwartzCLE_apply`: its support is the
      `complexChartEuclideanCLE m` image of the original support, so it lies in
      `(complexChartEuclideanCLE m) '' U0`.

   6. The final chart Weyl theorem is then a short transport proof once the
      Euclidean theorem is available:

      ```lean
      have hΔE :
          ∀ φ : SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ,
            SupportsInOpen (φ : _ -> ℂ) ((complexChartEuclideanCLE m) '' U0) ->
              transportedDistributionToEuclidean T
                (LineDeriv.laplacianCLM ℝ
                  (EuclideanSpace ℝ (Fin (m * 2)))
                  (SchwartzMap (EuclideanSpace ℝ (Fin (m * 2))) ℂ) φ) = 0 := by
        intro φ hφ
        have hback := supportsInOpen_transport_to_euclidean (m := m) hφ
        simpa [transportedDistributionToEuclidean,
          complexChartLaplacianSchwartzCLM_transport] using
          hΔ ((complexChartEuclideanSchwartzCLE m).symm φ) hback

      obtain ⟨HE, hHE_smooth, hHE_rep⟩ :=
        euclidean_weyl_laplacian_distribution_regular_on_open
          (transportedDistributionToEuclidean (m := m) T)
          (hU0_open.image (complexChartEuclideanCLE m).toHomeomorph)
          hΔE
      refine ⟨fun z => HE (complexChartEuclideanCLE m z), ?smooth, ?rep⟩
      ```

      The representation proof is the checked helper
      `representsDistributionOnComplexDomain_of_euclidean`: rewrite `T φ` as
      the transported distribution applied to
      `complexChartEuclideanSchwartzCLE m φ`, use
      `supportsInOpen_transport_from_euclidean` to feed the Euclidean
      representative theorem, then apply
      `integral_comp_complexChartEuclideanCLE` to change variables.  This is
      the exact point where the volume-preserving theorem is consumed.

   The transport proof of `weyl_laplacian_distribution_regular_on_open` then
   applies the Euclidean theorem to
   `transportedDistributionToEuclidean T` on
   `(complexChartEuclideanCLE m) '' U0`.  The support transport lemma moves
   compact support back to `U0`, and
   `complexChartLaplacianSchwartzCLM_transport` converts the checked
   coordinate-Laplacian hypothesis into the Euclidean Laplacian hypothesis.
   The representative on `U0` is
   `fun z => HE (complexChartEuclideanCLE m z)`.  Its real smoothness follows
   by composing `hHE : ContDiffOn ℝ ⊤ HE _` with the continuous linear map
   `complexChartEuclideanCLE m`; the representation identity is transported
   by `SchwartzMap.compCLMOfContinuousLinearEquiv_apply` and the linear
   change-of-variables formula for the finite-dimensional equivalence.

   Checked status of the transport layer:

   ```lean
   theorem complexChartEuclideanCLE_realDir
   theorem complexChartEuclideanCLE_imagDir
   theorem complexChartEuclidean_lineDeriv_realDir
   theorem complexChartEuclidean_lineDeriv_imagDir
   theorem complexChartEuclidean_secondLineDeriv_realDir
   theorem complexChartEuclidean_secondLineDeriv_imagDir
   def euclideanCoordinateLaplacianSchwartzCLM
   theorem euclideanCoordinateLaplacianSchwartzCLM_eq_laplacianCLM
   theorem complexChartLaplacianSchwartzCLM_transport
   def transportedDistributionToEuclidean
   theorem transportedDistributionToEuclidean_apply
   theorem supportsInOpen_transport_to_euclidean
   theorem supportsInOpen_transport_from_euclidean
   theorem complexChartEuclideanCLE_volumePreserving
   theorem integral_comp_complexChartEuclideanCLE
   def RepresentsEuclideanDistributionOn
   theorem representsDistributionOnComplexDomain_of_euclidean
   def euclideanTranslateSchwartzCLM
   theorem euclideanTranslateSchwartz_apply
   theorem seminorm_euclideanTranslateSchwartz_le
   def euclideanReflectedTranslate
   theorem euclideanReflectedTranslate_apply
   theorem supportsInOpen_euclideanReflectedTranslate_of_kernelSupport
   theorem euclideanLineDerivOp_comm
   theorem euclideanLineDerivOp_iterated_comm
   theorem fderiv_iteratedFDeriv_eq_iteratedFDeriv_euclideanLineDeriv
   theorem exists_seminorm_euclideanTranslateSchwartz_sub_le_linear
   theorem euclideanDiffQuotient_iteratedFDeriv_pointwise
   theorem tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport
   theorem continuous_apply_euclideanTranslateSchwartz_of_isCompactSupport
   theorem continuous_apply_euclideanReflectedTranslate_of_isCompactSupport
   ```

   The chart/representative declarations are checked in
   `SCV/DistributionalEOWRegularity.lean`; the Euclidean moving-kernel
   declarations are checked in `SCV/EuclideanWeyl.lean`.  The remaining Lean
   work for this substage is no longer coordinate, support, Jacobian,
   reflected-kernel bookkeeping, or first-order translation seminorm growth; it
   is the genuine local Euclidean Weyl theorem.

   Exact remaining theorem surfaces for the Weyl package:

   ```lean
   theorem euclidean_laplacian_distribution_regular_on_ball
       {ι : Type*} [Fintype ι] [DecidableEq ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (c : EuclideanSpace ℝ ι) {r R : ℝ}
       (hr : 0 < r) (hrR : r < R)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ)
             (Metric.ball c R) ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball c r) ∧
         RepresentsEuclideanDistributionOn T H (Metric.ball c r)

   theorem euclidean_weyl_laplacian_distribution_regular_on_open
       {ι : Type*} [Fintype ι] [DecidableEq ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       {V : Set (EuclideanSpace ℝ ι)}
       (hV_open : IsOpen V)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
         RepresentsEuclideanDistributionOn T H V
   ```

   The volume-preserving lemma is not a new analytic input.  It is a finite
   product/permutation calculation: compose the measurable real/imaginary
   complex chart, the coordinate-flattening permutation underlying
   `realBlockFlattenCLE`, and `PiLp.volume_preserving_toLp`.  This proves that
   no Jacobian factor appears in `integral_comp_complexChartEuclideanCLE`.

   Lean-ready Euclidean Weyl proof route.  Do not introduce a theorem-2
   wrapper and do not add an axiom.  Prove the pure Euclidean theorem by the
   standard mollifier-scale-invariance proof of Weyl's lemma.

   The first Euclidean translation, reflected-kernel support, derivative
   commutation, first-order seminorm estimate, and compact-kernel continuity
   layer is now checked in `SCV/EuclideanWeyl.lean`:

   ```lean
   noncomputable def euclideanTranslateSchwartzCLM
       {ι : Type*} [Fintype ι]
       (a : EuclideanSpace ℝ ι) :
       SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
         SchwartzMap (EuclideanSpace ℝ ι) ℂ

   theorem euclideanTranslateSchwartz_apply
       (a : EuclideanSpace ℝ ι)
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x : EuclideanSpace ℝ ι) :
       euclideanTranslateSchwartzCLM a φ x = φ (x + a)

   theorem seminorm_euclideanTranslateSchwartz_le
       (k l : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       ∃ D : ℝ, 0 ≤ D ∧ ∀ a : EuclideanSpace ℝ ι,
         (SchwartzMap.seminorm ℂ k l)
           (euclideanTranslateSchwartzCLM a φ) ≤
           D * (1 + ‖a‖) ^ k

   noncomputable def euclideanReflectedTranslate
       (x : EuclideanSpace ℝ ι)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
     euclideanTranslateSchwartzCLM (-x) ρ

   theorem euclideanReflectedTranslate_apply
       (x y : EuclideanSpace ℝ ι)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       euclideanReflectedTranslate x ρ y = ρ (y - x)

   theorem supportsInOpen_euclideanReflectedTranslate_of_kernelSupport
       {V : Set (EuclideanSpace ℝ ι)}
       {x : EuclideanSpace ℝ ι} {r : ℝ}
       (hx : Metric.closedBall x r ⊆ V)
       (hρ : tsupport (ρ : EuclideanSpace ℝ ι -> ℂ) ⊆
         Metric.closedBall 0 r) :
       SupportsInOpen
         (euclideanReflectedTranslate x ρ :
           EuclideanSpace ℝ ι -> ℂ) V

   theorem euclideanLineDerivOp_comm
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (v w : EuclideanSpace ℝ ι) :
       ∂_{v} ((∂_{w} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)) =
         ∂_{w} ((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ))

   theorem fderiv_iteratedFDeriv_eq_iteratedFDeriv_euclideanLineDeriv
       {n : ℕ}
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (v x : EuclideanSpace ℝ ι) :
       fderiv ℝ (iteratedFDeriv ℝ n
           (φ : EuclideanSpace ℝ ι -> ℂ)) x v =
         iteratedFDeriv ℝ n
           (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
             EuclideanSpace ℝ ι -> ℂ)) x

   theorem exists_seminorm_euclideanTranslateSchwartz_sub_le_linear
       (g : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (v : EuclideanSpace ℝ ι) (k n : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ t : ℝ, |t| ≤ 1 ->
           SchwartzMap.seminorm ℝ k n
             (euclideanTranslateSchwartzCLM (t • v) g - g) ≤ C * |t|

   theorem euclideanDiffQuotient_iteratedFDeriv_pointwise
       {n : ℕ}
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (v : EuclideanSpace ℝ ι) {t : ℝ} (ht : t ≠ 0)
       (x : EuclideanSpace ℝ ι) :
       iteratedFDeriv ℝ n
         (↑(t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ) -
             ∂_{v} φ) : EuclideanSpace ℝ ι -> ℂ) x =
         t⁻¹ •
           (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι -> ℂ) (x + t • v) -
            iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι -> ℂ) x) -
         iteratedFDeriv ℝ n
           (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
             EuclideanSpace ℝ ι -> ℂ)) x

   theorem tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (hρ_compact : HasCompactSupport
         (ρ : EuclideanSpace ℝ ι -> ℂ))
       (a0 : EuclideanSpace ℝ ι) :
       Tendsto
         (fun a : EuclideanSpace ℝ ι =>
           euclideanTranslateSchwartzCLM a ρ)
         (𝓝 a0) (𝓝 (euclideanTranslateSchwartzCLM a0 ρ))

   theorem continuous_apply_euclideanReflectedTranslate_of_isCompactSupport
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (hρ_compact : HasCompactSupport
         (ρ : EuclideanSpace ℝ ι -> ℂ)) :
       Continuous
         (fun x : EuclideanSpace ℝ ι =>
           T (euclideanReflectedTranslate x ρ))
   ```

   The proofs are the existing `translateSchwartz` and
   `TranslationDifferentiation` proofs transported from `Fin m -> ℝ` to
   `EuclideanSpace ℝ ι`: `SchwartzMap.compCLM` for translation,
   `tsupport_comp_eq_preimage` for support, `isCompact_closedBall` for
   compactness, and the standard mean-value/seminorm estimate for
   `τ_{t v}g - g`.  This layer is already compiled and exported by `SCV.lean`.
   The reflected convention is chosen so that the eventual regularization is
   `Hρ x = T (euclideanReflectedTranslate x ρ)` and
   `∫ Hρ x * φ x dx = T (ρ̌ * φ)` with Mathlib's convolution convention.

   The checked continuity of distributional mollifications has now been
   upgraded to the one-parameter differentiability theorem needed for every
   fixed line.  The full checked split difference-quotient layer is:

   ```lean
   theorem euclideanTranslateSchwartzCLM_zero
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       euclideanTranslateSchwartzCLM (0 : EuclideanSpace ℝ ι) φ = φ

   theorem euclideanDiffQuotient_weighted_pointwise_bound
       {n : ℕ}
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (v : EuclideanSpace ℝ ι) (k : ℕ)
       {C : ℝ} (hC_nonneg : 0 ≤ C)
       (hC : ∀ t : ℝ, |t| ≤ 1 ->
         SchwartzMap.seminorm ℝ k n
           (euclideanTranslateSchwartzCLM (t • v)
             (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) -
             ∂_{v} φ) ≤ C * |t|)
       {t : ℝ} (ht_ne : t ≠ 0) (ht_abs : |t| ≤ 1)
       (x : EuclideanSpace ℝ ι) :
       ‖x‖ ^ k *
           ‖t⁻¹ •
               (iteratedFDeriv ℝ n
                 (φ : EuclideanSpace ℝ ι -> ℂ) (x + t • v) -
                iteratedFDeriv ℝ n
                 (φ : EuclideanSpace ℝ ι -> ℂ) x) -
             iteratedFDeriv ℝ n
               (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
                 EuclideanSpace ℝ ι -> ℂ)) x‖ ≤ C * |t|

   theorem exists_seminorm_diffQuotient_euclideanTranslateSchwartz_sub_lineDeriv_le
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (v : EuclideanSpace ℝ ι) (k n : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ t : ℝ, t ≠ 0 -> |t| ≤ 1 ->
           SchwartzMap.seminorm ℝ k n
             (t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ) -
               ∂_{v} φ) ≤ C * |t|

   theorem tendsto_diffQuotient_euclideanTranslateSchwartz_zero
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (v : EuclideanSpace ℝ ι) :
       Tendsto
         (fun t : ℝ =>
           t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ))
         (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 (∂_{v} φ))
   ```

   The checked distributional derivative consumer is:

   ```lean
   theorem hasDerivAt_regularizedDistribution_along
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x v : EuclideanSpace ℝ ι) :
       HasDerivAt
         (fun t : ℝ =>
           T (euclideanReflectedTranslate (x + t • v) ρ))
         (-T (euclideanReflectedTranslate x
           (LineDeriv.lineDerivOp v ρ)))
         0
   ```

   The next implementation gate is **not** another line-derivative wrapper.
   A `ContDiff` theorem needs a Fréchet derivative in the center variable, so
   the missing analytic content is the direction-uniform translation remainder
   in Schwartz topology.  The package should be proved in this order:
   because `SCV/EuclideanWeyl.lean` is now a checked 1000-line support file,
   the next gate should live in a small companion file
   `SCV/EuclideanWeylFrechet.lean` importing `SCV/EuclideanWeyl.lean`, not by
   continuing to enlarge the stable file.

   ```lean
   noncomputable def euclideanLineDerivDirectionCLM
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       EuclideanSpace ℝ ι ->L[ℝ]
         SchwartzMap (EuclideanSpace ℝ ι) ℂ

   theorem euclideanLineDerivDirectionCLM_apply
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (v : EuclideanSpace ℝ ι) :
       euclideanLineDerivDirectionCLM ρ v = ∂_{v} ρ

   theorem exists_seminorm_diffQuotient_euclideanTranslateSchwartz_sub_lineDeriv_le_uniform_unit
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (k n : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 ->
         ∀ t : ℝ, t ≠ 0 -> |t| ≤ 1 ->
           SchwartzMap.seminorm ℝ k n
             (t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ) -
               ∂_{v} φ) ≤ C * |t|

   theorem exists_seminorm_euclideanTranslateSchwartz_sub_lineDeriv_le_quadratic_norm
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (k n : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ h : EuclideanSpace ℝ ι, ‖h‖ ≤ 1 ->
           SchwartzMap.seminorm ℝ k n
             (euclideanTranslateSchwartzCLM h φ - φ -
               euclideanLineDerivDirectionCLM φ h) ≤ C * ‖h‖ ^ 2

   theorem tendsto_frechetRemainder_euclideanTranslateSchwartz_zero
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       Tendsto
         (fun h : EuclideanSpace ℝ ι =>
           ‖h‖⁻¹ •
             (euclideanTranslateSchwartzCLM h φ - φ -
               euclideanLineDerivDirectionCLM φ h))
         (nhdsWithin (0 : EuclideanSpace ℝ ι) ({0}ᶜ))
         (𝓝 0)

   noncomputable def regularizedDistributionFDeriv
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x : EuclideanSpace ℝ ι) :
       EuclideanSpace ℝ ι ->L[ℝ] ℂ :=
     -(((T.restrictScalars ℝ).comp
          ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)).comp
          (euclideanLineDerivDirectionCLM ρ))

   theorem regularizedDistributionFDeriv_apply
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x v : EuclideanSpace ℝ ι) :
       regularizedDistributionFDeriv T ρ x v =
         -T (euclideanReflectedTranslate x (∂_{v} ρ))

   theorem hasDerivAt_regularizedDistribution_along_fderiv_apply
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x v : EuclideanSpace ℝ ι) :
       HasDerivAt
         (fun t : ℝ =>
           T (euclideanReflectedTranslate (x + t • v) ρ))
         (regularizedDistributionFDeriv T ρ x v)
         0

   theorem exists_seminorm_secondLineDeriv_unit_bound
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (k n : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 ->
           SchwartzMap.seminorm ℝ k n
             (∂_{v} (∂_{v} φ :
               SchwartzMap (EuclideanSpace ℝ ι) ℂ)) ≤ C

   theorem exists_seminorm_translate_lineDeriv_sub_le_linear_uniform_unit
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (k n : ℕ) :
       ∃ C : ℝ, 0 ≤ C ∧
         ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 ->
         ∀ t : ℝ, |t| ≤ 1 ->
           SchwartzMap.seminorm ℝ k n
             (euclideanTranslateSchwartzCLM (t • v)
               (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) -
               ∂_{v} φ) ≤ C * |t|

   theorem hasFDerivAt_regularizedDistribution
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (x : EuclideanSpace ℝ ι) :
       HasFDerivAt
         (fun x => T (euclideanReflectedTranslate x ρ))
         (regularizedDistributionFDeriv T ρ x) x

   theorem contDiff_regularizedDistribution
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       ContDiff ℝ (⊤ : ℕ∞)
         (fun x => T (euclideanReflectedTranslate x ρ))
   ```

   Production status: the derivative-candidate packaging declarations
   `euclideanLineDerivDirectionCLM`,
   `euclideanLineDerivDirectionCLM_apply`,
   `euclideanSecondLineDerivDirectionCLM`,
   `euclideanSecondLineDerivDirectionCLM_apply`,
   `exists_seminorm_secondLineDeriv_unit_bound`,
   `exists_seminorm_translate_secondLineDeriv_unit_bound`,
   `exists_seminorm_translate_lineDeriv_sub_le_linear_uniform_unit`,
   `exists_seminorm_diffQuotient_euclideanTranslateSchwartz_sub_lineDeriv_le_uniform_unit`,
   `exists_seminorm_euclideanTranslateSchwartz_sub_lineDeriv_le_quadratic_norm`,
   `tendsto_frechetRemainder_euclideanTranslateSchwartz_zero`,
   `regularizedDistributionFDeriv`,
   `regularizedDistributionFDeriv_apply`, and
   `hasDerivAt_regularizedDistribution_along_fderiv_apply`, and
   `hasFDerivAt_regularizedDistribution`, and
   `contDiff_regularizedDistribution` are checked in
   `SCV/EuclideanWeylFrechet.lean`.  The remaining theorem-2 SCV
   implementation content now returns to the localized Euclidean Weyl
   mollifier layer below.

   Proof transcript for the Fréchet gate:

   1. `euclideanLineDerivDirectionCLM` is the linear map
      `v ↦ ∂_v ρ`.  Linearity is exactly
      `lineDerivOp_left_add` and `lineDerivOp_left_smul`; continuity follows
      from `LinearMap.continuous_of_finiteDimensional`, since the direction
      space `EuclideanSpace ℝ ι` is finite-dimensional.
   2. The uniform-unit quotient theorem is the real missing estimate.  Do not
      obtain it by taking the already checked
      `exists_seminorm_diffQuotient...` for each `v`, because that gives a
      constant depending on `v`.  First prove
      `exists_seminorm_secondLineDeriv_unit_bound` by the following exact Lean
      ladder in `SCV/EuclideanWeylFrechet.lean`.

      The second derivative should be packaged as the continuous bilinear map
      already supplied abstractly by Mathlib's line-derivative notation:

      ```lean
      noncomputable def euclideanSecondLineDerivDirectionCLM
          (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          EuclideanSpace ℝ ι ->L[ℝ]
            EuclideanSpace ℝ ι ->L[ℝ]
              SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
        (LineDeriv.bilinearLineDerivTwo ℝ φ).toContinuousBilinearMap

      @[simp]
      theorem euclideanSecondLineDerivDirectionCLM_apply
          (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
          (v w : EuclideanSpace ℝ ι) :
          euclideanSecondLineDerivDirectionCLM φ v w =
            (∂_{v} (∂_{w} φ :
              SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
              SchwartzMap (EuclideanSpace ℝ ι) ℂ)
      ```

      Use `EuclideanSpace.basisFun ι ℝ` and
      `(EuclideanSpace.basisFun ι ℝ).sum_repr v` to expand

      ```lean
      v = ∑ i : ι, v i • EuclideanSpace.basisFun ι ℝ i.
      ```

      With `B := LineDeriv.bilinearLineDerivTwo ℝ φ`, linearity gives the
      diagonal expansion

      ```lean
      B v v =
        ∑ i : ι, ∑ j : ι,
          (v i * v j) • B (EuclideanSpace.basisFun ι ℝ i)
            (EuclideanSpace.basisFun ι ℝ j).
      ```

      The implementation proof uses only `map_sum`, `map_smul`,
      `Finset.smul_sum`, and `smul_smul`; no new analytic theorem is hidden in
      this expansion.  Add a private local helper if needed:

      ```lean
      private theorem seminorm_finset_sum_le
          (p : Seminorm ℝ V) (s : Finset α) (g : α -> V) :
          p (∑ i ∈ s, g i) ≤ ∑ i ∈ s, p (g i)
      ```

      Then apply it twice, rewrite scalar factors with
      `map_smul_eq_mul`, and prove the coordinate estimate
      `‖v i‖ ≤ ‖v‖` from `EuclideanSpace.norm_sq_eq`:

      ```lean
      have hsq_i : ‖v i‖ ^ 2 ≤ ∑ j : ι, ‖v j‖ ^ 2 :=
        Finset.single_le_sum
          (fun j _ => sq_nonneg (‖v j‖)) (Finset.mem_univ i)
      have hsq : ‖v i‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        simpa [EuclideanSpace.norm_sq_eq] using hsq_i
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
      ```

      Together with `‖v‖ ≤ 1`, this gives `|v i| ≤ 1` and hence
      `|v i * v j| ≤ 1`.  The uniform constant is exactly

      ```lean
      C =
        ∑ i : ι, ∑ j : ι,
          SchwartzMap.seminorm ℝ k n
            (∂_{EuclideanSpace.basisFun ι ℝ i}
              (∂_{EuclideanSpace.basisFun ι ℝ j} φ :
                SchwartzMap (EuclideanSpace ℝ ι) ℂ))
      ```

      This is nonnegative termwise.  The resulting theorem is the real
      direction-uniform analytic input:

      ```lean
      theorem exists_seminorm_secondLineDeriv_unit_bound
          (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
          (k n : ℕ) :
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 ->
              SchwartzMap.seminorm ℝ k n
                (∂_{v} (∂_{v} φ :
                  SchwartzMap (EuclideanSpace ℝ ι) ℂ)) ≤ C
      ```
   3. Prove
      `exists_seminorm_translate_lineDeriv_sub_le_linear_uniform_unit` by the
      existing mean-value translation proof, but first insert the genuinely
      needed translated-second-derivative estimate:

      ```lean
      theorem exists_seminorm_translate_secondLineDeriv_unit_bound
          (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
          (k n : ℕ) :
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 ->
            ∀ a : EuclideanSpace ℝ ι, ‖a‖ ≤ 1 ->
              SchwartzMap.seminorm ℝ k n
                (euclideanTranslateSchwartzCLM a
                  (∂_{v} (∂_{v} φ :
                    SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
                    SchwartzMap (EuclideanSpace ℝ ι) ℂ)) ≤ C
      ```

      Proof: apply `exists_seminorm_secondLineDeriv_unit_bound φ k n` and
      `exists_seminorm_secondLineDeriv_unit_bound φ 0 n` to get uniform
      constants `Ck` and `C0` for
      `h_v := ∂_v ∂_v φ`.  For `‖a‖ ≤ 1`,

      ```lean
      ‖x‖ ≤ ‖x + a‖ + ‖a‖
      (‖x + a‖ + ‖a‖)^k
        ≤ 2^(k-1) * (‖x + a‖^k + ‖a‖^k)
        ≤ 2^(k-1) * (‖x + a‖^k + 1)
      ```

      and `SchwartzMap.le_seminorm ℝ k n h_v (x+a)` plus
      `SchwartzMap.le_seminorm ℝ 0 n h_v (x+a)` bound the two summands.
      Thus `C = 2^(k-1) * (Ck + C0)` controls the translated second derivative
      uniformly on the unit translation ball.  With this helper in hand, for
      each `v` with `‖v‖ ≤ 1`, the derivative along the path
      `s ↦ euclideanTranslateSchwartzCLM (s • (t • v)) (∂_v φ)` is
      `∂_{t • v} (∂_v φ) = t • ∂_v ∂_v φ`, so the uniform second-derivative
      translated bound at `a = s • (t • v)` gives `C * |t|`.
   4. Prove
      `exists_seminorm_diffQuotient_euclideanTranslateSchwartz_sub_lineDeriv_le_uniform_unit`
      by feeding the uniform translate-line-derivative estimate into the now
      public `euclideanDiffQuotient_weighted_pointwise_bound`, then closing the
      Schwartz seminorm with `SchwartzMap.seminorm_le_bound`.
   5. For `h ≠ 0`, set `t = ‖h‖` and `v = ‖h‖⁻¹ • h`.  Then `‖v‖ = 1`,
      `h = t • v`, and `∂_h φ = t • ∂_v φ`.  Multiplying the uniform quotient
      estimate by `‖h‖` gives the quadratic-norm remainder theorem.  The case
      `h = 0` is immediate by simp.
   6. The quadratic remainder theorem gives
      `seminorm (‖h‖⁻¹ • remainder h) ≤ C * ‖h‖` on `0 < ‖h‖ ≤ 1`, hence
      `tendsto_frechetRemainder_euclideanTranslateSchwartz_zero` by the same
      seminorm-neighborhood argument used for
      `tendsto_diffQuotient_euclideanTranslateSchwartz_zero`.  The Lean proof
      should be written at the seminorm level:

      ```lean
      rw [(schwartz_withSeminorms ℝ
        (EuclideanSpace ℝ ι) ℂ).tendsto_nhds _ _]
      intro p ε hε
      obtain ⟨C, hC_nonneg, hC⟩ :=
        exists_seminorm_euclideanTranslateSchwartz_sub_lineDeriv_le_quadratic_norm
          φ p.1 p.2
      let δ : ℝ := min 1 (ε / (C + 1))
      have hδ_pos : 0 < δ := by
        have hC1 : 0 < C + 1 := by linarith
        have hquot : 0 < ε / (C + 1) := by positivity
        exact lt_min zero_lt_one hquot
      have hball :
          Metric.ball (0 : EuclideanSpace ℝ ι) δ ∩
              ({0}ᶜ : Set (EuclideanSpace ℝ ι)) ∈
            nhdsWithin (0 : EuclideanSpace ℝ ι)
              ({0}ᶜ : Set (EuclideanSpace ℝ ι)) := by
        simpa [Set.inter_comm] using
          inter_mem_nhdsWithin ({0}ᶜ : Set (EuclideanSpace ℝ ι))
            (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ ι) hδ_pos)
      refine Filter.mem_of_superset hball ?_
      intro h hh
      rcases hh with ⟨hh_ball, hh_punctured⟩
      have hh_norm_lt : ‖h‖ < δ := by
        simpa [dist_eq_norm] using hh_ball
      have hh_unit : ‖h‖ ≤ 1 :=
        le_trans (le_of_lt hh_norm_lt) (min_le_left _ _)
      have hh_ne : h ≠ 0 := by
        simpa using hh_punctured
      have hnorm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh_ne
      have hbound_quad := hC h hh_unit
      have hbound_linear :
          SchwartzMap.seminorm ℝ p.1 p.2
            (‖h‖⁻¹ •
              (euclideanTranslateSchwartzCLM h φ - φ -
                euclideanLineDerivDirectionCLM φ h)) ≤
            C * ‖h‖ := by
        calc
          SchwartzMap.seminorm ℝ p.1 p.2
              (‖h‖⁻¹ •
                (euclideanTranslateSchwartzCLM h φ - φ -
                  euclideanLineDerivDirectionCLM φ h))
              = |‖h‖⁻¹| *
                  SchwartzMap.seminorm ℝ p.1 p.2
                    (euclideanTranslateSchwartzCLM h φ - φ -
                      euclideanLineDerivDirectionCLM φ h) := by
                    rw [map_smul_eq_mul, Real.norm_eq_abs]
          _ = ‖h‖⁻¹ *
                  SchwartzMap.seminorm ℝ p.1 p.2
                    (euclideanTranslateSchwartzCLM h φ - φ -
                      euclideanLineDerivDirectionCLM φ h) := by
                    rw [abs_of_nonneg
                      (inv_nonneg.mpr (norm_nonneg h))]
          _ ≤ ‖h‖⁻¹ * (C * ‖h‖ ^ 2) := by
                    exact mul_le_mul_of_nonneg_left hbound_quad
                      (inv_nonneg.mpr (norm_nonneg h))
          _ = C * ‖h‖ := by
                    field_simp [hnorm_pos.ne']
      have hδ_eps : C * ‖h‖ < ε := by
        have hC1 : 0 < C + 1 := by linarith
        have hC_le : C ≤ C + 1 := by linarith
        have hh_eps : ‖h‖ < ε / (C + 1) :=
          lt_of_lt_of_le hh_norm_lt (min_le_right _ _)
        calc
          C * ‖h‖ ≤ (C + 1) * ‖h‖ := by gcongr
          _ < (C + 1) * (ε / (C + 1)) := by gcongr
          _ = ε := by field_simp [ne_of_gt hC1]
      simpa using lt_of_le_of_lt hbound_linear hδ_eps
      ```
   7. For the reflected translate at center `x`, rewrite
      `euclideanReflectedTranslate (x + h) ρ =
       euclideanTranslateSchwartzCLM (-x)
         (euclideanTranslateSchwartzCLM (-h) ρ)`.  Compose the Fréchet
      remainder limit for `-h` with
      `(T.restrictScalars ℝ).comp
       ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)`.
      The sign in `regularizedDistributionFDeriv_apply` comes from
      `∂_{-h} ρ = -∂_h ρ`.

      The checked implementation keeps the proof under Lean's heartbeat budget
      by splitting the scalar algebra from the topology.  The algebra helpers
      are private, but mathematically they assert only the identity
      "normalized scalar remainder = continuous functional applied to the
      normalized Schwartz remainder":

      ```lean
      private theorem regularizedDistribution_remainder_eq
          (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
          (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
          (x h : EuclideanSpace ℝ ι) :
          let L : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℝ] ℂ :=
            (T.restrictScalars ℝ).comp
              ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)
          let R : EuclideanSpace ℝ ι -> SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
            fun h => ‖-h‖⁻¹ •
              (euclideanTranslateSchwartzCLM (-h) ρ - ρ -
                euclideanLineDerivDirectionCLM ρ (-h))
          L (R h) = ‖h‖⁻¹ •
            (T (euclideanReflectedTranslate (x + h) ρ) -
              T (euclideanReflectedTranslate x ρ) -
              regularizedDistributionFDeriv T ρ x h)

      private theorem regularizedDistribution_remainder_norm_eq
          ... :
          ‖L (R h)‖ =
            ‖h‖⁻¹ *
              ‖T (euclideanReflectedTranslate (x + h) ρ) -
                T (euclideanReflectedTranslate x ρ) -
                regularizedDistributionFDeriv T ρ x h‖
      ```

      The topology helper is then:

      ```lean
      private theorem regularizedDistribution_remainder_norm_tendsto_zero
          (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
          (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
          (x : EuclideanSpace ℝ ι) :
          let L : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℝ] ℂ :=
            (T.restrictScalars ℝ).comp
              ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)
          let R : EuclideanSpace ℝ ι -> SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
            fun h => ‖-h‖⁻¹ •
              (euclideanTranslateSchwartzCLM (-h) ρ - ρ -
                euclideanLineDerivDirectionCLM ρ (-h))
          let G : EuclideanSpace ℝ ι -> ℝ := fun h => ‖L (R h)‖
          Tendsto G (𝓝 (0 : EuclideanSpace ℝ ι)) (𝓝 0)
      ```

      Proof transcript:

      ```lean
      let L : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℝ] ℂ :=
        (T.restrictScalars ℝ).comp
          ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)
      let R : EuclideanSpace ℝ ι -> SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
        fun h => ‖-h‖⁻¹ •
          (euclideanTranslateSchwartzCLM (-h) ρ - ρ -
            euclideanLineDerivDirectionCLM ρ (-h))
      let G : EuclideanSpace ℝ ι -> ℝ := fun h => ‖L (R h)‖
      have hneg_nhds : Tendsto (fun h : EuclideanSpace ℝ ι => -h)
          (𝓝[≠] (0 : EuclideanSpace ℝ ι))
          (𝓝 (0 : EuclideanSpace ℝ ι)) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using
          (continuous_neg.tendsto (0 : EuclideanSpace ℝ ι)))
      have hneg_mem : ∀ᶠ h : EuclideanSpace ℝ ι in
          𝓝[≠] (0 : EuclideanSpace ℝ ι),
          -h ∈ ({0}ᶜ : Set (EuclideanSpace ℝ ι)) := by
        filter_upwards [eventually_mem_nhdsWithin] with h hh
        simpa using (neg_ne_zero.mpr hh)
      have hneg : Tendsto (fun h : EuclideanSpace ℝ ι => -h)
          (𝓝[≠] (0 : EuclideanSpace ℝ ι))
          (𝓝[≠] (0 : EuclideanSpace ℝ ι)) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          (fun h : EuclideanSpace ℝ ι => -h) hneg_nhds hneg_mem
      have hbase :=
        (tendsto_frechetRemainder_euclideanTranslateSchwartz_zero ρ).comp hneg
      have hL_punct : Tendsto (fun h : EuclideanSpace ℝ ι => L (R h))
          (𝓝[≠] (0 : EuclideanSpace ℝ ι)) (𝓝 0) := by
        have hraw := L.continuous.continuousAt.tendsto.comp hbase
        simpa [R, Function.comp_def, norm_neg] using hraw
      have hnorm_punct : Tendsto G
          (𝓝[≠] (0 : EuclideanSpace ℝ ι)) (𝓝 0) := by
        simpa using hL_punct.norm
      have hG0 : G 0 = 0 := by
        simp [G, R, L]
      have hnorm_pure : Tendsto G
          (pure (0 : EuclideanSpace ℝ ι)) (𝓝 0) := by
        simpa [hG0] using (tendsto_pure_nhds G
          (0 : EuclideanSpace ℝ ι))
      rw [← nhdsNE_sup_pure (0 : EuclideanSpace ℝ ι)]
      exact hnorm_punct.sup hnorm_pure
      ```

      Finally shift from increments to points:

      ```lean
      have hshift : Tendsto (fun y : EuclideanSpace ℝ ι => y - x)
          (𝓝 x) (𝓝 (0 : EuclideanSpace ℝ ι)) := by
        simpa using (tendsto_id.sub tendsto_const_nhds :
          Tendsto (fun y : EuclideanSpace ℝ ι => y - x) (𝓝 x)
            (𝓝 (x - x)))
      have htarget :=
        (regularizedDistribution_remainder_norm_tendsto_zero T ρ x).comp hshift
      refine htarget.congr' ?_
      exact Filter.Eventually.of_forall
        (fun y : EuclideanSpace ℝ ι =>
          regularizedDistribution_remainder_norm_eq_sub T ρ x y)
      ```

      The public theorem is therefore:

      ```lean
      rw [hasFDerivAt_iff_tendsto]
      exact regularizedDistribution_remainder_norm_tendsto_at T ρ x
      ```
   8. For `contDiff_regularizedDistribution`, iterate the Fréchet derivative
      identity.  The recursive formula is:
      the derivative of `x ↦ T (euclideanReflectedTranslate x (∂^u ρ))` in
      direction `v` is
      `x ↦ -T (euclideanReflectedTranslate x (∂_v (∂^u ρ)))`.
      Use `euclideanLineDerivOp_iterated_comm` to keep the derivative order in
      the canonical `∂^{u.cons v}` form, and apply `contDiff_infty_iff_fderiv`
      (or its finite-dimensional `fderiv_apply` form) inductively.

      The checked Lean route should avoid direct manipulation of
      `iteratedFDeriv`.  First prove every finite order by induction on
      `r : ℕ`:

      ```lean
      private theorem contDiff_regularizedDistribution_nat
          (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
          (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          ∀ r : ℕ, ContDiff ℝ (r : ℕ∞)
            (fun x : EuclideanSpace ℝ ι =>
              T (euclideanReflectedTranslate x ρ))
        | 0 => by
            have hd : Differentiable ℝ
                (fun x : EuclideanSpace ℝ ι =>
                  T (euclideanReflectedTranslate x ρ)) := fun x =>
              (hasFDerivAt_regularizedDistribution T ρ x).differentiableAt
            exact (contDiff_zero (𝕜 := ℝ)
              (f := fun x : EuclideanSpace ℝ ι =>
                T (euclideanReflectedTranslate x ρ))).2 hd.continuous
        | r + 1 => by
            refine (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ)
              (E := EuclideanSpace ℝ ι) (F := ℂ)
              (f := fun x : EuclideanSpace ℝ ι =>
                T (euclideanReflectedTranslate x ρ)) (n := r)).2 ?_
            refine ⟨regularizedDistributionFDeriv T ρ, ?_, ?_⟩
            · rw [contDiff_clm_apply_iff]
              intro v
              have hbase := contDiff_regularizedDistribution_nat T
                (∂_{v} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) r
              simpa [regularizedDistributionFDeriv_apply] using hbase.neg
            · intro x
              exact hasFDerivAt_regularizedDistribution T ρ x
      ```

      The key mathematical point is that the derivative field evaluated at
      `v` is exactly the negative of the same regularized distribution with
      test function `∂_v ρ`; hence the induction decreases only the
      differentiability order, not any analytic regularity of `ρ`.  The
      infinite-order theorem is then immediate:

      ```lean
      theorem contDiff_regularizedDistribution
          (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
          (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun x : EuclideanSpace ℝ ι =>
              T (euclideanReflectedTranslate x ρ)) := by
        rw [contDiff_iff_forall_nat_le]
        intro m hm
        exact contDiff_regularizedDistribution_nat T ρ m
      ```

   The scale-invariance heart of Weyl's lemma is a pure radial-bump theorem.
   The first Lean slice is only the normalized compact Euclidean bump package.
   This is genuine substrate, but it is **not** the Poisson/right-inverse
   theorem.  The radial Poisson theorem below remains the hard
   scale-invariance input.  Keep the bump file separate from the already large
   Euclidean translation files:

   ```lean
   import OSReconstruction.SCV.EuclideanWeylFrechet
   import Mathlib.Analysis.Calculus.BumpFunction.Normed
   import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
   import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
   import Mathlib.MeasureTheory.Integral.IntegralEqImproper
   ```

   Do not define the Weyl bump through the generic `ContDiffBump.normed` API.
   That API gives smoothness, support, and normalization, but it hides the
   selected `ContDiffBumpBase` behind `someContDiffBumpBase`, so Lean cannot
   later recover the radial profile needed by the Poisson ODE.  Instead,
   define the bump directly from the explicit inner-product base
   `ContDiffBumpBase.ofInnerProductSpace`; this keeps radiality available as a
   theorem while still reusing Mathlib's smooth-transition construction.

   ```lean
   noncomputable def euclideanWeylRawBumpReal
       {ι : Type*} [Fintype ι]
       (ε : ℝ) : EuclideanSpace ℝ ι -> ℝ

   theorem euclideanWeylRawBumpReal_contDiff
       (ε : ℝ) :
       ContDiff ℝ (⊤ : ℕ∞)
         (euclideanWeylRawBumpReal (ι := ι) ε)

   theorem euclideanWeylRawBumpReal_nonneg
       (ε : ℝ) (x : EuclideanSpace ℝ ι) :
       0 ≤ euclideanWeylRawBumpReal ε x

   theorem euclideanWeylRawBumpReal_apply
       {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
       euclideanWeylRawBumpReal ε x =
         Real.smoothTransition (2 - 2 * (‖x‖ / ε))

   theorem euclideanWeylRawBumpReal_support
       {ε : ℝ} (hε : 0 < ε) :
       Function.support (euclideanWeylRawBumpReal (ι := ι) ε) =
         Metric.ball (0 : EuclideanSpace ℝ ι) ε

   theorem euclideanWeylRawBumpReal_hasCompactSupport
       {ε : ℝ} (hε : 0 < ε) :
       HasCompactSupport (euclideanWeylRawBumpReal (ι := ι) ε)

   theorem euclideanWeylRawBumpReal_integrable
       {ε : ℝ} (hε : 0 < ε) :
       Integrable (euclideanWeylRawBumpReal (ι := ι) ε)

   theorem euclideanWeylRawBumpReal_integral_pos
       {ε : ℝ} (hε : 0 < ε) :
       0 < ∫ x : EuclideanSpace ℝ ι, euclideanWeylRawBumpReal ε x

   noncomputable def euclideanWeylRawIntegralReal
       {ι : Type*} [Fintype ι] (ε : ℝ) : ℝ

   theorem euclideanWeylRawIntegralReal_pos
       {ε : ℝ} (hε : 0 < ε) :
       0 < euclideanWeylRawIntegralReal (ι := ι) ε

   theorem euclideanWeylRawIntegralReal_scale
       {ε : ℝ} (hε : 0 < ε) :
       euclideanWeylRawIntegralReal (ι := ι) ε =
         ε ^ Fintype.card ι *
           euclideanWeylRawIntegralReal (ι := ι) 1

   noncomputable def euclideanWeylBaseProfile (r : ℝ) : ℂ :=
     (Real.smoothTransition (2 - 2 * |r|) : ℂ)

   theorem euclideanWeylBaseProfile_eq_zero_of_one_le_abs
       {r : ℝ} (hr : 1 ≤ |r|) :
       euclideanWeylBaseProfile r = 0

   theorem euclideanWeylBaseProfile_eq_one_of_abs_le_half
       {r : ℝ} (hr : |r| ≤ 1 / 2) :
       euclideanWeylBaseProfile r = 1

   noncomputable def euclideanWeylWeightedRawMass
       (N : ℕ) (ε : ℝ) : ℂ

   theorem euclideanWeylWeightedRawMass_scale
       {N : ℕ} (hNpos : 0 < N) {ε : ℝ} (hε : 0 < ε) :
       euclideanWeylWeightedRawMass N ε =
         (((ε ^ N : ℝ) : ℂ)) * euclideanWeylWeightedRawMass N 1

   noncomputable def euclideanWeylNormalizedProfile
       {ι : Type*} [Fintype ι] (ε : ℝ) : ℝ -> ℂ

   theorem euclideanWeylNormalizedProfile_eq_zero_of_epsilon_le_abs
       {ε : ℝ} (hε : 0 < ε) {r : ℝ}
       (hr : ε ≤ |r|) :
       euclideanWeylNormalizedProfile (ι := ι) ε r = 0

   theorem euclideanWeylNormalizedProfile_support_subset
       {ε : ℝ} (hε : 0 < ε) :
       Function.support (euclideanWeylNormalizedProfile (ι := ι) ε) ⊆
         Set.Icc (-ε) ε

   theorem euclideanWeylNormalizedProfile_eq_plateau_of_abs_le_half_epsilon
       {ε : ℝ} (hε : 0 < ε) {r : ℝ}
       (hr : |r| ≤ ε / 2) :
       euclideanWeylNormalizedProfile (ι := ι) ε r =
         (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹)

   theorem euclideanWeylNormalizedProfile_contDiff
       {ε : ℝ} (hε : 0 < ε) :
       ContDiff ℝ (⊤ : ℕ∞) (euclideanWeylNormalizedProfile (ι := ι) ε)

   theorem euclideanWeylWeightedNormalizedProfile_integrable
       (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
       Integrable (fun r : ℝ =>
         ((r ^ (N - 1) : ℝ) : ℂ) *
           euclideanWeylNormalizedProfile (ι := ι) ε r)

   theorem euclideanWeylBump_weightedMass_eq_const
       {ι : Type*} [Fintype ι] [Nonempty ι]
       {ε : ℝ} (hε : 0 < ε) :
       ∫ r in Set.Ioi 0,
         ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
           euclideanWeylNormalizedProfile (ι := ι) ε r =
       (((euclideanWeylRawIntegralReal (ι := ι) 1 : ℝ) : ℂ)⁻¹) *
         euclideanWeylWeightedRawMass (Fintype.card ι) 1

   noncomputable def euclideanWeylBumpSubProfile
       {ι : Type*} [Fintype ι]
       (ε δ : ℝ) : ℝ -> ℂ

   theorem euclideanWeylBumpSubProfile_eq_zero_of_max_le_abs
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {r : ℝ}
       (hr : max ε δ ≤ |r|) :
       euclideanWeylBumpSubProfile (ι := ι) ε δ r = 0

   theorem euclideanWeylBumpSubProfile_support_subset
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       Function.support (euclideanWeylBumpSubProfile (ι := ι) ε δ) ⊆
         Set.Icc (-(max ε δ)) (max ε δ)

   theorem euclideanWeylBumpSubProfile_eq_plateau_of_abs_le_half_min
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {r : ℝ}
       (hr : |r| ≤ min ε δ / 2) :
       euclideanWeylBumpSubProfile (ι := ι) ε δ r =
         (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) -
           (((euclideanWeylRawIntegralReal (ι := ι) δ : ℝ) : ℂ)⁻¹)

   theorem euclideanWeylBumpSubProfile_exists_plateau
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       ∃ η : ℝ, ∃ c : ℂ, 0 < η ∧
         ∀ r ∈ Set.Icc 0 η,
           euclideanWeylBumpSubProfile (ι := ι) ε δ r = c

   theorem euclideanWeylBumpSubProfile_weightedMass_eq_zero
       {ι : Type*} [Fintype ι] [Nonempty ι]
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       ∫ r in Set.Ioi 0,
         ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
           euclideanWeylBumpSubProfile (ι := ι) ε δ r = 0

   noncomputable def euclideanWeylBump
       {ι : Type*} [Fintype ι]
       (ε : ℝ) (hε : 0 < ε) :
       SchwartzMap (EuclideanSpace ℝ ι) ℂ

   @[simp]
   theorem euclideanWeylBump_apply
       (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
       euclideanWeylBump ε hε x =
         ((euclideanWeylRawBumpReal ε x /
           (∫ y : EuclideanSpace ℝ ι,
             euclideanWeylRawBumpReal ε y) : ℝ) : ℂ)

   theorem euclideanWeylBump_raw_profile
       {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
       euclideanWeylBump ε hε x =
         euclideanWeylNormalizedProfile (ι := ι) ε ‖x‖

   theorem euclideanWeylBump_eq_of_norm_eq
       {ε : ℝ} (hε : 0 < ε)
       {x y : EuclideanSpace ℝ ι} (hxy : ‖x‖ = ‖y‖) :
       euclideanWeylBump ε hε x = euclideanWeylBump ε hε y

   theorem euclideanWeylBump_sub_eq_of_norm_eq
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
       {x y : EuclideanSpace ℝ ι} (hxy : ‖x‖ = ‖y‖) :
       ((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
         SchwartzMap (EuclideanSpace ℝ ι) ℂ) x) =
       ((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
         SchwartzMap (EuclideanSpace ℝ ι) ℂ) y)

   theorem euclideanWeylBumpSubProfile_norm_eq_bump_sub
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
       (x : EuclideanSpace ℝ ι) :
       euclideanWeylBumpSubProfile (ι := ι) ε δ ‖x‖ =
         (euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
           SchwartzMap (EuclideanSpace ℝ ι) ℂ) x

   theorem euclideanWeylBump_nonneg_re
       (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
       0 ≤ (euclideanWeylBump ε hε x).re

   theorem euclideanWeylBump_im_eq_zero
       (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
       (euclideanWeylBump ε hε x).im = 0

   theorem euclideanWeylBump_normalized
       (ε : ℝ) (hε : 0 < ε) :
       ∫ x : EuclideanSpace ℝ ι, euclideanWeylBump ε hε x = 1

   theorem euclideanWeylBump_support
       (ε : ℝ) (hε : 0 < ε) :
       tsupport (euclideanWeylBump ε hε :
         EuclideanSpace ℝ ι -> ℂ) ⊆ Metric.closedBall 0 ε

   theorem euclideanWeylBump_sub_integral_eq_zero
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       ∫ x : EuclideanSpace ℝ ι,
         (euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
           SchwartzMap (EuclideanSpace ℝ ι) ℂ) x = 0

   theorem euclideanWeylBump_sub_support
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       tsupport ((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
         SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
         EuclideanSpace ℝ ι -> ℂ) ⊆ Metric.closedBall 0 (max ε δ)

   theorem euclideanWeylBump_sub_hasCompactSupport
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       HasCompactSupport
         (((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
           SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
           EuclideanSpace ℝ ι -> ℂ))
   ```

   The checked implementation proves these declarations directly in
   `SCV/EuclideanWeylBump.lean`.  The raw smoothness proof composes
   `ContDiffBumpBase.ofInnerProductSpace.smooth` with
   `x ↦ (2, (2 / ε) • x)`, whose first component stays in `Set.Ioi 1`.
   The support proof rewrites the raw support as the preimage of
   `Metric.ball 0 2` under scalar multiplication by `2 / ε`, hence exactly
   `Metric.ball 0 ε`.  Positivity of the raw integral follows from
   `integral_pos_iff_support_of_nonneg`, nonnegativity of the base profile, and
   positive volume of the ball.  Normalization is then just
   `integral_complex_ofReal` plus `MeasureTheory.integral_div`.

   The next theorem is the hard scalar-analysis sublemma inside the Weyl
   proof.  It must not be stated as a generic compact-support right inverse for
   the Laplacian: for non-radial compact tests the image of
   `Δ : C_c^\infty -> C_c^\infty` annihilates every harmonic polynomial, not
   only constants.  The theorem needed here is narrower and true because the
   right-hand side is the difference of two centered radial normalized bumps.
   The radiality kills all nonconstant harmonic-polynomial moments by angular
   averaging, and the zero integral kills the constant moment.  Therefore the
   implementation should prove the bump-difference theorem through the
   following explicit radial package, not through an abstract parametrix
   wrapper.

   First record the radiality and weighted-mass facts for the checked bump.
   The `ContDiffBumpBase.ofInnerProductSpace` construction is radial in the
   Euclidean norm, and the normalized denominator is scalar, so equality of
   norms gives equality of bump values:

   ```lean
   theorem euclideanWeylBump_eq_of_norm_eq
       {ι : Type*} [Fintype ι]
       {ε : ℝ} (hε : 0 < ε)
       {x y : EuclideanSpace ℝ ι} (hxy : ‖x‖ = ‖y‖) :
       euclideanWeylBump ε hε x = euclideanWeylBump ε hε y

   theorem euclideanWeylBump_sub_eq_of_norm_eq
       {ι : Type*} [Fintype ι]
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
       {x y : EuclideanSpace ℝ ι} (hxy : ‖x‖ = ‖y‖) :
       ((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
         SchwartzMap (EuclideanSpace ℝ ι) ℂ) x) =
       ((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
         SchwartzMap (EuclideanSpace ℝ ι) ℂ) y)
   ```

   Next isolate the mass-compatibility input needed by the ODE.  Do **not**
   introduce a full polar-coordinate theorem here unless later work actually
   needs it.  For this bump difference, the weighted radial mass is zero by a
   smaller scaling argument: all radii use one fixed radial profile
   `β(s) = smoothTransition (2 - 2 * s)`; the Euclidean normalization
   denominator scales like `ε ^ N` under the linear change of variables
   `x = ε • y`, and the one-variable weighted profile integral scales by the
   same `ε ^ N` under `r = ε * s`.  Hence every normalized radius has the same
   weighted radial mass, so the difference of two normalized radii has weighted
   mass zero.  This avoids a broad integration theorem and keeps the proof
   exactly on the mollifier scale-invariance route.

   ```lean
   noncomputable def euclideanWeylBaseProfile (r : ℝ) : ℂ :=
     (Real.smoothTransition (2 - 2 * |r|) : ℂ)

   noncomputable def euclideanWeylRawIntegralReal
       {ι : Type*} [Fintype ι] (ε : ℝ) : ℝ :=
     ∫ x : EuclideanSpace ℝ ι, euclideanWeylRawBumpReal ε x

   noncomputable def euclideanWeylWeightedRawMass
       (N : ℕ) (ε : ℝ) : ℂ :=
     ∫ r in Set.Ioi 0,
       ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylBaseProfile (r / ε)

   noncomputable def euclideanWeylNormalizedProfile
       {ι : Type*} [Fintype ι] (ε : ℝ) : ℝ -> ℂ :=
     fun r =>
       (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) *
         euclideanWeylBaseProfile (r / ε)

   theorem euclideanWeylBump_raw_profile
       {ι : Type*} [Fintype ι]
       {ε : ℝ} (hε : 0 < ε) :
       ∀ x : EuclideanSpace ℝ ι,
         euclideanWeylBump ε hε x =
           euclideanWeylNormalizedProfile (ι := ι) ε ‖x‖

   theorem euclideanWeylRawIntegralReal_scale
       {ι : Type*} [Fintype ι]
       {ε : ℝ} (hε : 0 < ε) :
       euclideanWeylRawIntegralReal (ι := ι) ε =
         ε ^ Fintype.card ι *
           euclideanWeylRawIntegralReal (ι := ι) 1

   theorem euclideanWeylWeightedRawMass_scale
       {N : ℕ} (hNpos : 0 < N) {ε : ℝ} (hε : 0 < ε) :
       euclideanWeylWeightedRawMass N ε =
         (((ε ^ N : ℝ) : ℂ)) * euclideanWeylWeightedRawMass N 1

   theorem euclideanWeylBump_weightedMass_eq_const
       {ι : Type*} [Fintype ι] [Nonempty ι]
       {ε : ℝ} (hε : 0 < ε) :
       ∫ r in Set.Ioi 0,
         ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
           euclideanWeylNormalizedProfile (ι := ι) ε r =
       (((euclideanWeylRawIntegralReal (ι := ι) 1 : ℝ) : ℂ)⁻¹) *
         euclideanWeylWeightedRawMass (Fintype.card ι) 1

   noncomputable def euclideanWeylBumpSubProfile
       {ι : Type*} [Fintype ι]
       (ε δ : ℝ) : ℝ -> ℂ :=
     fun r =>
       euclideanWeylNormalizedProfile (ι := ι) ε r -
       euclideanWeylNormalizedProfile (ι := ι) δ r

   theorem euclideanWeylBumpSubProfile_spec
       {ι : Type*} [Fintype ι] [Nonempty ι]
       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       ContDiff ℝ (⊤ : ℕ∞) (euclideanWeylBumpSubProfile (ι := ι) ε δ) ∧
       Function.support (euclideanWeylBumpSubProfile (ι := ι) ε δ) ⊆
         Set.Icc (-(max ε δ)) (max ε δ) ∧
       (∃ η : ℝ, ∃ c : ℂ, 0 < η ∧
         ∀ r ∈ Set.Icc 0 η,
           euclideanWeylBumpSubProfile (ι := ι) ε δ r = c) ∧
       (∀ x : EuclideanSpace ℝ ι,
         euclideanWeylBumpSubProfile (ι := ι) ε δ ‖x‖ =
           (euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
             SchwartzMap (EuclideanSpace ℝ ι) ℂ) x) ∧
       (∫ r in Set.Ioi 0,
         ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
           euclideanWeylBumpSubProfile (ι := ι) ε δ r) = 0
   ```

   The proof of `euclideanWeylRawIntegralReal_scale` is the exact Euclidean
   Haar scaling theorem, not polar integration.  Rewrite
   `euclideanWeylRawBumpReal ε x` as
   `euclideanWeylRawBumpReal 1 (ε⁻¹ • x)` by
   `euclideanWeylRawBumpReal_apply`, then use
   `MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume` and
   `finrank_euclideanSpace`.  The proof of
   `euclideanWeylWeightedRawMass_scale` is the one-dimensional substitution
   theorem `MeasureTheory.integral_comp_mul_left_Ioi`: after applying it to
   `G r = ((r ^ (N - 1) : ℝ) : ℂ) *
     euclideanWeylBaseProfile (r / ε)`, the integrand
   `G (ε * s)` rewrites to
   `(((ε ^ (N - 1) : ℝ) : ℂ)) *
     ((s ^ (N - 1) : ℝ) : ℂ) * euclideanWeylBaseProfile s`.
   Multiplying by the Jacobian `ε` gives `ε ^ N`.  The normalized weighted
   mass is therefore independent of the radius because the Euclidean
   denominator and the weighted one-dimensional numerator carry the same
   `ε ^ N` factor.  Positivity of the real raw integral supplies the nonzero
   denominator.

   The profile `euclideanWeylBumpSubProfile ε δ` is built directly from the
   explicit `ContDiffBumpBase.ofInnerProductSpace` formula.  Its scalar
   smoothness is proved without differentiating `|r|` directly: identify
   `r ↦ euclideanWeylBaseProfile (r / ε)` with the checked raw Euclidean bump
   on `EuclideanSpace ℝ (Fin 1)` along the smooth line
   `r ↦ r • EuclideanSpace.single 0 1`.  Near `0` the subprofile is constant
   because each bump is equal to its normalized plateau value on
   `closedBall 0 (min ε δ / 2)`.  Near and beyond `max ε δ` it is identically
   zero.  These two local-constancy facts are what make the radial primitive
   smooth at the origin and compactly supported at the outer radius; do not
   replace them by an unexplained "radial smoothness" phrase.

   The radial Poisson primitive itself lives in a separate companion file, so
   the checked bump file stays small:

   ```lean
   import OSReconstruction.SCV.EuclideanWeylBump
   import Mathlib.Analysis.InnerProductSpace.Calculus
   import Mathlib.Analysis.InnerProductSpace.Laplacian
   import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
   import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
   ```

   ```lean
   def radialProfileLaplacian (N : ℕ) (a : ℝ -> ℂ) (r : ℝ) : ℂ :=
     deriv (deriv a) r + (((N - 1 : ℝ) / r : ℝ) : ℂ) * deriv a r

   noncomputable def radialMass (N : ℕ) (F : ℝ -> ℂ) (r : ℝ) : ℂ :=
     ∫ s in (0)..r, ((s ^ (N - 1) : ℝ) : ℂ) * F s

   noncomputable def radialPrimitiveDeriv
       (N : ℕ) (F : ℝ -> ℂ) (r : ℝ) : ℂ :=
     if r = 0 then 0
     else (((r ^ (N - 1) : ℝ) : ℂ)⁻¹) * radialMass N F r

   noncomputable def radialPrimitiveProfile
       (N : ℕ) (F : ℝ -> ℂ) (R r : ℝ) : ℂ :=
     -∫ t in r..R, radialPrimitiveDeriv N F t

   theorem radialMass_eq_weightedMass_of_support
       {N : ℕ} {F : ℝ -> ℂ} {R : ℝ}
       (hR : 0 ≤ R)
       (hweight_int :
         IntegrableOn
           (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ) * F r)
           (Set.Ioi 0) volume)
       (hF_support : Function.support F ⊆ Set.Icc (-R) R) :
       radialMass N F R =
         ∫ r in Set.Ioi 0, ((r ^ (N - 1) : ℝ) : ℂ) * F r

   theorem radialMass_eq_const_near_zero
       {N : ℕ} (hNpos : 0 < N) {F : ℝ -> ℂ} {η r : ℝ} {c : ℂ}
       (hη : 0 < η)
       (hr_nonneg : 0 ≤ r) (hr_le : r ≤ η)
       (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
       radialMass N F r =
         c * (((r ^ N : ℝ) : ℂ) / (N : ℂ))

   theorem radialPrimitiveDeriv_eq_linear_near_zero
       {N : ℕ} (hNpos : 0 < N) {F : ℝ -> ℂ} {η r : ℝ} {c : ℂ}
       (hη : 0 < η)
       (hr_pos : 0 < r) (hr_le : r ≤ η)
       (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
       radialPrimitiveDeriv N F r =
         c * (((r : ℝ) : ℂ) / (N : ℂ))

   theorem radialPrimitiveProfile_eq_quadratic_near_zero
       {N : ℕ} (hNpos : 0 < N) {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hη : 0 < η) (hηR : η ≤ R)
       (hprim_int_tail :
         IntervalIntegrable (radialPrimitiveDeriv N F) volume η R)
       (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
       ∃ C : ℂ,
         ∀ r ∈ Set.Icc 0 η,
           radialPrimitiveProfile N F R r =
             C + (c / (2 * (N : ℂ))) * (((r ^ 2 : ℝ) : ℂ))

   theorem deriv_radialMass
       {N : ℕ} {F : ℝ -> ℂ}
       (hF_cont : Continuous F) :
       ∀ r ∈ Set.Ioi 0,
         deriv (radialMass N F) r =
           ((r ^ (N - 1) : ℝ) : ℂ) * F r

   theorem deriv_radialPrimitiveDeriv
       {N : ℕ} (hNpos : 0 < N) {F : ℝ -> ℂ}
       (hF_cont : Continuous F) :
       ∀ r ∈ Set.Ioi 0,
         deriv (radialPrimitiveDeriv N F) r +
           (((((N - 1 : ℕ) : ℝ) / r : ℝ) : ℂ) *
             radialPrimitiveDeriv N F r) = F r

   theorem continuousAt_radialPrimitiveDeriv_of_pos
       {N : ℕ} {F : ℝ -> ℂ}
       (hF_cont : Continuous F) {r : ℝ} (hr : 0 < r) :
       ContinuousAt (radialPrimitiveDeriv N F) r

   theorem intervalIntegrable_radialPrimitiveDeriv_of_pos
       {N : ℕ} {F : ℝ -> ℂ}
       (hF_cont : Continuous F) {a b : ℝ}
       (ha : 0 < a) (hb : 0 < b) :
       IntervalIntegrable (radialPrimitiveDeriv N F) volume a b

   theorem hasDerivAt_radialPrimitiveProfile_of_pos
       {N : ℕ} {F : ℝ -> ℂ} {R r : ℝ}
       (hF_cont : Continuous F)
       (hprim_int :
         IntervalIntegrable (radialPrimitiveDeriv N F) volume r R)
       (hr : 0 < r) :
       HasDerivAt (fun u : ℝ => radialPrimitiveProfile N F R u)
         (radialPrimitiveDeriv N F r) r

   theorem radialProfileLaplacian_radialPrimitiveProfile_of_pos_of_R_pos
       {N : ℕ} (hNpos : 0 < N) {F : ℝ -> ℂ} {R : ℝ}
       (hF_cont : Continuous F) (hRpos : 0 < R) :
       ∀ r ∈ Set.Ioi 0,
         radialProfileLaplacian N
             (fun u : ℝ => radialPrimitiveProfile N F R u) r = F r

   theorem radialPrimitiveProfile_eventually_quadratic_norm_near_zero
       {ι : Type*} [Fintype ι]
       {N : ℕ} (hNpos : 0 < N) {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hη : 0 < η) (hηR : η ≤ R)
       (hprim_int_tail :
         IntervalIntegrable (radialPrimitiveDeriv N F) volume η R)
       (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c) :
       ∃ C : ℂ, ∀ᶠ x : EuclideanSpace ℝ ι in 𝓝 0,
         radialPrimitiveProfile N F R ‖x‖ =
           C + (c / (2 * (N : ℂ))) * (((‖x‖ ^ 2 : ℝ) : ℂ))

   theorem laplacian_norm_sq_real
       {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
       Laplacian.laplacian
           (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2) x =
         (2 * Fintype.card ι : ℝ)

   theorem laplacian_quadratic_norm_complex
       {ι : Type*} [Fintype ι]
       (C K : ℂ) (x : EuclideanSpace ℝ ι) :
       Laplacian.laplacian
           (fun y : EuclideanSpace ℝ ι =>
             C + K * (((‖y‖ ^ 2 : ℝ) : ℂ))) x =
         K * ((2 * Fintype.card ι : ℝ) : ℂ)

   theorem contDiffAt_radialPrimitiveProfile_norm_zero
       {ι : Type*} [Fintype ι]
       {N : ℕ} (hNpos : 0 < N) {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hη : 0 < η) (hηR : η ≤ R)
       (hprim_int_tail :
         IntervalIntegrable (radialPrimitiveDeriv N F) volume η R)
       (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
       ContDiffAt ℝ (⊤ : ℕ∞)
         (fun x : EuclideanSpace ℝ ι =>
           radialPrimitiveProfile N F R ‖x‖) 0

   theorem laplacian_radialPrimitiveProfile_norm_zero
       {ι : Type*} [Fintype ι]
       {N : ℕ} (hN : N = Fintype.card ι) (hNpos : 0 < N)
       {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hη : 0 < η) (hηR : η ≤ R)
       (hprim_int_tail :
         IntervalIntegrable (radialPrimitiveDeriv N F) volume η R)
       (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
       Laplacian.laplacian
           (fun x : EuclideanSpace ℝ ι =>
             radialPrimitiveProfile N F R ‖x‖) 0 = c

   theorem radialPrimitiveProfile_eventually_zero_outside
       {N : ℕ} {F : ℝ -> ℂ} {R : ℝ}
       (hF_cont : Continuous F)
       (hR : 0 ≤ R)
       (hF_support : Function.support F ⊆ Set.Icc (-R) R)
       (hMass_R : radialMass N F R = 0) :
       ∀ᶠ r : ℝ in Filter.atTop, radialPrimitiveProfile N F R r = 0

   theorem contDiff_radialPrimitiveProfile_norm
       {ι : Type*} [Fintype ι]
       {N : ℕ} (hNpos : 0 < N)
       {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hRpos : 0 < R)
       (hη : 0 < η) (hηR : η ≤ R)
       (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
       (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c) :
       ContDiff ℝ (⊤ : ℕ∞)
         (fun x : EuclideanSpace ℝ ι =>
           radialPrimitiveProfile N F R ‖x‖)

   theorem laplacian_radialPrimitiveProfile
       {ι : Type*} [Fintype ι]
       {N : ℕ} (hN : N = Fintype.card ι)
       (hNpos : 0 < N) {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hRpos : 0 < R)
       (hη : 0 < η) (hηR : η ≤ R)
       (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
       (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c) :
       ∀ x : EuclideanSpace ℝ ι,
         Laplacian.laplacian
           (fun y : EuclideanSpace ℝ ι =>
             radialPrimitiveProfile N F R ‖y‖) x = F ‖x‖

	   theorem exists_schwartz_radialPrimitiveProfile_norm
	       {ι : Type*} [Fintype ι]
	       {N : ℕ} (hNpos : 0 < N)
	       {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
       (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
       (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c)
       (hF_support : Function.support F ⊆ Set.Icc (-R) R)
       (hMass_R : radialMass N F R = 0) :
	       ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	         HasCompactSupport (A : EuclideanSpace ℝ ι -> ℂ) ∧
	         ∀ x : EuclideanSpace ℝ ι,
	           A x = radialPrimitiveProfile N F R ‖x‖

	   theorem tsupport_radialPrimitiveProfile_norm_subset
	       {ι : Type*} [Fintype ι]
	       {N : ℕ} {F : ℝ -> ℂ} {R : ℝ}
	       (hF_cont : Continuous F) (hR : 0 ≤ R)
	       (hF_support : Function.support F ⊆ Set.Icc (-R) R)
	       (hMass_R : radialMass N F R = 0) :
	       tsupport
	           (fun x : EuclideanSpace ℝ ι =>
	             radialPrimitiveProfile N F R ‖x‖) ⊆
	         Metric.closedBall 0 R

	   theorem exists_schwartz_radialPrimitiveProfile_norm_with_support
	       {ι : Type*} [Fintype ι]
	       {N : ℕ} (hNpos : 0 < N)
	       {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
	       (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
	       (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
	       (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c)
	       (hF_support : Function.support F ⊆ Set.Icc (-R) R)
	       (hMass_R : radialMass N F R = 0) :
	       ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	         HasCompactSupport (A : EuclideanSpace ℝ ι -> ℂ) ∧
	         tsupport (A : EuclideanSpace ℝ ι -> ℂ) ⊆
	           Metric.closedBall 0 R ∧
	         ∀ x : EuclideanSpace ℝ ι,
	           A x = radialPrimitiveProfile N F R ‖x‖

	   theorem exists_compact_laplacian_eq_radial_schwartz
	       {ι : Type*} [Fintype ι]
	       {N : ℕ} (hN : N = Fintype.card ι) (hNpos : 0 < N)
       {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
       (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
       (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c)
       (hF_support : Function.support F ⊆ Set.Icc (-R) R)
       (hMass_R : radialMass N F R = 0)
       (B : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
       (hB : ∀ x : EuclideanSpace ℝ ι, B x = F ‖x‖) :
	       ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	         HasCompactSupport (A : EuclideanSpace ℝ ι -> ℂ) ∧
	         LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	           (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A = B

	   theorem exists_compact_laplacian_eq_radial_schwartz_with_support
	       {ι : Type*} [Fintype ι]
	       {N : ℕ} (hN : N = Fintype.card ι) (hNpos : 0 < N)
	       {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
	       (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
	       (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
	       (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c)
	       (hF_support : Function.support F ⊆ Set.Icc (-R) R)
	       (hMass_R : radialMass N F R = 0)
	       (B : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	       (hB : ∀ x : EuclideanSpace ℝ ι, B x = F ‖x‖) :
	       ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	         HasCompactSupport (A : EuclideanSpace ℝ ι -> ℂ) ∧
	         tsupport (A : EuclideanSpace ℝ ι -> ℂ) ⊆
	           Metric.closedBall 0 R ∧
	         LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	           (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A = B

	   theorem exists_compact_laplacian_eq_euclideanWeylBump_sub
	       {ι : Type*} [Fintype ι] [Nonempty ι]
	       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
       ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
         HasCompactSupport (A : EuclideanSpace ℝ ι -> ℂ) ∧
	         LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	           (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A =
	           euclideanWeylBump ε hε - euclideanWeylBump δ hδ

	   theorem exists_compact_laplacian_eq_euclideanWeylBump_sub_with_support
	       {ι : Type*} [Fintype ι] [Nonempty ι]
	       {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
	       ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	         HasCompactSupport (A : EuclideanSpace ℝ ι -> ℂ) ∧
	         tsupport (A : EuclideanSpace ℝ ι -> ℂ) ⊆
	           Metric.closedBall 0 (max ε δ) ∧
	         LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	           (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A =
	           euclideanWeylBump ε hε - euclideanWeylBump δ hδ
	   ```

   Production status in `SCV/EuclideanWeylPoisson.lean`: the definitions
   `radialMass`, `radialPrimitiveDeriv`, and `radialPrimitiveProfile`, plus
   `radialMass_zero`, `radialPrimitiveDeriv_zero`,
   `radialPrimitiveProfile_self`, `deriv_radialMass`,
   `hasDerivAt_radialMass`,
   `radialMass_eq_weightedMass_of_support`,
   `radialMass_eq_const_near_zero`,
   `radialPrimitiveDeriv_eq_inv_mul`,
   `radialPrimitiveDeriv_mul_power_eq_radialMass`, and
   `radialPrimitiveDeriv_eq_linear_near_zero`, and
   `radialPrimitiveProfile_eq_quadratic_near_zero`,
   `deriv_radialPrimitiveDeriv`,
   `continuousAt_radialPrimitiveDeriv_of_pos`,
   `intervalIntegrable_radialPrimitiveDeriv_of_pos`,
   `hasDerivAt_radialPrimitiveProfile_of_pos`,
   `deriv_radialPrimitiveProfile_of_pos`,
   `radialProfileLaplacian_radialPrimitiveProfile_of_pos`,
   `radialProfileLaplacian_radialPrimitiveProfile_of_pos_of_R_pos`,
   `radialPrimitiveProfile_eventually_quadratic_norm_near_zero`,
   `laplacian_norm_sq_real`,
   `laplacian_quadratic_norm_complex`,
   `contDiffAt_radialPrimitiveProfile_norm_zero`,
   `laplacian_radialPrimitiveProfile_norm_zero`,
   `contDiffOn_radialPrimitiveDeriv_of_smooth`,
   `contDiffOn_radialPrimitiveProfile_of_pos`,
   `contDiffOn_radialPrimitiveDeriv_of_smooth_infty`,
   `contDiffOn_radialPrimitiveProfile_of_pos_infty`,
   `eventually_fderiv_radial_comp_basisFun_eq`,
   `iteratedFDeriv_radial_comp_basisFun_basisFun`,
   `laplacian_radialProfile_off_origin`,
   `laplacian_radialPrimitiveProfile`,
   `contDiff_radialPrimitiveProfile_norm`,
	   `radialMass_eq_radialMass_of_support_ge`,
	   `radialPrimitiveProfile_eq_zero_of_ge`, and
	   `radialPrimitiveProfile_eventually_zero_outside`,
	   `tsupport_radialPrimitiveProfile_norm_subset`,
	   `hasCompactSupport_radialPrimitiveProfile_norm`,
	   `exists_schwartz_radialPrimitiveProfile_norm`,
	   `exists_schwartz_radialPrimitiveProfile_norm_with_support`,
	   `exists_compact_laplacian_eq_radial_schwartz`,
	   `exists_compact_laplacian_eq_radial_schwartz_with_support`,
	   `exists_compact_laplacian_eq_euclideanWeylBump_sub`,
	   `exists_compact_laplacian_eq_euclideanWeylBump_sub_with_support`,
	   `lineDerivOp_euclideanTranslateSchwartzCLM`,
	   `lineDerivOp_euclideanReflectedTranslate`, and
	   `laplacianCLM_euclideanReflectedTranslate`, and
	   `regularizedDistribution_bump_scale_eq` are checked.  The
	   finite-dimensional norm-to-coordinate-Laplacian calculation, its assembly
	   with the checked origin theorem, and the resulting all-points radial
	   Poisson equation are no longer blockers.  The bump-difference specialization
	   as a compactly supported Schwartz test function is checked in positive
	   dimension, with the exact support radius needed by translated local
	   harmonicity; the reflected-translate Laplacian commutation is checked; and
	   local harmonic scale invariance for normalized bumps is checked.  The
	   companion `SCV/EuclideanWeylRegularity.lean` now also checks
	   `closedBall_subset_ball_of_half_margin`,
	   `closedBall_subset_ball_of_uniform_margin`,
	   `euclideanWeylBallRepresentative`,
	   `euclideanWeylBallRepresentative_eq_regularized`,
	   `euclideanWeylBallRepresentative_eq_regularized_on_ball`, and
	   `contDiffOn_euclideanWeylBallRepresentative`.  Remaining local Weyl work
	   is the convolution/approximate-identity representation assembly, plus
	   zero-dimensional bookkeeping if a caller needs a dimension-free
	   bump-difference theorem.

   Proof transcript.  Split first on `Fintype.card ι = 0`; after that no
   separate `card = 1` mathematical route is needed.  For every
   positive-dimensional Euclidean space, the same proof works: off the origin
   the norm is smooth and the standard radial-Laplacian formula is valid, while
   the origin is handled by the checked quadratic germ.

   * If `Fintype.card ι = 0`, the Euclidean space is a singleton.  Use
     `Subsingleton.elim` for the domain and the checked normalization of both
     bumps to show the bump difference is the zero Schwartz function; take
     `A = 0`.  This is the only zero-dimensional route; do not try to feed
     `N = 0` into the radial ODE, where `r ^ (N - 1)` is not the intended
     Jacobian.

   * If `0 < Fintype.card ι`, use the standard radial-Laplacian theorem.  Obtain
     the profile `F` and `weightedMass = 0` from
     `euclideanWeylBumpSubProfile_spec`, set `N = Fintype.card ι`,
     `R = max ε δ`, and define
     `A₀ x = radialPrimitiveProfile N F R ‖x‖`.  The profile is an even smooth
     extension in the scalar variable, with support in `[-R, R]`; the ODE uses
     only its restriction to `r >= 0`.  The derivative calculation is exactly
     `(r^(N-1) A'(r))' = r^(N-1) F(r)`: `deriv_radialMass` is FTC-1,
     `deriv_radialPrimitiveDeriv` is one field-simplification on `0 < r`,
     `radialProfileLaplacian_radialPrimitiveProfile_of_pos_of_R_pos` gives the
     scalar profile Laplacian for `r > 0`, and
     `laplacian_radialPrimitiveProfile_norm_zero` gives the Euclidean
     Laplacian at `x = 0`.  The absolute-value cusp in dimension one is not
     hidden: it is exactly the origin case already discharged by the quadratic
     norm theorem.

	   In the positive-dimensional cases, the support theorem uses
	   `radialMass N F R = 0` and `F = 0` for `r >= R` to prove `A₀ = 0` outside
	   `closedBall 0 R`.  This must be recorded as the stronger support-radius
	   theorem
	   `tsupport_radialPrimitiveProfile_norm_subset`, not merely as compact
	   support, because the local scale-invariance proof must feed the translated
	   primitive to a hypothesis whose support is restricted to the open set `V`.
	   The proof is:

	   ```lean
	   theorem tsupport_radialPrimitiveProfile_norm_subset ... :
	       tsupport (fun x => radialPrimitiveProfile N F R ‖x‖) ⊆
	         Metric.closedBall 0 R := by
	     let E := EuclideanSpace ℝ ι
	     have hsupp :
	         Function.support
	           (fun x : E => radialPrimitiveProfile N F R ‖x‖) ⊆
	         Metric.closedBall 0 R := by
	       intro x hx
	       rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
	       by_contra hnot
	       have hR_le : R ≤ ‖x‖ := le_of_lt (not_le.mp hnot)
	       exact hx
	         (radialPrimitiveProfile_eq_zero_of_ge
	           hF_cont hR hR_le hF_support hMass_R)
	     rw [tsupport]
	     exact closure_minimal hsupp isClosed_closedBall
	   ```

	   Then `hasCompactSupport_radialPrimitiveProfile_norm` is the compactness
	   corollary obtained from `isCompact_closedBall`, and the Schwartz packaging
	   theorem should carry both outputs:

	   ```lean
	   rcases exists_schwartz_radialPrimitiveProfile_norm_with_support ... with
	     ⟨A, hAcompact, hAsupp, hAeq⟩
	   ```

	   Use `SchwartzMap.laplacian_apply` and
	   `laplacian_radialPrimitiveProfile` to ext the Laplacian equality.  Keep
	   these theorems pure analysis and independent of `T`, `U0`, OS, Wightman,
	   or EOW.

   Lean proof notes for the radial ODE package:

   * `radialMass_eq_weightedMass_of_support` is now checked.  It is the bridge
     from the checked `Ioi` weighted-mass theorem to the ODE boundary condition.
     Its statement explicitly assumes `IntegrableOn` of the weighted profile on
     `Set.Ioi 0`; this is supplied later by smooth compact support, and should
     not be hidden in the bridge.  The proof rewrites the `Ioi` integral as the
     interval integral over `(0, R]` plus the tail over `(R, ∞)`, then kills the
     tail using `Function.support F ⊆ Set.Icc (-R) R`.

   * `deriv_radialMass` should use
     `Continuous.deriv_integral` /
     `intervalIntegral.integral_hasDerivAt_right` for the continuous integrand
     `s ↦ ((s ^ (N - 1) : ℝ) : ℂ) * F s`.  Keep the statement on `Set.Ioi 0`
     so all later field simplifications can use `r ≠ 0`.

   * Near zero, prove the three explicit formulas in order:
     `radialMass_eq_const_near_zero`,
     `radialPrimitiveDeriv_eq_linear_near_zero`, and
     `radialPrimitiveProfile_eq_quadratic_near_zero`.  All three are now
     checked.  The key checked algebra is
     `∫ s in 0..r, s^(N-1) = r^N / N` for `0 ≤ r ≤ η` and `0 < N`, using
     `intervalIntegral.integral_congr`, `integral_complex_ofReal`, and
     `integral_pow`.  The quadratic theorem chooses one constant
     independent of `r`,
     `C = -(∫ t in η..R, radialPrimitiveDeriv N F t) -
       (c / (2 * (N : ℂ))) * (((η ^ 2 : ℝ) : ℂ))`,
     and proves the formula for every `r ∈ Icc 0 η` by splitting
     `∫ t in r..R` into `∫ t in r..η + ∫ t in η..R`.  This is what removes the
     apparent singularity at `r = 0`; it must appear as an explicit theorem,
     not as a comment inside the Laplacian proof.

   * Away from zero, `hasDerivAt_radialMass` and
     `deriv_radialPrimitiveDeriv` are now checked.  The proof uses the local
     identity
     `radialPrimitiveDeriv N F r =
       (((r ^ (N - 1) : ℝ) : ℂ)⁻¹) * radialMass N F r`
     on `Set.Ioi 0`, differentiates the real inverse power
     `r ↦ (r ^ (N - 1))⁻¹`, composes it through `Complex.ofRealCLM`, and closes
     the log-derivative algebra with the split `N = 1` / `N ≥ 2`.  The checked
     statement is exactly
     `deriv (radialPrimitiveDeriv N F) r +
       (((((N - 1 : ℕ) : ℝ) / r : ℝ) : ℂ) *
         radialPrimitiveDeriv N F r) = F r`
     for `0 < r`.

   * Outside `R`, `radialMass_eq_radialMass_of_support_ge`,
     `radialPrimitiveProfile_eq_zero_of_ge`, and
     `radialPrimitiveProfile_eventually_zero_outside` are now checked.  The
     mass-constancy lemma assumes `Continuous F`, splits `∫ 0..r` at `R`, and
     kills `∫ R..r` by support zero on the `uIoc` interval.  Combined with
     `radialMass N F R = 0`, the primitive derivative vanishes for `R < r`;
     the defining interval integral for `radialPrimitiveProfile` is then zero
     for every `r ≥ R`, hence eventually at `Filter.atTop`.

   * The scalar profile-Laplacian theorem is now checked.  The proof first
     proves continuity of `radialPrimitiveDeriv` on `Ioi 0`, then obtains
     `HasDerivAt (radialPrimitiveProfile N F R) (radialPrimitiveDeriv N F r)`
     by the left-endpoint FTC.  Differentiating the first-derivative identity
     only locally on `Ioi 0` gives
     `radialProfileLaplacian N (fun r => radialPrimitiveProfile N F R r) r =
     F r`.  The convenient consumer
     `radialProfileLaplacian_radialPrimitiveProfile_of_pos_of_R_pos` supplies
     all interval-integrability hypotheses from `Continuous F` and `0 < R`.

   * The origin theorem is now checked.  The explicit near-zero formula is
     transported to Euclidean space by
     `radialPrimitiveProfile_eventually_quadratic_norm_near_zero`.  Mathlib's
     function Laplacian API gives
     `laplacian_norm_sq_real : Δ (fun x => ‖x‖^2) = 2 * Fintype.card ι`;
     composing with `Complex.ofRealCLM`, adding the constant, and multiplying
     by `K = c / (2 * (N : ℂ))` gives
     `laplacian_quadratic_norm_complex`.  Therefore
     `contDiffAt_radialPrimitiveProfile_norm_zero` and
     `laplacian_radialPrimitiveProfile_norm_zero` are both checked with no
     dimension split.

   The off-origin geometric lemma is now checked.  It is the direct
   finite-dimensional calculus identity below, with no parametrix wrapper:

   ```lean
   theorem laplacian_radialProfile_off_origin
       {ι : Type*} [Fintype ι]
       {N : ℕ} (hN : N = Fintype.card ι)
       {a : ℝ -> ℂ} {x : EuclideanSpace ℝ ι}
       (hx : x ≠ 0)
       (ha : ContDiffAt ℝ 2 a ‖x‖) :
       Laplacian.laplacian
           (fun y : EuclideanSpace ℝ ι => a ‖y‖) x =
         radialProfileLaplacian N a ‖x‖
   ```

   The proof should not introduce a parametrix wrapper.  It is a direct
   finite-dimensional calculus identity:

   1. Let `ρ y = ‖y‖`, `e i = EuclideanSpace.basisFun ι ℝ i`, and
      `r = ρ x`.  From `hx`, get `0 < r`.
   2. Prove the norm derivatives away from zero:

      ```lean
      have hρ₁ :
        HasFDerivAt ρ ((r⁻¹ : ℝ) • innerSL ℝ x) x
      have hρ₁_i :
        fderiv ℝ ρ x (e i) = x i / r
      have hρ₂_i :
        iteratedFDeriv ℝ 2 ρ x ![e i, e i] =
          1 / r - (x i)^2 / r^3
      ```

      `hρ₁` comes from `ρ = sqrt (fun y => ‖y‖^2)` and
      `hasStrictFDerivAt_norm_sq`; `hρ₂_i` is the derivative of
      `y ↦ inner ℝ y (e i) / ‖y‖` in the same coordinate direction.
      Use `EuclideanSpace.basisFun_inner`, `real_inner_self_eq_norm_sq`, and
      `field_simp [hr.ne']`.
   3. Apply the one-variable chain rule twice to `a ∘ ρ`:

      ```lean
      iteratedFDeriv ℝ 2 (fun y => a (ρ y)) x ![e i, e i] =
        deriv (deriv a) r * (((x i / r : ℝ) : ℂ)^2) +
        deriv a r * (((1 / r - (x i)^2 / r^3 : ℝ) : ℂ))
      ```

      This is the real Hessian formula for a scalar radial function; keep it as
      an explicit lemma if the term-level chain rule is long.
   4. Sum over `i`.  Use
      `EuclideanSpace.norm_sq_eq` to rewrite
      `∑ i, (x i)^2 = r^2`, and `hN` to rewrite the number of basis vectors.
      This summation layer should be proved before the full chain-rule
      theorem, since it is pure finite-dimensional Euclidean algebra:

      ```lean
      theorem euclidean_card_pos_of_ne_zero
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
          0 < Fintype.card ι

      theorem nat_cast_card_sub_one_of_ne_zero
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
          (((Fintype.card ι - 1 : ℕ) : ℝ) =
            (Fintype.card ι : ℝ) - 1)

      theorem sum_coord_sq_div_norm_sq_eq_one
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
          (∑ i : ι, (x i / ‖x‖)^2) = (1 : ℝ)

      theorem sum_complex_coord_sq_div_norm_sq_eq_one
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
          (∑ i : ι, (((x i / ‖x‖ : ℝ) : ℂ)^2)) = (1 : ℂ)

      theorem sum_radial_norm_hessian_coeff
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
          (∑ i : ι, (1 / ‖x‖ - (x i)^2 / ‖x‖^3)) =
            ((Fintype.card ι : ℝ) - 1) / ‖x‖

      theorem sum_complex_radial_norm_hessian_coeff
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
          (∑ i : ι,
            (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))) =
            ((((Fintype.card ι : ℝ) - 1) / ‖x‖ : ℝ) : ℂ)
      ```

      Proof transcript: `euclidean_card_pos_of_ne_zero` is by contradiction;
      if `Fintype.card ι = 0`, then `ι` is empty and
      `EuclideanSpace ℝ ι` is subsingleton, contradicting `x ≠ 0`.
      The first sum identity rewrites `‖x‖^2` by
      `EuclideanSpace.norm_sq_eq`, with `Real.norm_eq_abs` and `sq_abs`, then
      divides by `‖x‖^2` using `norm_pos_iff.mpr hx`.  The Hessian-coefficient
      sum uses `Finset.sum_sub_distrib`, `Finset.sum_const`,
      `Finset.sum_div`, the same norm-square identity, and `field_simp`.
      The complex versions are `exact_mod_cast` from the real identities.

      Therefore the coordinate sum is
      `deriv (deriv a) r + (((N - 1 : ℝ) / r : ℝ) : ℂ) * deriv a r`,
      which is exactly `radialProfileLaplacian N a r`.

   5. Keep the analytic chain-rule layer separate from the summation layer.
      The final off-origin theorem should depend on these exact calculus
      slots, not on any parametrix or Poisson-specific wrapper:

      ```lean
      theorem hasFDerivAt_norm_off_origin
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
          HasFDerivAt
            (fun y : EuclideanSpace ℝ ι => ‖y‖)
            ((‖x‖⁻¹ : ℝ) • innerSL ℝ x) x

      theorem fderiv_norm_basisFun_off_origin
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
          fderiv ℝ (fun y : EuclideanSpace ℝ ι => ‖y‖) x
              ((EuclideanSpace.basisFun ι ℝ) i) =
            x i / ‖x‖

      theorem iteratedFDeriv_norm_basisFun_basisFun_off_origin
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
          iteratedFDeriv ℝ 2
              (fun y : EuclideanSpace ℝ ι => ‖y‖) x
              ![(EuclideanSpace.basisFun ι ℝ) i,
                (EuclideanSpace.basisFun ι ℝ) i] =
            1 / ‖x‖ - (x i)^2 / ‖x‖^3

      theorem fderiv_coord_div_norm_basisFun
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
          fderiv ℝ (fun y : EuclideanSpace ℝ ι => y i / ‖y‖) x
              ((EuclideanSpace.basisFun ι ℝ) i) =
            1 / ‖x‖ - (x i)^2 / ‖x‖^3

      theorem fderiv_complex_coord_div_norm_basisFun
          {ι : Type*} [Fintype ι]
          {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
          fderiv ℝ
              (fun y : EuclideanSpace ℝ ι =>
                (((y i / ‖y‖ : ℝ) : ℂ))) x
              ((EuclideanSpace.basisFun ι ℝ) i) =
            (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))

      theorem fderiv_radial_comp_basisFun_off_origin
          {ι : Type*} [Fintype ι]
          {a : ℝ -> ℂ} {x : EuclideanSpace ℝ ι}
          (hx : x ≠ 0) (ha : DifferentiableAt ℝ a ‖x‖) (i : ι) :
          fderiv ℝ (fun y : EuclideanSpace ℝ ι => a ‖y‖) x
              ((EuclideanSpace.basisFun ι ℝ) i) =
            deriv a ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ))

      theorem fderiv_deriv_radial_comp_basisFun_off_origin
          {ι : Type*} [Fintype ι]
          {a : ℝ -> ℂ} {x : EuclideanSpace ℝ ι}
          (hx : x ≠ 0)
          (hda : DifferentiableAt ℝ (deriv a) ‖x‖) (i : ι) :
          fderiv ℝ
              (fun y : EuclideanSpace ℝ ι => deriv a ‖y‖) x
              ((EuclideanSpace.basisFun ι ℝ) i) =
            deriv (deriv a) ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ))

      theorem fderiv_radial_chain_product_basisFun
          {ι : Type*} [Fintype ι]
          {a : ℝ -> ℂ} {x : EuclideanSpace ℝ ι}
          (hx : x ≠ 0)
          (hda : DifferentiableAt ℝ (deriv a) ‖x‖) (i : ι) :
          fderiv ℝ (fun y : EuclideanSpace ℝ ι =>
              deriv a ‖y‖ * (((y i / ‖y‖ : ℝ) : ℂ))) x
              ((EuclideanSpace.basisFun ι ℝ) i) =
            deriv (deriv a) ‖x‖ *
                (((x i / ‖x‖ : ℝ) : ℂ)^2) +
              deriv a ‖x‖ *
                (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))

      theorem iteratedFDeriv_radial_comp_basisFun_basisFun
          {ι : Type*} [Fintype ι]
          {a : ℝ -> ℂ} {x : EuclideanSpace ℝ ι}
          (hx : x ≠ 0) (ha : ContDiffAt ℝ 2 a ‖x‖) (i : ι) :
          iteratedFDeriv ℝ 2
              (fun y : EuclideanSpace ℝ ι => a ‖y‖) x
              ![(EuclideanSpace.basisFun ι ℝ) i,
                (EuclideanSpace.basisFun ι ℝ) i] =
            deriv (deriv a) ‖x‖ *
                (((x i / ‖x‖ : ℝ) : ℂ)^2) +
              deriv a ‖x‖ *
                (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))
      ```

      Proof transcript: obtain `hasFDerivAt_norm_off_origin` by composing
      `hasStrictFDerivAt_norm_sq` with `Real.sqrt` on a neighborhood where
      `‖y‖^2` stays positive.  The coordinate first derivative follows by
      applying the Frechet derivative to `basisFun i` and using
      `EuclideanSpace.basisFun_inner`.  For the second derivative, rewrite
      the first coordinate derivative locally as
      `fun y => inner ℝ y (basisFun i) / ‖y‖`; differentiate in the same
      coordinate using the product/inverse rule and the already proved first
      derivative of the norm.  The checked product-rule lemma
      `fderiv_radial_chain_product_basisFun` proves the algebraic body of the
      radial second chain rule once the first derivative has been locally
      rewritten as `deriv a ‖y‖ * ((y i / ‖y‖ : ℝ) : ℂ)`.

      The checked bridge for
      `iteratedFDeriv_radial_comp_basisFun_basisFun` is:

      ```lean
      theorem eventually_fderiv_radial_comp_basisFun_eq
          {ι : Type*} [Fintype ι]
          {a : ℝ -> ℂ} {x : EuclideanSpace ℝ ι}
          (hx : x ≠ 0) (ha : ContDiffAt ℝ 2 a ‖x‖) (i : ι) :
          (fun y : EuclideanSpace ℝ ι =>
              fderiv ℝ
                (fun z : EuclideanSpace ℝ ι => a ‖z‖) y
                ((EuclideanSpace.basisFun ι ℝ) i)) =ᶠ[𝓝 x]
            (fun y : EuclideanSpace ℝ ι =>
              deriv a ‖y‖ * (((y i / ‖y‖ : ℝ) : ℂ)))
      ```

      Proof transcript: use `hx` to restrict to `y ≠ 0`; use
      `ha.eventually` and continuity of `norm` to ensure
      `DifferentiableAt ℝ a ‖y‖` on a neighborhood of `x`.  At each such `y`,
      apply the checked `fderiv_radial_comp_basisFun_off_origin`.  The
      differentiability input for `deriv a` in
      `fderiv_radial_chain_product_basisFun` comes from `ha.fderiv_right` /
      `ContDiffAt.differentiableAt` together with the one-dimensional identity
      between `fderiv` and `deriv`.  Then `Filter.EventuallyEq.fderiv_eq`, the
      checked product-rule lemma, the evaluation-map chain rule for
      `L ↦ L (basisFun i)`, and `iteratedFDeriv_two_apply` give the radial
      composition theorem.  This is the one-variable second chain rule with
      `ρ = fun y => ‖y‖`: the `a''(ρ x) * (Dρ[e_i])^2` term plus the
      `a'(ρ x) * D^2ρ[e_i,e_i]` term.  This is now checked in
      `EuclideanWeylPoisson.lean`.

      The checked final off-origin theorem is the trace/summation step:

      ```lean
      theorem laplacian_radialProfile_off_origin
          {ι : Type*} [Fintype ι]
          {N : ℕ} (hN : N = Fintype.card ι)
          {a : ℝ -> ℂ} {x : EuclideanSpace ℝ ι}
          (hx : x ≠ 0) (ha : ContDiffAt ℝ 2 a ‖x‖) :
          Laplacian.laplacian
              (fun y : EuclideanSpace ℝ ι => a ‖y‖) x =
            radialProfileLaplacian N a ‖x‖ := by
        calc
          Laplacian.laplacian (fun y => a ‖y‖) x
              = ∑ i : ι,
                  iteratedFDeriv ℝ 2 (fun y => a ‖y‖) x
                    ![(EuclideanSpace.basisFun ι ℝ) i,
                      (EuclideanSpace.basisFun ι ℝ) i] := by
                exact congrFun
                  (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
                    (fun y => a ‖y‖) (EuclideanSpace.basisFun ι ℝ)) x
          _ = ∑ i : ι,
                (deriv (deriv a) ‖x‖ *
                    (((x i / ‖x‖ : ℝ) : ℂ)^2) +
                  deriv a ‖x‖ *
                    (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [iteratedFDeriv_radial_comp_basisFun_basisFun hx ha i]
          _ = deriv (deriv a) ‖x‖ *
                  (∑ i : ι, (((x i / ‖x‖ : ℝ) : ℂ)^2)) +
                deriv a ‖x‖ *
                  (∑ i : ι,
                    (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))) := by
                rw [Finset.sum_add_distrib]
                rw [← Finset.mul_sum, ← Finset.mul_sum]
          _ = radialProfileLaplacian N a ‖x‖ := by
                rw [sum_complex_coord_sq_div_norm_sq_eq_one hx,
                    sum_complex_radial_norm_hessian_coeff hx]
                subst N
                rw [← nat_cast_card_sub_one_of_ne_zero hx]
                simp [radialProfileLaplacian, mul_comm]
      ```

   The positive-half-line regularity and all-points assembly are also checked:

   ```lean
   theorem contDiffOn_radialPrimitiveDeriv_of_smooth
       {N : ℕ} {F : ℝ -> ℂ} (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F) :
       ContDiffOn ℝ 1 (radialPrimitiveDeriv N F) (Set.Ioi 0)

   theorem contDiffOn_radialPrimitiveProfile_of_pos
       {N : ℕ} {F : ℝ -> ℂ} {R : ℝ}
       (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F) (hRpos : 0 < R) :
       ContDiffOn ℝ 2
         (fun r : ℝ => radialPrimitiveProfile N F R r) (Set.Ioi 0)
   ```

   `contDiffOn_radialPrimitiveDeriv_of_smooth` uses the honest positive-line
   formula
   `radialPrimitiveDeriv N F r =
   (((r^(N-1) : ℝ) : ℂ)⁻¹) * radialMass N F r`, proves `radialMass` is `C^1`
   from `hasDerivAt_radialMass` plus the continuous integrand
   `((r^(N-1) : ℝ) : ℂ) * F r`, and inverts the nonzero power on `Ioi 0`.
   `contDiffOn_radialPrimitiveProfile_of_pos` then applies
   `contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi`, the checked FTC theorem
   `hasDerivAt_radialPrimitiveProfile_of_pos`, and the derivative congruence
   `deriv_radialPrimitiveProfile_of_pos`.

   The checked all-points assembly is:

   ```lean
   theorem laplacian_radialPrimitiveProfile
       {ι : Type*} [Fintype ι]
       {N : ℕ} (hN : N = Fintype.card ι) (hNpos : 0 < N)
       {F : ℝ -> ℂ} {R η : ℝ} {c : ℂ}
       (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
       (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
       (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c) :
       ∀ x : EuclideanSpace ℝ ι,
         Laplacian.laplacian
           (fun y : EuclideanSpace ℝ ι =>
             radialPrimitiveProfile N F R ‖y‖) x = F ‖x‖
   ```

   Its proof is `by_cases hx : x = 0`.  At `x = 0`, use
   `laplacian_radialPrimitiveProfile_norm_zero hN hNpos hη hηR ...` and
   `hF_zero 0 ⟨le_rfl, hη.le⟩`.  At `x ≠ 0`, use
   `laplacian_radialProfile_off_origin` with
   `a = fun r => radialPrimitiveProfile N F R r`, then rewrite the scalar
   profile Laplacian by
   `radialProfileLaplacian_radialPrimitiveProfile_of_pos_of_R_pos hNpos
   hF_smooth.continuous hRpos ‖x‖ (norm_pos_iff.mpr hx)`.
   The `ha : ContDiffAt ℝ 2 a ‖x‖` input for the off-origin lemma is obtained
   by applying `contDiffOn_radialPrimitiveProfile_of_pos` and
   `Ioi_mem_nhds (norm_pos_iff.mpr hx)`.  For the final Schwartz primitive,
   combine this all-points Poisson theorem with the outside-support constancy
   theorem and the existing compact-bump hypotheses to package the profile as a
   compactly supported `SchwartzMap`.

   The scale-invariance consumer also needed one translation-commutation lemma
   for the Laplacian of a reflected translate.  This calculus identity is now
   checked:

   ```lean
   theorem lineDerivOp_euclideanReflectedTranslate
       {ι : Type*} [Fintype ι]
       (x v : EuclideanSpace ℝ ι)
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       (∂_{v} (euclideanReflectedTranslate x φ) :
         SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
       euclideanReflectedTranslate x
         (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)

   theorem laplacianCLM_euclideanReflectedTranslate
       {ι : Type*} [Fintype ι]
       (x : EuclideanSpace ℝ ι)
       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
       LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
           (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
           (euclideanReflectedTranslate x φ) =
         euclideanReflectedTranslate x
           (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
             (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ)
   ```

	   From this primitive theorem, the local scale invariance of a harmonic
	   distribution is now checked.  This is the last Weyl-scale step before
	   defining local representatives.  The support condition is exactly why the
	   primitive theorem has the strengthened radius output: if
	   `tsupport A ⊆ closedBall 0 (max ε δ)` and
	   `closedBall x (max ε δ) ⊆ V`, then
	   `supportsInOpen_euclideanReflectedTranslate_of_kernelSupport` proves the
	   translated test is supported in `V`.

	   ```lean
	   theorem regularizedDistribution_bump_scale_eq
	       {ι : Type*} [Fintype ι] [Nonempty ι]
	       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
	       {V : Set (EuclideanSpace ℝ ι)}
	       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0)
       {x : EuclideanSpace ℝ ι} {ε δ : ℝ}
       (hε : 0 < ε) (hδ : 0 < δ)
       (hxε : Metric.closedBall x ε ⊆ V)
       (hxδ : Metric.closedBall x δ ⊆ V) :
	       T (euclideanReflectedTranslate x (euclideanWeylBump ε hε)) =
	       T (euclideanReflectedTranslate x (euclideanWeylBump δ hδ))
	   ```

	   Lean-ready proof transcript:

	   ```lean
	   rcases exists_compact_laplacian_eq_euclideanWeylBump_sub_with_support
	       (ι := ι) hε hδ with
	     ⟨A, hAcompact, hAsupp, hAlap⟩
	   have hxR : Metric.closedBall x (max ε δ) ⊆ V := by
	     intro y hy
	     by_cases hδε : δ ≤ ε
	     · apply hxε
	       simpa [max_eq_left hδε] using hy
	     · have hεδ : ε ≤ δ := le_of_lt (lt_of_not_ge hδε)
	       apply hxδ
	       simpa [max_eq_right hεδ] using hy
	   have hAsuppV :
	       SupportsInOpen
	         (euclideanReflectedTranslate x A : EuclideanSpace ℝ ι -> ℂ) V :=
	     supportsInOpen_euclideanReflectedTranslate_of_kernelSupport hxR hAsupp
	   have hzero := hΔ (euclideanReflectedTranslate x A) hAsuppV
	   rw [laplacianCLM_euclideanReflectedTranslate, hAlap] at hzero
	   have htranslate_sub :
	       euclideanReflectedTranslate x
	           (euclideanWeylBump ε hε - euclideanWeylBump δ hδ) =
	         euclideanReflectedTranslate x (euclideanWeylBump ε hε) -
	           euclideanReflectedTranslate x (euclideanWeylBump δ hδ) := by
	     simp [euclideanReflectedTranslate]
	   rw [htranslate_sub] at hzero
	   rw [map_sub] at hzero
	   exact sub_eq_zero.mp hzero
	   ```

	   This proof uses only the checked Poisson primitive, the checked reflected
	   translate support theorem, and the checked Laplacian-translation
	   commutation.  It does not add a new harmonic-analysis axiom and does not
	   change the OS-II route.

	   The next checked stage now lives in the companion file
	   `SCV/EuclideanWeylRegularity.lean`, importing
	   `SCV/EuclideanWeylPoisson.lean`, rather than continuing to grow the
	   already-large Poisson file.  It defines the local ball representative and
	   proves its smoothness on smaller balls.  The two checked metric support
	   lemmas are:

	   ```lean
	   theorem closedBall_subset_ball_of_half_margin
	       {ι : Type*} [Fintype ι]
	       {c x : EuclideanSpace ℝ ι} {R : ℝ}
	       (hx : x ∈ Metric.ball c R) :
	       Metric.closedBall x ((R - dist x c) / 2) ⊆ Metric.ball c R := by
	     intro y hy
	     rw [Metric.mem_ball] at hx ⊢
	     have hyx : dist y x ≤ (R - dist x c) / 2 := by
	       simpa [Metric.mem_closedBall] using hy
	     have hyc : dist y c ≤ dist y x + dist x c := dist_triangle y x c
	     have hlt : dist y x + dist x c < R := by
	       nlinarith
	     exact lt_of_le_of_lt hyc hlt

	   theorem closedBall_subset_ball_of_uniform_margin
	       {ι : Type*} [Fintype ι]
	       {c x : EuclideanSpace ℝ ι} {r R ε : ℝ}
	       (hx : x ∈ Metric.ball c r)
	       (hεR : ε + r < R) :
	       Metric.closedBall x ε ⊆ Metric.ball c R := by
	     intro y hy
	     rw [Metric.mem_ball] at hx ⊢
	     have hyx : dist y x ≤ ε := by
	       simpa [Metric.mem_closedBall] using hy
	     have hyc : dist y c ≤ dist y x + dist x c := dist_triangle y x c
	     have hlt : dist y x + dist x c < R := by
	       nlinarith
	     exact lt_of_le_of_lt hyc hlt

	   noncomputable def euclideanWeylBallRepresentative
	       {ι : Type*} [Fintype ι]
	       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
	       (c : EuclideanSpace ℝ ι) (R : ℝ)
	       (x : EuclideanSpace ℝ ι) : ℂ :=
	     by
	       classical
	       exact
	         if hx : x ∈ Metric.ball c R then
	           let ε := (R - dist x c) / 2
	           have hε : 0 < ε := by
	             dsimp [ε]
	             rw [Metric.mem_ball] at hx
	             linarith
	           T (euclideanReflectedTranslate x
	             (euclideanWeylBump ε hε))
	         else 0

	   theorem euclideanWeylBallRepresentative_eq_regularized
	       {ι : Type*} [Fintype ι] [Nonempty ι]
	       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
	       {c : EuclideanSpace ℝ ι} {R ε : ℝ}
	       (hΔ :
	         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ)
	             (Metric.ball c R) ->
	             T
	               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0)
	       {x : EuclideanSpace ℝ ι}
	       (hε : 0 < ε)
	       (hxε : Metric.closedBall x ε ⊆ Metric.ball c R) :
	         euclideanWeylBallRepresentative T c R x =
	           T (euclideanReflectedTranslate x (euclideanWeylBump ε hε))

	   theorem euclideanWeylBallRepresentative_eq_regularized_on_ball
	       {ι : Type*} [Fintype ι] [Nonempty ι]
	       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
	       {c : EuclideanSpace ℝ ι} {r R ε : ℝ}
	       (hε : 0 < ε)
	       (hεR : ε + r < R)
	       (hΔ :
	         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ)
	             (Metric.ball c R) ->
	             T
	               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
	       ∀ x ∈ Metric.ball c r,
	         euclideanWeylBallRepresentative T c R x =
	           T (euclideanReflectedTranslate x (euclideanWeylBump ε hε))

	   theorem contDiffOn_euclideanWeylBallRepresentative
	       {ι : Type*} [Fintype ι] [Nonempty ι]
	       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
	       {c : EuclideanSpace ℝ ι} {r R ε : ℝ}
	       (hε : 0 < ε)
	       (hεR : ε + r < R)
	       (hΔ :
	         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ)
	             (Metric.ball c R) ->
	             T
	               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
	       ContDiffOn ℝ (⊤ : ℕ∞)
	         (euclideanWeylBallRepresentative T c R) (Metric.ball c r)
	   ```

	   Production status: all six declarations in this local representative
	   package are checked in `SCV/EuclideanWeylRegularity.lean`.

	   Proof transcript:

	   * In `euclideanWeylBallRepresentative_eq_regularized`, first derive
	     `hx : x ∈ ball c R` from the fixed-radius support hypothesis by applying
	     it to `x ∈ closedBall x ε`.  Unfold the representative and rewrite the
	     dependent `if` by `rw [dif_pos hx]`.  Then apply
	     `regularizedDistribution_bump_scale_eq` with
	     `closedBall_subset_ball_of_half_margin hx` for the definition's
	     variable radius and `hxε` for the fixed radius.
	   * The `_on_ball` theorem is the pointwise theorem plus
	     `closedBall_subset_ball_of_uniform_margin hx hεR`.
	   * For `contDiffOn_euclideanWeylBallRepresentative`, obtain
	     `hreg := contDiff_regularizedDistribution T (euclideanWeylBump ε hε)`,
	     then use `hreg.contDiffOn.congr` and the `_on_ball` equality.  This is
	     the first genuinely smooth representative theorem; it is not the final
	     distribution-representation theorem, which still needs the convolution
	     and approximate-identity step below.

	   Finally prove representation on the smaller ball by approximate identity.
	   Lean route correction: do **not** write
	   `∫ x, φ x • euclideanReflectedTranslate x ρ` as a Bochner integral with
	   values in `SchwartzMap`; in the current Mathlib API `SchwartzMap` has the
	   complete locally convex topology needed for continuity, but it is not a
	   `NormedAddCommGroup`, so the ordinary Bochner integral theorem
	   `ContinuousLinearMap.integral_comp_comm` does not apply.  The honest Lean
	   route is to define the test by Mathlib's Schwartz convolution and then
	   prove the scalar pairing identity as its own functional-analytic lemma.

	   ```lean
	   -- Checked in `SCV/EuclideanWeylRegularity.lean`.
	   noncomputable def euclideanConvolutionTest
	       {ι : Type*} [Fintype ι]
	       (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
	       SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
	     SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) φ ρ

	   theorem euclideanConvolutionTest_apply
	       {ι : Type*} [Fintype ι]
	       (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	       (x : EuclideanSpace ℝ ι) :
	       euclideanConvolutionTest φ ρ x =
	         ∫ y : EuclideanSpace ℝ ι, φ y * ρ (x - y)

	   theorem euclideanConvolutionTest_apply_reflected
	       {ι : Type*} [Fintype ι]
	       (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	       (x : EuclideanSpace ℝ ι) :
	       euclideanConvolutionTest φ ρ x =
	         ∫ y : EuclideanSpace ℝ ι, ρ (x - y) * φ y

	   theorem euclideanConvolutionTest_apply_reflectedTranslate
	       {ι : Type*} [Fintype ι]
	       (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	       (y : EuclideanSpace ℝ ι) :
	       euclideanConvolutionTest φ ρ y =
	         ∫ x : EuclideanSpace ℝ ι,
	           euclideanReflectedTranslate x ρ y * φ x

	   theorem regularizedDistribution_integral_pairing
	       {ι : Type*} [Fintype ι]
	       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
	       (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	       (hρ_compact : HasCompactSupport
	         (ρ : EuclideanSpace ℝ ι -> ℂ))
	       (hφ_compact : HasCompactSupport
	         (φ : EuclideanSpace ℝ ι -> ℂ)) :
	       ∫ x : EuclideanSpace ℝ ι,
	         T (euclideanReflectedTranslate x ρ) * φ x =
	         T (euclideanConvolutionTest φ ρ)

	   theorem tendsto_euclideanConvolutionTest_of_shrinking_normalized_support
	       {ι : Type*} [Fintype ι]
	       (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	       (ρn : ℕ -> SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	       (hρ_nonneg : ∀ n x, 0 ≤ (ρn n x).re)
	       (hρ_real : ∀ n x, (ρn n x).im = 0)
	       (hρ_norm : ∀ n, ∫ x, ρn n x = 1)
	       (hρ_support : ∀ n,
	         tsupport (ρn n : EuclideanSpace ℝ ι -> ℂ) ⊆
	           Metric.closedBall 0 (1 / (n + 1 : ℝ))) :
	       Tendsto (fun n => euclideanConvolutionTest φ (ρn n))
	         atTop (𝓝 φ)

	   theorem exists_euclideanConvolutionTest_approxIdentity
	       {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r) :
	       ∃ ρn : ℕ -> SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	         (∀ n, ∫ x, ρn n x = 1) ∧
	         (∀ n,
	           tsupport (ρn n : EuclideanSpace ℝ ι -> ℂ) ⊆
	             Metric.closedBall 0 (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
	         (∀ n,
	           tsupport (ρn n : EuclideanSpace ℝ ι -> ℂ) ⊆
	             Metric.closedBall 0 r) ∧
	         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	           Tendsto (fun n => euclideanConvolutionTest φ (ρn n))
	             atTop (𝓝 φ)

	   theorem integral_pairing_congr_of_eq_on_tsupport
	       {ι : Type*} [Fintype ι]
	       {φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ}
	       {H G : EuclideanSpace ℝ ι -> ℂ}
	       (hHG : ∀ x ∈ tsupport (φ : EuclideanSpace ℝ ι -> ℂ),
	         H x = G x) :
	       (∫ x, H x * φ x) = ∫ x, G x * φ x

	   theorem euclidean_laplacian_distribution_regular_on_ball
	       {ι : Type*} [Fintype ι] [Nonempty ι]
	       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
	       (c : EuclideanSpace ℝ ι) {r R : ℝ}
	       (hr : 0 < r) (hrR : r < R)
	       (hΔ :
	         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ)
	             (Metric.ball c R) ->
	             T
	               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
	       ∃ H : EuclideanSpace ℝ ι -> ℂ,
	         ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball c r) ∧
	         RepresentsEuclideanDistributionOn T H (Metric.ball c r)
	   ```

	   Proof obligations for this representation stage:

	   * The `euclideanConvolutionTest` surface is checked.  It imports
	     `Mathlib.Analysis.Fourier.Convolution`, defines Mathlib convolution
	     `(φ * ρ)(x) = ∫ y, φ y * ρ (x - y)`, and proves the reflected-translate
	     formula
	     `(φ * ρ)(y) = ∫ x, euclideanReflectedTranslate x ρ y * φ x`.
	     This is the sign convention needed for the scalar pairing identity.
	   * `regularizedDistribution_integral_pairing` is the genuine
	     functional-analytic step.  It says the scalar function
	     `x ↦ T (euclideanReflectedTranslate x ρ)` is exactly the distributional
	     convolution of `T` with a compactly supported regularizing kernel `ρ`,
	     paired against compactly supported `φ`.  This is **not** a wrapper and
	     should not be hidden behind an unsupported Bochner integral into
	     `SchwartzMap`.  The compact-kernel hypothesis is the one needed by the
	     Weyl route because the consumers use the checked normalized compact
	     Euclidean bumps.

	     The Lean route should use the same finite-probe idea already used in
	     `SCV/PaleyWiener.lean` for its `paley_wiener_half_line` boundary-value
	     identity.  For a continuous Schwartz functional `T`, first factor `T`
	     through finitely many weighted coordinate-line-derivative probes landing
	     in a Banach product of bounded continuous functions:

	     ```lean
	     noncomputable def euclideanWeightedLineDerivToBCFCLM
	         {ι : Type*} [Fintype ι]
	         (k n : ℕ) (u : Fin n -> ι) :
	         SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
	           EuclideanSpace ℝ ι ->ᵇ ℂ

	     noncomputable def euclideanProbeCLM
	         {ι : Type*} [Fintype ι]
	         (s : Finset (ℕ × ℕ)) :
	         SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
	           ((p : s.attach) ->
	             (Fin p.1.2 -> ι) -> EuclideanSpace ℝ ι ->ᵇ ℂ)

	     theorem euclideanSchwartzFunctional_exists_probe_factorization
	         {ι : Type*} [Fintype ι]
	         (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ) :
	         ∃ s : Finset (ℕ × ℕ),
	         ∃ G :
	           (((p : s.attach) ->
	             (Fin p.1.2 -> ι) -> EuclideanSpace ℝ ι ->ᵇ ℂ) ->L[ℂ] ℂ),
	           T = G.comp (euclideanProbeCLM s)
	     ```

	     The implementation starts with the concrete probe substrate, not with
	     an abstract "finite family of seminorms" placeholder.  The first slice
	     is checked in the small companion
	     `SCV/EuclideanWeylProbe.lean`, importing
	     `SCV/EuclideanWeylRegularity.lean`:

	     ```lean
	     noncomputable def euclideanPolynomialWeight
	         {ι : Type*} [Fintype ι]
	         (k : ℕ) (x : EuclideanSpace ℝ ι) : ℂ :=
	       (((1 : ℝ) + ‖x‖ ^ 2) ^ k : ℝ)

	     theorem euclideanPolynomialWeight_hasTemperateGrowth
	         {ι : Type*} [Fintype ι]
	         (k : ℕ) :
	         (euclideanPolynomialWeight (ι := ι) k).HasTemperateGrowth

	     noncomputable def euclideanCoordinateDirs
	         {ι : Type*} [Fintype ι] {n : ℕ} (u : Fin n -> ι) :
	         Fin n -> EuclideanSpace ℝ ι :=
	       fun j => EuclideanSpace.basisFun ι ℝ (u j)

	     noncomputable def euclideanIteratedCoordinateLineDerivCLM
	         {ι : Type*} [Fintype ι] :
	         (n : ℕ) -> (Fin n -> ι) ->
	           SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
	             SchwartzMap (EuclideanSpace ℝ ι) ℂ

	     theorem euclideanIteratedCoordinateLineDerivCLM_apply
	         {ι : Type*} [Fintype ι] {n : ℕ}
	         (u : Fin n -> ι)
	         (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
	         euclideanIteratedCoordinateLineDerivCLM n u f =
	           ∂^{euclideanCoordinateDirs u} f

	     noncomputable def euclideanWeightedLineDerivToBCFCLM
	         {ι : Type*} [Fintype ι]
	         (k n : ℕ) (u : Fin n -> ι) :
	         SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
	           BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ

	     theorem euclideanWeightedLineDerivToBCFCLM_apply
	         {ι : Type*} [Fintype ι]
	         (k n : ℕ) (u : Fin n -> ι)
	         (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	         (x : EuclideanSpace ℝ ι) :
	         euclideanWeightedLineDerivToBCFCLM k n u f x =
	           euclideanPolynomialWeight k x *
	             (∂^{euclideanCoordinateDirs u} f) x

	     noncomputable abbrev EuclideanProbeSpace
	         {ι : Type*} [Fintype ι] (s : Finset (ℕ × ℕ)) :=
	       (p : ↑s.attach) ->
	         (Fin p.1.1.2 -> ι) ->
	           BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ

	     noncomputable def euclideanProbeCLM
	         {ι : Type*} [Fintype ι]
	         (s : Finset (ℕ × ℕ)) :
	         SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ]
	           EuclideanProbeSpace (ι := ι) s

	     theorem euclideanProbeCLM_apply
	         {ι : Type*} [Fintype ι]
	         (s : Finset (ℕ × ℕ))
	         (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	         (p : ↑s.attach) (u : Fin p.1.1.2 -> ι)
	         (x : EuclideanSpace ℝ ι) :
	         euclideanProbeCLM s f p u x =
	           euclideanPolynomialWeight p.1.1.1 x *
	             (∂^{euclideanCoordinateDirs u} f) x
	     ```

	     The implementation details are already fixed by existing APIs:
	     `euclideanPolynomialWeight_hasTemperateGrowth` is `fun_prop` after
	     unfolding; the line-derivative CLM is recursive, using
	     `LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	     (EuclideanSpace.basisFun ι ℝ (u 0))` and `Fin.tail`; the apply theorem
	     rewrites by `LineDeriv.iteratedLineDerivOp_succ_left`; the weighted BCF
	     map is
	     `SchwartzMap.toBoundedContinuousFunctionCLM.comp
	     (SchwartzMap.smulLeftCLM.comp
	     euclideanIteratedCoordinateLineDerivCLM)`; and the finite probe map is
	     `ContinuousLinearMap.pi` twice.

	     The nontrivial domination lemma behind the later factorization is
	     finite dimensional, not distributional: full `iteratedFDeriv` seminorms
	     are controlled by finitely many coordinate line-derivative probes in the
	     orthonormal basis `EuclideanSpace.basisFun ι ℝ`.  It must not be hidden
	     inside the factorization theorem.  State it explicitly:

	     ```lean
	     theorem euclideanContinuousMultilinearMap_norm_le_coordinate_sum
	         {ι : Type*} [Fintype ι] (n : ℕ)
	         (A : (EuclideanSpace ℝ ι) [×n]→L[ℝ] ℂ) :
	         ‖A‖ ≤
	           Finset.univ.sum
	             (fun u : Fin n -> ι =>
	               ‖A (euclideanCoordinateDirs u)‖)

	     theorem euclideanSchwartzSeminorm_le_coordinateProbeNorm
	         {ι : Type*} [Fintype ι]
	         (k n : ℕ)
	         (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
	         SchwartzMap.seminorm ℝ k n f ≤
	           Finset.univ.sum
	             (fun u : Fin n -> ι =>
	               ‖euclideanWeightedLineDerivToBCFCLM k n u f‖)
	     ```

	     Proof transcript for
	     `euclideanContinuousMultilinearMap_norm_le_coordinate_sum`: expand
	     each input vector in the orthonormal basis by
	     `(EuclideanSpace.basisFun ι ℝ).sum_repr`, use multilinearity to expand
	     `A v` as a finite sum over `u : Fin n -> ι`, bound
	     `‖v j (u j)‖ ≤ ‖v j‖`, then apply
	     `ContinuousMultilinearMap.opNorm_le_bound`.  The exact constant is
	     checked as `1`, so no hidden finite-dimensional norm-equivalence
	     constant is being used.  Then
	     `euclideanSchwartzSeminorm_le_coordinateProbeNorm` follows by
	     `SchwartzMap.seminorm_le_bound`, rewriting coordinate values with
	     `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv` and
	     `euclideanWeightedLineDerivToBCFCLM_apply`, and absorbing the harmless
	     inequality `‖x‖ ^ k ≤ ‖euclideanPolynomialWeight k x‖`.
	     Both domination theorems are checked in `SCV/EuclideanWeylProbe.lean`.

	     The Hahn-Banach factorization stage is now checked in the same small
	     file, following the checked
	     `SCV/PaleyWiener.lean` pattern with the Euclidean coordinate-probe
	     domination theorem replacing the one-dimensional probe bound:

	     ```lean
	     theorem euclideanSchwartzFunctional_bound
	         {ι : Type*} [Fintype ι]
	         (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ) :
	         ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
	           ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	             ‖T φ‖ ≤
	               (C • s.sup
	                 (schwartzSeminormFamily ℂ
	                   (EuclideanSpace ℝ ι) ℂ)) φ

	     theorem euclideanSchwartzSeminorm_le_probeNorm
	         {ι : Type*} [Fintype ι]
	         (s : Finset (ℕ × ℕ)) (p : ↑s.attach)
	         (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
	         SchwartzMap.seminorm ℝ p.1.1.1 p.1.1.2 f ≤
	           Fintype.card (Fin p.1.1.2 -> ι) *
	             ‖(euclideanProbeCLM s f :
	               EuclideanProbeSpace (ι := ι) s)‖

	     theorem euclideanSchwartzFunctional_bound_by_probeNorm
	         {ι : Type*} [Fintype ι]
	         (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ) :
	         ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
	           ∀ f : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	             ‖T f‖ ≤
	               C * ‖(euclideanProbeCLM s f :
	                 EuclideanProbeSpace (ι := ι) s)‖

	     theorem euclideanSchwartzFunctional_exists_probe_factorization
	         {ι : Type*} [Fintype ι]
	         (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ) :
	         ∃ s : Finset (ℕ × ℕ),
	         ∃ G : EuclideanProbeSpace (ι := ι) s ->L[ℂ] ℂ,
	           T = G.comp (euclideanProbeCLM s)
	     ```

	     Proof transcript:

	     1. Build the seminorm
	        `q := (normSeminorm ℂ ℂ).comp T.toLinearMap`; continuity is
	        `continuous_norm.comp T.continuous`, and
	        `Seminorm.bound_of_continuous
	          (schwartz_withSeminorms ℂ (EuclideanSpace ℝ ι) ℂ) q`
	        gives the finite family `s`.
	     2. For each attached index `p : s.attach`, apply the checked
	        `euclideanSchwartzSeminorm_le_coordinateProbeNorm` and bound every
	        component
	        `euclideanWeightedLineDerivToBCFCLM p.1.1.1 p.1.1.2 u f`
	        first by the `p`-fiber norm and then by the full Pi norm using
	        `norm_le_pi_norm`.  The finite coordinate count is exactly
	        `Fintype.card (Fin p.1.1.2 -> ι)`.
	     3. Sum these bounds over `s`, using
	        `Seminorm.finset_sup_le_sum`, to obtain a real constant
	        `C0 * ∑ p ∈ s, Fintype.card (Fin p.2 -> ι)`.
	     4. From the probe-norm bound, prove
	        `ker (euclideanProbeCLM s) ≤ ker T`: if the probe packet is zero,
	        the bound gives `‖T f‖ ≤ 0`, hence `T f = 0`.
	     5. Define the range functional by quotienting by the probe kernel:

	        ```lean
	        ((LinearMap.ker (euclideanProbeCLM s).toLinearMap).liftQ
	            T.toLinearMap hker).comp
	          ((euclideanProbeCLM s).toLinearMap
	            .quotKerEquivRange.symm.toLinearMap)
	        ```

	        The apply theorem is
	        `LinearMap.quotKerEquivRange_symm_apply_image`; the norm bound on
	        the range is the probe-norm bound rewritten on range representatives.
	     6. Turn the range functional into a `StrongDual` with
	        `LinearMap.mkContinuous`, extend it to the ambient Banach probe
	        space by `exists_extension_norm_eq`, and extensionality gives
	        `T = G.comp (euclideanProbeCLM s)`.

	     The factorization theorem and the scalar pairing theorem are now
	     checked.  The pairing is proved in the small companion
	     `SCV/EuclideanWeylPairing.lean` by factoring only through this Banach
	     probe space.  This is the exact replacement for the forbidden
	     `SchwartzMap`-valued Bochner integral:

	     ```lean
	     noncomputable def euclideanPairingProbeFamily
	         {ι : Type*} [Fintype ι]
	         (s : Finset (ℕ × ℕ))
	         (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	         (x : EuclideanSpace ℝ ι) :
	         ((p : s.attach) ->
	           (Fin p.1.2 -> ι) -> EuclideanSpace ℝ ι ->ᵇ ℂ) :=
	       euclideanProbeCLM s
	         (φ x • euclideanReflectedTranslate x ρ)

	     theorem integrable_euclideanPairingProbeFamily
	         {ι : Type*} [Fintype ι]
	         (s : Finset (ℕ × ℕ))
	         (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	         (hφ_compact : HasCompactSupport
	           (φ : EuclideanSpace ℝ ι -> ℂ))
	         (hρ_compact : HasCompactSupport
	           (ρ : EuclideanSpace ℝ ι -> ℂ)) :
	         Integrable (euclideanPairingProbeFamily s φ ρ)

	     theorem integral_euclideanPairingProbeFamily_eq_probe_convolution
	         {ι : Type*} [Fintype ι]
	         (s : Finset (ℕ × ℕ))
	         (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
	         (hφ_compact : HasCompactSupport
	           (φ : EuclideanSpace ℝ ι -> ℂ))
	         (hρ_compact : HasCompactSupport
	           (ρ : EuclideanSpace ℝ ι -> ℂ)) :
	         ∫ x : EuclideanSpace ℝ ι,
	             euclideanPairingProbeFamily s φ ρ x =
	           euclideanProbeCLM s (euclideanConvolutionTest φ ρ)
	     ```

	     Componentwise, the last theorem is the standard regularization
	     computation from Streater-Wightman §2-1:
	     `D^u(φ * ρ)(y) = ∫ x, φ x * D^uρ(y - x)`.  In Lean this is now checked
	     from `euclideanConvolutionTest_apply_reflectedTranslate`, ordinary
	     Banach-valued integral evaluation through Pi projections and
	     `BoundedContinuousFunction.evalCLM`, Fourier-transform injectivity on
	     Euclidean Schwartz space, and the derivative-through-convolution lemma
	     `iteratedLineDerivOp_euclideanConvolutionTest_right`.

	     The final proof transcript is then:

	     ```lean
	     obtain ⟨s, G, hTG⟩ :=
	       euclideanSchwartzFunctional_exists_probe_factorization T
	     have hT_apply :
	         ∀ f, T f = G (euclideanProbeCLM s f) := by
	       intro f; exact congrArg (fun L => L f) hTG
	     calc
	       ∫ x, T (euclideanReflectedTranslate x ρ) * φ x
	           = ∫ x, T (φ x • euclideanReflectedTranslate x ρ) := by
	             apply MeasureTheory.integral_congr_ae
	             filter_upwards with x
	             simp [map_smul, smul_eq_mul, mul_comm]
	       _ = ∫ x, G (euclideanPairingProbeFamily s φ ρ x) := by
	             apply MeasureTheory.integral_congr_ae
	             filter_upwards with x
	             rw [hT_apply]
	             rfl
	       _ = G (∫ x, euclideanPairingProbeFamily s φ ρ x) := by
	             exact G.integral_comp_comm
	               (integrable_euclideanPairingProbeFamily
	                 s φ ρ hφ_compact hρ_compact)
	       _ = G (euclideanProbeCLM s (euclideanConvolutionTest φ ρ)) := by
	             rw [integral_euclideanPairingProbeFamily_eq_probe_convolution]
	       _ = T (euclideanConvolutionTest φ ρ) := by
	             rw [hT_apply]
	     ```

	     This proves the exact scalar identity while keeping all actual integrals
	     Banach-valued or scalar-valued.
	     API-backed Gemini Deep Research interaction
	     `v1_ChdJRG51YWRtQUtvNm9fdU1QMkx1MmdRTRIXSURudWFkbUFLbzZvX3VNUDJMdTJnUU0`
	     completed on 2026-04-26 and sanity-checked this theorem shape: the
	     scalar pairing identity is true with the current reflected-translate
	     convention, no sign correction is needed, and the finite-probe /
	     ordinary-Bochner route is a mathematically faithful formal substitute
	     for the usual weak/Pettis regularization argument.  Its main warning is
	     the same one recorded above: the coordinate-probe domination,
	     derivative-under-the-integral, and compact-support integrability lemmas
	     must be proved explicitly rather than hidden behind a generalized
	     Schwartz-valued integral.
	   * `tendsto_euclideanConvolutionTest_of_shrinking_normalized_support` is
	     now checked in `SCV/EuclideanWeylApproxIdentity.lean`; the proved
	     theorem is slightly stronger than the consumer requirement and holds
	     for every Euclidean Schwartz test `φ`.  The proof is the Euclidean
	     analogue of
	     `tendsto_realConvolutionTest_of_shrinking_normalized_support`: first
	     prove the symmetric formula
	     `euclideanConvolutionTest_apply_swap`,
	     differentiate through convolution on the left by
	     `iteratedLineDerivOp_euclideanConvolutionTest_left`, prove the
	     CLM-valued difference formula
	     `iteratedFDeriv_euclideanConvolutionTest_sub_eq_integral`, prove the
	     weighted translation estimate
	     `exists_weighted_iteratedFDeriv_euclideanTranslate_sub_le_linear`, use
	     nonnegative real normalization to get
	     `∫ x, ‖ρn n x‖ = 1`, and then close every
	     `schwartz_withSeminorms` seminorm.  The compactness needed for the
	     CLM-valued Bochner integral comes from the kernel support hypothesis,
	     not from a `SchwartzMap`-valued integral shortcut.
	   * The checked constructor
	     `exists_euclideanConvolutionTest_approxIdentity` uses the explicit
	     normalized radial kernels `euclideanWeylBump` with radii
	     `min (r / 2) (1 / (n + 1))`; it exports normalization, the fixed-radius
	     support bound needed for ball margins, and the full Schwartz-topology
	     convergence theorem above.
	   * For a test `φ` supported in `ball c r`, choose `ε0 > 0` with
	     `ε0 + r < R`, and choose a shrinking normalized bump sequence with
	     support radius at most `ε0`.  On `tsupport φ`, scale invariance identifies
	     `euclideanWeylBallRepresentative T c R x` with
	     `T (euclideanReflectedTranslate x (ρn n))`; outside `tsupport φ`, the
	     factor `φ x` is zero.  Therefore
	     `∫ H x * φ x = T (euclideanConvolutionTest φ (ρn n))` for all `n`.
	     The approximate-identity theorem and continuity of `T` give
	     `T (euclideanConvolutionTest φ (ρn n)) -> T φ`, while the left side is
	     constant, so `T φ = ∫ H x * φ x`.  This proves the representation
	     identity.

	     Lean-ready transcript for the ball theorem:

	     ```lean
	     theorem euclidean_laplacian_distribution_regular_on_ball
	         {ι : Type*} [Fintype ι] [Nonempty ι]
	         (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
	         (c : EuclideanSpace ℝ ι) {r R : ℝ}
	         (hr : 0 < r) (hrR : r < R)
	         (hΔ :
	           ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
	             SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ)
	               (Metric.ball c R) ->
	               T
	                 (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
	                   (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
	         ∃ H : EuclideanSpace ℝ ι -> ℂ,
	           ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball c r) ∧
	           RepresentsEuclideanDistributionOn T H (Metric.ball c r) := by
	       let H := euclideanWeylBallRepresentative T c R
	       let η : ℝ := (R - r) / 2
	       have hη_pos : 0 < η := by linarith
	       have hηR : η + r < R := by linarith
	       have hH_smooth :
	           ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball c r) :=
	         contDiffOn_euclideanWeylBallRepresentative T hη_pos hηR hΔ
	       refine ⟨H, hH_smooth, ?_⟩
	       intro φ hφ
	       let εn : ℕ -> ℝ := fun n => min (η / 2) (1 / (n + 1 : ℝ))
	       have hεn_pos : ∀ n, 0 < εn n := ...
	       let ρn : ℕ -> SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
	         fun n => euclideanWeylBump (εn n) (hεn_pos n)
	       have happrox :
	           Tendsto (fun n => euclideanConvolutionTest φ (ρn n))
	             atTop (𝓝 φ) :=
	         tendsto_euclideanConvolutionTest_of_shrinking_normalized_support
	           φ ρn
	             (fun n x => euclideanWeylBump_nonneg_re (εn n) (hεn_pos n) x)
	             (fun n x => euclideanWeylBump_im_eq_zero (εn n) (hεn_pos n) x)
	             (fun n => euclideanWeylBump_normalized (εn n) (hεn_pos n))
	             (by
	               intro n
	               exact (euclideanWeylBump_support (εn n) (hεn_pos n)).trans
	                 (Metric.closedBall_subset_closedBall (min_le_right _ _)))
	       have hpair :
	           ∀ n,
	             (∫ x, H x * φ x) =
	               T (euclideanConvolutionTest φ (ρn n)) := by
	         intro n
	         have hρ_compact :
	             HasCompactSupport (ρn n : EuclideanSpace ℝ ι -> ℂ) := ...
	         have hH_eq :
	             ∀ x ∈ tsupport (φ : EuclideanSpace ℝ ι -> ℂ),
	               H x = T (euclideanReflectedTranslate x (ρn n)) := by
	           intro x hx
	           have hx_ball : x ∈ Metric.ball c r := hφ.2 hx
	           have hxε :
	               Metric.closedBall x (εn n) ⊆ Metric.ball c R :=
	             closedBall_subset_ball_of_uniform_margin hx_ball
	               (by have hε_le : εn n ≤ η := ...; linarith)
	           simpa [H, ρn] using
	             euclideanWeylBallRepresentative_eq_regularized
	               T hΔ (hεn_pos n) hxε
	         calc
	           (∫ x, H x * φ x) =
	               ∫ x, T (euclideanReflectedTranslate x (ρn n)) * φ x := by
	                 apply integral_congr_ae
	                 filter_upwards with x
	                 by_cases hx : x ∈ tsupport (φ : EuclideanSpace ℝ ι -> ℂ)
	                 · rw [hH_eq x hx]
	                 · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
	                   simp [hφx]
	           _ = T (euclideanConvolutionTest φ (ρn n)) :=
	                 regularizedDistribution_integral_pairing
	                   T (ρn n) φ hρ_compact hφ.1
	       have hTend :
	           Tendsto (fun n => T (euclideanConvolutionTest φ (ρn n)))
	             atTop (𝓝 (T φ)) :=
	         T.continuous.tendsto φ |>.comp happrox
	       have hconst :
	           Tendsto (fun _ : ℕ => ∫ x, H x * φ x)
	             atTop (𝓝 (T φ)) := by
	         simpa [hpair] using hTend
	       exact (tendsto_nhds_unique tendsto_const_nhds hconst).symm
	     ```

	     This ball theorem is now checked in
	     `SCV/EuclideanWeylRepresentation.lean` as
	     `euclidean_laplacian_distribution_regular_on_ball`.  The remaining
	     Weyl regularity target is the open-set assembly below: finite
	     partition of unity on `tsupport φ`, support preservation for the
	     localized products, overlap equality of local representatives, and
	     patching the ball representatives into one smooth representative on
	     `V`.

   The open-set theorem is a local assembly over balls.  The implementation
   should not introduce another Weyl lemma or a theorem-2 wrapper.  It should
   only assemble the checked ball theorem by canonical local patching and
   ordinary finite smooth partitions on compact test supports.

   ```lean
   theorem exists_finite_schwartz_partitionOfUnity_on_compact
       {ι : Type*} [Fintype ι]
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
       {K : Set E} (hK : IsCompact K)
       {U : ι -> Set E}
       (hU_open : ∀ i, IsOpen (U i))
       (hU_relcompact : ∀ i, ∃ c R, U i ⊆ Metric.closedBall c R)
       (hcover : K ⊆ ⋃ i, U i) :
       ∃ χ : ι -> SchwartzMap E ℂ,
         (∀ i, HasCompactSupport (χ i : E -> ℂ)) ∧
         (∀ i, tsupport (χ i : E -> ℂ) ⊆ U i) ∧
         (∀ x ∈ K, ∑ i, χ i x = 1)

   theorem supportsInOpen_partition_mul
       {χ φ : SchwartzMap E ℂ} {U V : Set E}
       (hχ : tsupport (χ : E -> ℂ) ⊆ U)
       (hφ : SupportsInOpen (φ : E -> ℂ) V) :
       SupportsInOpen
         ((SchwartzMap.smulLeftCLM ℂ (χ : E -> ℂ) φ) : E -> ℂ)
         (U ∩ V)

   theorem euclidean_weyl_laplacian_distribution_regular_on_open
       {ι : Type*} [Fintype ι] [DecidableEq ι]
       (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ ->L[ℂ] ℂ)
       {V : Set (EuclideanSpace ℝ ι)}
       (hV_open : IsOpen V)
       (hΔ :
         ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
           SupportsInOpen (φ : EuclideanSpace ℝ ι -> ℂ) V ->
             T
               (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
                 (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0) :
       ∃ H : EuclideanSpace ℝ ι -> ℂ,
         ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
         RepresentsEuclideanDistributionOn T H V
   ```

   The Lean route should be the following, in this order.

   **Canonical local representative.**

   For `x ∈ V`, choose a positive radius `R x` with

   ```lean
   Metric.closedBall x (R x) ⊆ V
   ```

   using `exists_pos_closedBall_subset_of_isOpen`, and define the global
   candidate by the canonical ball representative centered at the point:

   ```lean
   H x :=
     if hx : x ∈ V then euclideanWeylBallRepresentative T x (R ⟨x, hx⟩) x
       else 0
   ```

   The only choice here is the radius guaranteed by openness; the
   representative itself is the already checked canonical
   `euclideanWeylBallRepresentative`, not an arbitrary local witness.

   For any fixed `c ∈ V`, put `R0 := R c`.  On the smaller ball
   `Metric.ball c (R0 / 4)`, prove

   ```lean
   H y = euclideanWeylBallRepresentative T c R0 y
   ```

   by choosing a Weyl bump radius `ε` small enough that both
   `Metric.closedBall y ε ⊆ Metric.ball c R0` and
   `Metric.closedBall y ε ⊆ Metric.ball y (R y)` hold, then applying
   `euclideanWeylBallRepresentative_eq_regularized` to both centers.  This is
   the concrete overlap-patching lemma and avoids invoking distributional
   uniqueness for the smoothness proof.  Smoothness of `H` on `V` then follows
   locally from `contDiffOn_euclideanWeylBallRepresentative`.

   **Finite partitions only on test supports.**

   The partition of unity is needed only after a test `φ` is fixed.  Let
   `K := tsupport φ`; `hφ.1` gives `IsCompact K`, and `hφ.2` gives
   `K ⊆ V`.  Cover `K` by finitely many smaller balls

   ```lean
   U i := Metric.ball (c i) (r i)
   ```

   such that each `Metric.closedBall (c i) (2 * r i) ⊆ V` and the local
   equality

   ```lean
   ∀ y ∈ U i, H y = euclideanWeylBallRepresentative T (c i) (2 * r i) y
   ```

   is available.  Use Mathlib's
   `SmoothPartitionOfUnity.exists_isSubordinate` with `s = K` and this finite
   ball cover.  Because each `U i` is bounded, `tsupport (ρ i) ⊆ U i` implies
   compact support by containment in `Metric.closedBall (c i) (r i)`.
   Convert the real smooth partition functions to complex-valued Schwartz
   maps:

   ```lean
   ρχ i : SchwartzMap E ℂ
   hρχ_apply i x : ρχ i x = (ρ i x : ℂ)
   hρχ_support i : tsupport (ρχ i : E -> ℂ) ⊆ U i
   hpartition_on_K : ∀ x ∈ K, ∑ i, ρχ i x = 1
   ```

   Then the checked lemma
   `schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport` gives

   ```lean
   φ = ∑ i, SchwartzMap.smulLeftCLM ℂ (ρχ i : E -> ℂ) φ
   ```

   and `supportsInOpen_partition_mul_left` gives support of each localized
   test inside the corresponding ball `U i`.

   **Representation identity for a fixed test.**

   Apply the checked ball representation theorem to each `U i`, replace the
   local ball representative by `H` on the support of the localized test using
   the local equality above, sum the finitely many identities, and use
   linearity of `T` plus the finite partition decomposition of `φ`.

   The only analytic bookkeeping needed in the summation is the finite-integral
   passage; the local integrability part is now checked as

   ```lean
   theorem integrable_continuousOn_mul_schwartz_of_supportsInOpen
       {H : E -> ℂ} {ψ : SchwartzMap E ℂ} {U : Set E}
       (hU : IsOpen U)
       (hH : ContinuousOn H U)
       (hψ : SupportsInOpen (ψ : E -> ℂ) U) :
       Integrable fun x => H x * ψ x
   ```

   proved by extending `H * ψ` by zero outside `U`.  Since
   `tsupport ψ ⊆ U`, every point outside `U` has a neighborhood on which
   `ψ = 0`, while points in `U` use `hH`.  Compact support comes from
   `hψ.1`.

   With this finite-integral lemma in place, the open-set theorem is a direct
   proof with no new axiom and no theorem-level `sorry`.

   Production status in `SCV/EuclideanWeylOpen.lean`: the first open-assembly
   prerequisites are now checked.

   ```lean
   exists_pos_closedBall_subset_of_isOpen
   euclideanWeylOpenRadius
   euclideanWeylOpenRepresentative
   euclideanWeylOpenRepresentative_eq_ballRepresentative_on_small_ball
   contDiffOn_euclideanWeylOpenRepresentative
   supportsInOpen_partition_mul
   supportsInOpen_partition_mul_left
   exists_finite_schwartz_partitionOfUnity_on_compact
   schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
   integrable_continuousOn_mul_schwartz_of_supportsInOpen
   euclideanDistribution_representation_of_finite_partition_for_test
   euclidean_weyl_laplacian_distribution_regular_on_open
   ```

   `SCV/EuclideanWeylRepresentation.lean` also now exposes the
   non-existential canonical ball representation theorem:

   ```lean
   euclideanWeylBallRepresentative_represents_on_ball
   ```

   This closes the radius-selection, canonical-overlap/smoothness,
   support-preservation, finite compact partition, finite
   partition-decomposition, local compact-support integrability, finite
   summation, and the full open-set Euclidean Weyl representation theorem.
   The downstream complex-chart holomorphic regularity theorem
   `SCV.distributionalHolomorphic_regular` is now checked in
   `SCV/DistributionalEOWHolomorphic.lean`: after Weyl regularity gives a
   smooth representative, the file extracts the pointwise Cauchy-Riemann
   equations from distributional `∂bar` equations and converts real
   smoothness plus CR to complex differentiability.

   After Weyl regularity gives a smooth representative, recover the pointwise
   Cauchy-Riemann equations from the distributional equations.  The pointwise
   operator definition and its global-Schwartz compatibility lemma are now
   checked in `SCV/DistributionalEOWRegularity.lean`:

   ```lean
   def pointwiseDbar (j : Fin m) (H : ComplexChartSpace m -> ℂ)
       (z : ComplexChartSpace m) : ℂ :=
     (1 / 2 : ℂ) *
       (fderiv ℝ H z (complexRealDir j) +
        Complex.I * fderiv ℝ H z (complexImagDir j))

   theorem dbarSchwartzCLM_apply_eq_pointwiseDbar
       (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (z : ComplexChartSpace m) :
       (dbarSchwartzCLM j φ) z =
         pointwiseDbar j (φ : ComplexChartSpace m -> ℂ) z

   theorem pointwiseDbar_eq_zero_of_distributionalHolomorphic
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hCR : IsDistributionalHolomorphicOn Hdist U0)
       (H : ComplexChartSpace m -> ℂ)
       (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
       (hRep : RepresentsDistributionOnComplexDomain Hdist H U0) :
       ∀ j : Fin m, ∀ z ∈ U0, pointwiseDbar j H z = 0
   ```

   Proof transcript.  Fix `j` and a compactly supported Schwartz test `φ`
   supported in `U0`.  From `hRep` and `hCR`,
   ```
   0 = Hdist (dbarSchwartzCLM j φ)
     = ∫ z, H z * (dbarSchwartzCLM j φ) z.
   ```
   Choose a smooth compact cutoff equal to one near `tsupport φ`; multiplying
   it by the smooth representative `H` gives a global Schwartz representative
   on the support, and its `∂bar` equals the pointwise `∂bar H` on
   `tsupport φ`.  Apply the checked integration-by-parts theorem
   `integral_mul_dbarSchwartzCLM_right_eq_neg_left` to get
   ```
   ∫ z, pointwiseDbar j H z * φ z = 0.
   ```
   Since `pointwiseDbar j H` is continuous on `U0`, the pointwise extraction
   step should use the following local variant of the checked
   `DistributionalUniqueness.lean` fundamental lemma.  This is not a wrapper:
   it is the exact local distribution-theory statement needed because the Weyl
   representative is only known to be smooth on `U0`, not globally.

   ```lean
   theorem eq_zero_on_open_of_supportsInOpen_schwartz_integral_zero
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
       [IsLocallyFiniteMeasure (volume : Measure E)]
       [Measure.IsOpenPosMeasure (volume : Measure E)]
       {g : E -> ℂ} {U : Set E}
       (hU_open : IsOpen U)
       (hg : ContinuousOn g U)
       (hint : ∀ φ : SchwartzMap E ℂ,
         SupportsInOpen (φ : E -> ℂ) U ->
           ∫ x : E, g x * φ x = 0) :
       ∀ x ∈ U, g x = 0
   ```

   Lean transcript for this local fundamental lemma: fix `x ∈ U`; choose
   `χ : E -> ℝ` with `χ x = 1`, compact support, `tsupport χ ⊆ U`, and
   `χ` smooth, using `exists_contDiff_tsupport_subset`.  For every compactly
   supported Schwartz `φ`, apply `hint` to
   `SchwartzMap.smulLeftCLM ℂ (fun y => (χ y : ℂ)) φ`.  Its support lies in
   `U` because `tsupport χ ⊆ U`.  This proves
   `∫ ((χ y : ℂ) * g y) * φ y = 0` for every compactly supported Schwartz
   `φ`.  The product `(fun y => (χ y : ℂ) * g y)` is globally continuous:
   on `U` this is `χ * g`; outside `U` every boundary point has a neighborhood
   on which `χ = 0`, because `tsupport χ ⊆ U`.  Apply the already checked
   global/compact-support fundamental lemma pattern from
   `eq_zero_on_open_of_compactSupport_schwartz_integral_zero` to obtain
   `(χ x : ℂ) * g x = 0`, then use `χ x = 1`.

   With that lemma, the pointwise CR theorem becomes Lean-local:

   ```lean
   theorem continuousOn_pointwiseDbar_of_contDiffOn
       {H : ComplexChartSpace m -> ℂ} {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
       (j : Fin m) :
       ContinuousOn (pointwiseDbar j H) U0 := by
     -- use `hH_smooth.continuousOn_fderiv_of_isOpen hU0_open` and
     -- apply the continuous derivative field to the two fixed coordinate
     -- directions `complexRealDir j` and `complexImagDir j`.
     -- Checked in `SCV/DistributionalEOWHolomorphic.lean`.

   theorem integral_pointwiseDbar_mul_eq_zero_of_distributionalHolomorphic
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hCR : IsDistributionalHolomorphicOn Hdist U0)
       (H : ComplexChartSpace m -> ℂ)
       (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
       (hRep : RepresentsDistributionOnComplexDomain Hdist H U0)
       (j : Fin m)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0) :
       (∫ z : ComplexChartSpace m, pointwiseDbar j H z * φ z) = 0 := by
     -- 1. `hRep (dbarSchwartzCLM j φ) (hφ.dbar j)` rewrites
     --    `Hdist (dbarSchwartzCLM j φ)` as `∫ H * dbar φ`.
     -- 2. `hCR j φ hφ` says the same left side is zero.
     -- 3. Use `exists_local_schwartz_representative_with_dbar_eq` below to
     --    choose a global Schwartz `G` with `G = H` near
     --    `tsupport (dbar φ)` and `dbar G = pointwiseDbar H` on
     --    `tsupport φ`.
     -- 4. Replace `H` by `G` in `∫ H * dbar φ`, apply
     --    `integral_mul_dbarSchwartzCLM_right_eq_neg_left G φ j`, and replace
     --    `dbar G` by `pointwiseDbar H` on `tsupport φ`.

   theorem exists_local_schwartz_representative_with_dbar_eq
       {H : ComplexChartSpace m -> ℂ} {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0)
       (j : Fin m) :
       ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
         (∀ z ∈ tsupport
             ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
               ComplexChartSpace m -> ℂ),
             H z = G z) ∧
         (∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
             (dbarSchwartzCLM j G) z = pointwiseDbar j H z)

     -- Proof transcript:
     -- * Use `exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen`
     --   to get a smooth compact cutoff `χ` and an open set `V` with
     --   `tsupport φ ⊆ V ⊆ U0` and `χ = 1` on `V`.
     -- * Package `(fun z => (χ z : ℂ) * H z)` as a Schwartz map.  It is
     --   globally smooth because outside `U0` the cutoff is eventually zero,
     --   while on `U0` it is the product of a global smooth cutoff and the
     --   real-smooth representative.
     -- * The equality `H = G` on `tsupport (dbar φ)` follows from
     --   `dbarSchwartzCLM_tsupport_subset j φ`.
     -- * On `tsupport φ`, `χ = 1` on the open neighborhood `V`, hence
     --   `fderiv ℝ G z = fderiv ℝ H z`; unfold
     --   `dbarSchwartzCLM_apply_eq_pointwiseDbar`.

   theorem pointwiseDbar_eq_zero_of_distributionalHolomorphic
       (Hdist : SchwartzMap (ComplexChartSpace m) ℂ ->L[ℂ] ℂ)
       {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hCR : IsDistributionalHolomorphicOn Hdist U0)
       (H : ComplexChartSpace m -> ℂ)
       (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
       (hRep : RepresentsDistributionOnComplexDomain Hdist H U0) :
       ∀ j : Fin m, ∀ z ∈ U0, pointwiseDbar j H z = 0 := by
     intro j
     exact
       eq_zero_on_open_of_supportsInOpen_schwartz_integral_zero
         hU0_open
         (continuousOn_pointwiseDbar_of_contDiffOn hU0_open hH_smooth j)
         (integral_pointwiseDbar_mul_eq_zero_of_distributionalHolomorphic
           Hdist hU0_open hCR H hH_smooth hRep j)
   ```

   Finally convert smooth real differentiability plus the Cauchy-Riemann
   equations into complex differentiability:

   ```lean
   theorem differentiableOn_complex_of_contDiffOn_real_and_pointwiseDbar_zero
       {H : ComplexChartSpace m -> ℂ} {U0 : Set (ComplexChartSpace m)}
       (hU0_open : IsOpen U0)
       (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
       (hDbar : ∀ j : Fin m, ∀ z ∈ U0, pointwiseDbar j H z = 0) :
       DifferentiableOn ℂ H U0
   ```

   At `z ∈ U0`, the real derivative `fderiv ℝ H z` is a continuous real-linear
   map.  The equations `pointwiseDbar j H z = 0` say
   `L (complexImagDir j) = Complex.I * L (complexRealDir j)` for every
   coordinate.  Decompose an arbitrary vector into its real and imaginary
   coordinate directions to prove `L (Complex.I • v) = Complex.I * L v`; hence
   `L` is the restriction of a continuous complex-linear map.  This supplies
   the `HasFDerivAt` witness over `ℂ` and therefore `DifferentiableOn ℂ H U0`.

   The implementation exposes the finite-dimensional linear algebra as named
   lemmas, because this is the part most likely to fail if written as one
   opaque tactic block:

   ```lean
   theorem complexChart_vector_decomposition
       (v : ComplexChartSpace m) :
       v =
         ∑ j : Fin m,
           ((v j).re • complexRealDir j + (v j).im • complexImagDir j)

   theorem complexChart_I_smul_realDir
       (j : Fin m) :
       Complex.I • complexRealDir j = complexImagDir j

   theorem complexChart_I_smul_imagDir
       (j : Fin m) :
       Complex.I • complexImagDir j = -complexRealDir j

   theorem fderiv_imagDir_eq_I_mul_realDir_of_pointwiseDbar_zero
       {H : ComplexChartSpace m -> ℂ} {z : ComplexChartSpace m} {j : Fin m}
       (h : pointwiseDbar j H z = 0) :
       fderiv ℝ H z (complexImagDir j) =
         Complex.I * fderiv ℝ H z (complexRealDir j)

   theorem realCLM_commutes_I_of_coordinate_CR
       (L : ComplexChartSpace m ->L[ℝ] ℂ)
       (hcoord : ∀ j : Fin m,
         L (complexImagDir j) = Complex.I * L (complexRealDir j)) :
       ∀ v : ComplexChartSpace m, L (Complex.I • v) = Complex.I * L v

   theorem realCLM_map_complex_smul_of_commutes_I
       (L : ComplexChartSpace m ->L[ℝ] ℂ)
       (hI : ∀ v : ComplexChartSpace m, L (Complex.I • v) = Complex.I * L v)
       (c : ℂ) (v : ComplexChartSpace m) :
       L (c • v) = c • L v

   noncomputable def complexChartCLMOfRealCLMCommutingI
       (L : ComplexChartSpace m ->L[ℝ] ℂ)
       (hI : ∀ v : ComplexChartSpace m, L (Complex.I • v) = Complex.I * L v) :
       ComplexChartSpace m ->L[ℂ] ℂ
   ```

   These coordinate and complex-linear packaging lemmas are checked in
   `SCV/DistributionalEOWHolomorphic.lean`.

   Then build the complex derivative witness by defining
   `Lℂ : ComplexChartSpace m ->L[ℂ] ℂ` from `L = fderiv ℝ H z` and
   `realCLM_commutes_I_of_coordinate_CR`, with pointwise formula
   `Lℂ v = L v`.  Apply
   `differentiableAt_iff_restrictScalars ℝ` at the open point
   `z ∈ U0`, using `hH_smooth.differentiableOn (by simp)` and openness of
   `U0` to promote real differentiability within `U0` to
   `DifferentiableAt ℝ H z`.

   The checked assembly of `distributionalHolomorphic_regular` is:

   ```lean
   have hΔ :
       ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
         SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U0 ->
           Hdist (complexChartLaplacianSchwartzCLM φ) = 0 :=
     fun φ hφ =>
       local_laplacian_zero_of_distributionalHolomorphic Hdist hCR φ hφ
   obtain ⟨H, hH_smooth, hRep⟩ :=
     weyl_laplacian_distribution_regular_on_open Hdist hm hU0_open hΔ
   have hDbar :=
     pointwiseDbar_eq_zero_of_distributionalHolomorphic
       Hdist hU0_open hCR H hH_smooth hRep
   exact ⟨H,
     differentiableOn_complex_of_contDiffOn_real_and_pointwiseDbar_zero
       hU0_open hH_smooth hDbar,
     hRep⟩
   ```

   This closes the distributional-holomorphic regularity input needed by the
   regularized-envelope route.  The next proof-doc/Lean frontier is no longer
   CR extraction, the delta-limit estimate, or the pointwise representation
   bridge; the checked recovery lemmas now cover
   `regularizedEnvelope_kernelLimit_from_representation`,
   `regularizedEnvelope_deltaLimit_agreesOnWedges`,
   `regularizedEnvelope_pointwiseRepresentation_of_productKernel`, and
   `regularizedEnvelope_chartEnvelope_from_productKernel`.  The remaining
   Streater-Wightman nonzero-envelope work is the upstream regularized-family
   construction/product-kernel interface and the local continuous EOW
   extraction/patching package below.
8. Use the representation identity with an approximate identity `ψι -> δ0`.
   The tests `realConvolutionTest φ ψι` converge to `φ`, while on wedge pieces
   `Gψι` agrees with the real mollifications of `Fplus`/`Fminus`; the existing
   `tendsto_realMollify_normedBump_tubeDomain` theorem supplies the pointwise
   wedge convergence.  Limit uniqueness gives `H = Fplus` on the plus wedge
   and `H = Fminus` on the minus wedge.

No theorem may be named
`HasCommonDistributionalBoundaryValueOn`, `BoundaryPairingLimit`, or similar:
the actual data are compact support, support margin, compact direction set,
slow growth, and the `TendstoUniformlyOn` boundary limits.

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

For theorem 2, the immediate SCV implementation order is:

1. `SCV/DistributionalEOWKernel.lean`: the QFT-free Schwartz substrate.
   The checked portion is `complexTranslateSchwartz`,
   `schwartzTensorProduct₂`, `realConvolutionShearCLE`,
   `complexRealFiberIntegralRaw`, `complexRealFiberIntegral`,
   `realConvolutionTest`, the real-fiber translation CLM, fiber-integral
   invariance under real-fiber translation, the product-test fiber integral
   identity, the real/complex translation composition laws, the
   sheared-functional / fiber-invariance predicates, the sheared tensor
   fiber-translation identity, the mixed fiber quotient, product density,
   translation-covariant descent, the product-kernel `∂bar` consumer, the
   distributional-holomorphicity continuity passage, compact
   approximate-identity convergence, `distributionalHolomorphic_regular`,
   the pointwise representation bridge, and the checked chart assembly theorem
   `regularizedEnvelope_chartEnvelope_from_productKernel`.  The remaining
   portion is the upstream local continuous EOW extraction and regularized
   local EOW family/product-kernel package;
2. `SCV/LocalContinuousEOW.lean`: adapt the now-public
   `SCV.local_eow_extension` and `SCV.local_extensions_consistent` theorem
   bodies from global tube domains to local `Ωplus/Ωminus` wedge domains;
3. `SCV/LocalDistributionalEOW.lean`: prove
   `local_distributional_edge_of_the_wedge_envelope` from the
   Streater-Wightman regularization transcript above;
4. return to `WickRotation/OSToWightmanLocalityOS45...` and instantiate the
   SCV theorem as `BHW.os45_adjacent_commonBoundaryEnvelope`.

The broader SCV infrastructure should still be implemented in this order after
the theorem-2 local EOW package is no longer blocking:

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

1. theorem 2 locality uses the new local distributional EOW envelope package
   through `BHW.os45_adjacent_commonBoundaryEnvelope`;
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
4. already-proved SCV theorems are kept separate from the live open ones,
5. the theorem-2 local EOW route names the exact pure-SCV substrate lemmas
   instead of using informal “kernel theorem” or product-tensor placeholders.

After the local/global covariance audit, the next recovery theorem is
implementation-ready only in the local-descent order specified in Section 2.4.
The first Lean target is
`regularizedLocalEOW_pairingCLM_of_fixedWindow`, preceded by the listed cutoff,
partial-evaluation, and compact-uniform seminorm helpers.  The retired
global-covariance surface
`regularizedLocalEOW_productKernel_from_continuousEOW` must not be used as the
next target.

The checked substrate remains as follows.  The first Lean file is
`SCV/DistributionalEOWKernel.lean`; it
now contains the checked QFT-free
definitions `ComplexChartSpace`, `SupportsInOpen`, `KernelSupportWithin`,
`complexRealDir`, `complexImagDir`, `directionalDerivSchwartzCLM`,
`dbarSchwartzCLM`, `IsDistributionalHolomorphicOn`,
`RepresentsDistributionOnComplexDomain`, `complexTranslateSchwartzCLM`, and
`complexTranslateSchwartz`, plus the checked SCV-owned two-space tensor
product `schwartzTensorProduct₂`, the real-direction shear
`realConvolutionShearCLE`, the raw generic fiber integral
`complexRealFiberIntegralRaw`, the fixed-fiber integrability lemma
`integrable_complexRealFiber`, the base-direction derivative field
`baseFDerivSchwartz`, the zeroth-order weighted decay estimate
`exists_norm_pow_mul_complexRealFiberIntegralRaw_le`, the uniform integrable
bound `exists_integrable_bound_baseFDerivSchwartz`,
`hasFDerivAt_complexRealFiberIntegralRaw`,
`fderiv_complexRealFiberIntegralRaw_eq`,
`contDiff_nat_complexRealFiberIntegralRaw`,
`contDiff_complexRealFiberIntegralRaw`,
`decay_complexRealFiberIntegralRaw`, `complexRealFiberIntegral`,
`realConvolutionTest` with its apply theorem,
`complexRealFiberTranslateSchwartzCLM`,
`complexRealFiberIntegral_fiberTranslate`,
`complexRealFiberIntegral_schwartzTensorProduct₂`,
`translateSchwartz_translateSchwartz`,
`complexTranslateSchwartz_complexTranslateSchwartz`,
`shearedProductKernelFunctional`, and
`IsComplexRealFiberTranslationInvariant`, plus
`complexRealFiberTranslate_shearedTensor_eq`.  It also now contains the
checked pure coordinate-transport layer `headBlockShift`,
`realBlockFlattenCLE`, `complexToFinTwoCLE`, `complexChartRealFlattenCLE`,
`finAppendCLE`, `mixedChartFiberFirstCLE`, the head/tail real-imaginary apply
lemmas, `mixedChartFiberFirstCLE_symm_headBlockShift`, and
`mixedChartFiberFirstCLE_translate`.  The transported fiber-integral identity,
pure-SCV head-block factorization extraction, mixed fiber quotient,
normalized-cutoff factorization, product-density theorem, and product-kernel
descent are now checked.  The support-preservation companion
`SCV/DistributionalEOWSupport.lean` is also checked, with
`KernelSupportWithin_hasCompactSupport`,
`directionalDerivSchwartzCLM_tsupport_subset`,
`directionalDerivSchwartzCLM_supportsInOpen`,
`dbarSchwartzCLM_tsupport_subset`, and `SupportsInOpen.dbar`.  The checked
approximate-identity companion now also supplies
`tendsto_realConvolutionTest_of_shrinking_normalized_support` and
`exists_realConvolutionTest_approxIdentity`.  The distributional-regularity and
kernel-recovery layers now continue through
`distributionalHolomorphic_regular`,
`regularizedEnvelope_holomorphicDistribution_from_productKernel`,
`regularizedEnvelope_pointwiseRepresentation_of_productKernel`, and
`regularizedEnvelope_chartEnvelope_from_productKernel`.  The next declarations
should therefore address the local continuous EOW extraction and the
regularized local EOW family/product-kernel package specified in Section 2.4.

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

For theorem 2, the boundary-value package also needs a compact-direction
strengthening.  The public `tube_boundaryValueData_of_polyGrowth` is currently
raywise; the OS45 local EOW supplier needs uniform convergence on every compact
direction set `Kη ⊆ C`.  This must be proved in the same QFT-free SCV package,
not added as a new axiom and not hidden in a BHW-specific theorem.  The
uniform theorem should have the following shape before the OS specialization:

```lean
theorem tube_boundaryValueData_uniformOnCompactDirections_of_polyGrowth
    {n d : ℕ}
    (C : Set (Fin n -> Fin (d + 1) -> ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    {F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC_bd : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ W : SchwartzMap (Fin n -> Fin (d + 1) -> ℝ) ℂ ->L[ℂ] ℂ,
      ∀ (Kη : Set (Fin n -> Fin (d + 1) -> ℝ)),
        IsCompact Kη -> Kη ⊆ C ->
        ∀ φ : SchwartzMap (Fin n -> Fin (d + 1) -> ℝ) ℂ,
          TendstoUniformlyOn
            (fun ε η => ∫ x : Fin n -> Fin (d + 1) -> ℝ,
              F (fun k μ => (x k μ : ℂ) +
                (ε : ℂ) * (η k μ : ℂ) * Complex.I) * φ x)
            (fun _ => W φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη
```

The proof is the raywise proof with every estimate made uniform on compact
`Kη`: compactness supplies a bound on `‖η‖` and a single tube-radius margin for
small `ε`; the polynomial-growth estimate gives one Schwartz seminorm
dominating all slices; continuity of the integrand in `(ε,η,x)` plus that
dominating seminorm gives local uniform convergence; a finite subcover of
`Kη` gives `TendstoUniformlyOn`.  The existing private lemmas
`tubeSlice_uniformPolyGrowth_of_polyGrowth` and
`tubeSliceIntegralCLM_uniformSeminormBound_of_polyGrowth` are the correct
starting points, but their current statements are only fixed-direction
uniformity and must be compact-direction versions before the theorem above can
be checked.

The implementation theorem slots should therefore be:

```lean
def tubeSliceFunctional (ε : ℝ) (y : ConeDir) : SchwartzMap →L[ℂ] ℂ
lemma tubeSliceFunctional_seminorm_bound
lemma tubeSliceFunctional_compactDirection_seminorm_bound
lemma tubeSliceFunctional_cauchy_as_epsilon_to_zero
lemma tubeSliceFunctional_compactDirection_cauchy_as_epsilon_to_zero
lemma tubeSliceFunctional_limit_exists
lemma tubeSliceFunctional_limit_independent_of_direction
def tubeBoundaryValueDistribution
lemma tubeBoundaryValueDistribution_isContinuous
theorem tube_boundaryValueData_uniformOnCompactDirections_of_polyGrowth
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
