# Proof-Docs Completion Plan

Purpose: this note is the execution plan for bringing the proof-document stack
to the standard

> "Lean implementation should require proving the named packages, not
> rediscovering the mathematics, changing theorem surfaces, or making new route
> choices."

This is a documentation-only plan. It does **not** authorize production Lean
deviation from the existing blueprints.

This note should be read together with:

- `docs/sorry_triage.md`
- `docs/mathlib_gap_analysis.md`
- `docs/theorem2_locality_blueprint.md`
- `docs/theorem3_os_route_blueprint.md`
- `docs/theorem4_cluster_blueprint.md`
- `docs/general_k_continuation_blueprint.md`
- `docs/scv_infrastructure_blueprint.md`
- `docs/gns_pipeline_blueprint.md`
- `docs/nuclear_spaces_blueprint.md`
- `docs/vna_infrastructure_blueprint.md`

## 0. Paper-authority rule

Every proof doc and production implementation must follow the OS papers
strictly.  OS II is the authoritative correction for the `E -> R` analytic
continuation, growth, and tempered boundary-value route wherever OS I depended
on Lemma 8.8.  The only currently documented OS-paper error is OS I Lemma 8.8;
all other deviations require a new local paper audit entry before they can
affect theorem surfaces or implementation.

Allowed "fill-in" work is limited to:

1. spelling out paper steps as Lean theorem packages;
2. adding standard analytic/topological lemmas needed to formalize those paper
   steps;
3. replacing the false OS I Lemma 8.8 many-variable jump with the OS II Chapter
   V/VI induction and estimate machinery.

Not allowed:

1. alternate proof routes chosen for implementation convenience;
2. theorem surfaces that weaken or strengthen the OS statement without a paper
   reason;
3. generic infrastructure shortcuts that bypass an OS-paper step;
4. same-test Euclidean/Minkowski equalities unless an explicit proved bridge
   justifies that exact surface.

## 0.1. External-theorem circularity audit

Before any external theorem is accepted as a theorem-2 input, audit the proof of
that external theorem for direct or transitive dependence on local
commutativity, weak local commutativity, or any equivalent permutation
symmetry of the Wightman boundary distributions being proved.

If such a dependence is present, the theorem is circular for theorem 2 and must
be fenced off as orientation only.  It may not be used as a proof supplier even
if its conclusion has the right shape.

Current examples:

1. `blocker_iterated_eow_hExtPerm_d1_nontrivial` is not a theorem-2 input in
   dimension one because it assumes `IsLocallyCommutativeWeak 1 W`.
2. Streater-Wightman Theorem 3-6 is not a theorem-2 input because its proof
   uses local commutativity.
3. Streater-Wightman Figure 2-4 remains allowed only as adjacent geometric
   real-environment input, because that local geometry does not use QFT
   locality.
4. `hallWightman_fixedPoint_endpointActiveGallery_of_two_le` is no longer an
   active theorem-2 frontier in its documented form. Its edge relation requires
   common fixed-`w` permuted-forward-tube witnesses, but the repository proves
   that distinct permuted forward-tube sectors are disjoint. The hF_perm-only
   generic direct BHW source branch-law theorem
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`
   is also not ready to close as stated.  The approved Deep Research audit
   found the statement mathematically unsafe: because nontrivial permuted
   forward tubes are disjoint from the ordered forward tube, total Lean values
   of `F` off the ordered tube can satisfy `hF_perm` without constraining the
   analytic germ whose BHW continuation is being compared.  The active
   replacement is the distributional Euclidean/Jost-anchored BHW source branch-law theorem,
   whose proved PET-algebra assembly theorem is
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry`, and whose
   branch-equality corollary is
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` on permuted
   extended-tube sectors, specialized to the OS witness as
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.  Its corrected
   source contract uses restricted real Lorentz invariance plus the real
   distributional Euclidean/Jost uniqueness anchor supplied by OS II; complex-Lorentz
   single-valuedness on `S''_n` is the Hall-Wightman output, not an input.  The
   Lean implementation locus is
   the small source file
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtension.lean`.
   Its checked support theorem
   `BHW.permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz` proves
   sector-branch holomorphicity; the theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` now proves the
   forward-tube agreement plus PET Lorentz/permutation outputs from the source
   branch law.  The genuine remaining frontier is the Hall-Wightman
   compatibility/single-valued `Fpet` branch-law construction, not any
   downstream OS wrapper;
   `BHWPermutation/PermutationFlow.lean` is forbidden for this source theorem
   because its current BHW theorem depends on `IsLocallyCommutativeWeak`.
   A checked false shortcut has been ruled out: pointwise permutation symmetry
   of the raw base function does not by itself compare arbitrary PET sector
   branches, because the complex-Lorentz representative needed for the
   comparison need not stay in the base forward tube.  The remaining gap is
   exactly Hall-Wightman single-valued continuation for the distributionally anchored
   symmetric permuted-tube datum.  The theorem-2 blueprint now fixes the internal
   branch-law proof contract: make the branches
   `G π z = BHW.extendF F (fun k => z (π k))` explicit, obtain their sector
   holomorphicity from
   `BHW.permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz`, build
   the symmetric `S'_n` datum using the distributional Euclidean/Jost anchor, apply the source
   Hall-Wightman/BHW compatibility theorem on `S''_n`, and only then build
   one `Fpet` by the existing `BHW.gluedPETValue` API.  The blueprint now also fixes
   the private lemma ladder for the implementation pass:
   `source_permutedForwardBranch_holomorphicOn`,
   `source_permutedForwardBranch_restrictedLorentzInvariant`,
   `source_permutedForwardBranch_symmetric`, and exactly one non-elementary
   source-facing compatibility theorem
   `hallWightman_source_permutedBranch_compatibility`.  No helper may assume
   the `S''_n` compatibility that this source theorem is meant to prove.
   The Lean surface now also includes the data-carrying
   `SelectedAdjacentDistributionalJostAnchorData` packet and the checked
   reindexing definition
   `bvt_F_distributionalJostAnchor_of_selectedJostData` in
   `OSToWightmanSelectedWitness.lean`; that bridge introduces no new `sorry`
   and supplies `BHW.SourceDistributionalAdjacentTubeAnchor` from selected
   adjacent OS anchor data.
   The source side also now has checked full-matrix sufficient theorems
   `BHW.sourceDistributionalUniquenessSet_of_isOpen_nonempty` and
   `BHW.sourceDistributionalUniquenessSet_of_contains_open`: a nonempty open
   real set in the full product coordinate space is a uniqueness set for
   holomorphic scalar-product representatives, by the repo's totally-real
   identity theorem.  These lemmas are true but not the general OS supplier.
   The attempted theorem that the Gram image of an OS45 Jost patch contains a
   full-matrix open subset is false: Gram matrices are symmetric, and in
   arity above the spacetime vector dimension they lie in a rank-bounded
   Hall-Wightman scalar-product variety.  The API-backed Deep Research check
   `v1_ChYtLURyYWZ4UjFKNy00d19TbWNMUUJnEhYtLURyYWZ4UjFKNy00d19TbWNMUUJn`
   confirmed this correction; the production anchor now carries the
   variety-level predicate `BHW.sourceDistributionalUniquenessSetOnVariety`.
   The approved Deep Research check rejected the hF_perm-only source boundary
   and routed growth/temperedness to the upstream OS-II boundary-value
   construction.  The remaining implementation step is now specified down to
   Lean pseudocode: prove or source-import
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
   from Hall-Wightman's scalar-product theorem plus distributional EOW on the
   distributionally anchored symmetric permuted-tube datum `S'_n`, using
   `sourceMinkowskiGram`, branch scalar-product representatives,
   compact-test Schwinger symmetry on adjacent permutation-indexed Jost
   patches, branch-boundary distribution matching there, scalar-product
   uniqueness, and Hall-Wightman single-valued continuation on `S''_n`.  Any
   adjacent-patch cover connectivity used internally belongs inside that source
   theorem, not in the theorem-2 consumer API.  A common pointwise `Φ` may be
   produced as a corollary after this source theorem, but it is not the OS
   input.  The follow-up Deep Research check
   `v1_ChdUSW5yYWFuUkhNNlVfdU1QOE9YaGtRWRIXVElucmFhblJITTZVX3VNUDhPWGhrUVk`
   specifically rejects promoting
   `BHW.petSectorFiber_adjacent_connected_of_two_le` to an active theorem-2
   gate.
   The corrected OS supplier now has an implementation-level decomposition:
   `E` should be the whole Gram image of the selected OS45 patch, while
   uniqueness is proved by finding a smaller regular Hall-Wightman real
   environment inside that image and applying the checked monotonicity lemma
   `BHW.sourceDistributionalUniquenessSetOnVariety_mono`.  The remaining
   proof-doc gaps are therefore the genuine finite-dimensional geometry and
   SCV source facts: dense/open maximal-span configurations, the regular
   Gram-map local real-environment theorem, and Hall-Wightman uniqueness from
   a maximal-totally-real scalar-product environment.  The regular-stratum
   definitions themselves are now checked in Lean:
   `sourceGramExpectedDim`, `sourceConfigurationSpan`,
   `sourceComplexConfigurationSpan`, `SourceGramRegularAt`, and
   `SourceComplexGramRegularAt`, together with the concrete template
   `sourceFullSpanTemplate`.  The theorem-2 blueprint now also gives
   proof skeletons for the three supplier facts: maximal-span density/open
   regular locus via determinant minors, regular Gram-map rank/local
   real-environment via the constant-rank theorem, and Hall-Wightman
   real-environment uniqueness via local maximal-totally-real charts plus
   analytic continuation on the connected scalar-product variety.
   The OS-side constructor is now pinned to a field-by-field Lean transcript:
   the strengthened `BHW.os45_adjacent_singleChart_commonBoundaryValue` must
   export one and the same OS45 patch `V` with Jost membership, both adjacent
   extended-tube memberships, and an
   `BHW.AdjacentOSEOWDifferenceEnvelope`.  The theorem-2 blueprint now separates
   the OS45 instantiation theorem
   `BHW.os45_adjacent_commonBoundaryEnvelope` from the direct-coordinate
   packaging: it constructs the common chart, applies the pure-SCV local
   distributional envelope theorem
   `SCV.local_distributional_edge_of_the_wedge_envelope`, and exports a
   holomorphic branch-difference function with the Wick/real trace identities.
   The SCV theorem surface is now pinned to truncated local wedges, a local
   continuous EOW lemma extracted from the Cauchy-polydisc proof,
   Streater-Wightman real-direction regularization, compact-subcone-uniform
   distributional boundary limits, kernel/nuclear-theorem recovery,
   translation covariance, compactly supported approximate identities, and
   explicit slow-growth bounds; this keeps the theorem in the OS-II
   distributional category instead of silently upgrading to pointwise boundary
   values.  The finite-order primitive shortcut is rejected because the
   multi-variable integration constants are infinite-dimensional, and the false
   polynomial-correction shortcut is not used.  The checked
   real-mollification infrastructure in `SCV/DistributionalUniqueness.lean`
   supplies part of the route, but the nonzero-envelope kernel recovery still
   has to be formalized through the exact QFT-free substrate
   `SCV.complexTranslateSchwartz`, `SCV.schwartzTensorProduct₂`,
   `SCV.schwartzKernel₂_extension`, `SCV.realConvolutionTest`,
   `SCV.translationCovariantProductKernel_descends`,
   `SCV.distributionalHolomorphic_regular`, and the envelope-family lemmas
   `SCV.regularizedEnvelope_linearContinuousInKernel`,
   `SCV.regularizedEnvelope_translationCovariant`,
   `SCV.regularizedEnvelope_productKernel`,
   `SCV.regularizedEnvelope_kernelRepresentation`, and
   `SCV.regularizedEnvelope_deltaLimit_agreesOnWedges`.  The checked consumer uses
   `bvt_F_acrOne_package` to prove vanishing.
   The first SCV substrate slice is now checked in
   `SCV/DistributionalEOWKernel.lean`: `complexTranslateSchwartz`,
   `schwartzTensorProduct₂`, `realConvolutionShearCLE`,
   `complexRealFiberIntegralRaw`, `integrable_complexRealFiber`,
   `baseFDerivSchwartz`,
   `exists_norm_pow_mul_complexRealFiberIntegralRaw_le`,
   `exists_integrable_bound_baseFDerivSchwartz`,
   `hasFDerivAt_complexRealFiberIntegralRaw`, the raw integral smoothness and
   decay theorems, `complexRealFiberIntegral`, and
   `realConvolutionTest` with the exact OS-II sign and its translation identity
   `realConvolutionTest φ ψ z = ∫ t, φ (z - realEmbed t) * ψ t`.
   The identity
   `realConvolutionTest (complexTranslateSchwartz a φ) ψ =
    realConvolutionTest φ (translateSchwartz a ψ)`
   is the checked sign bridge into product-kernel descent.
   The same SCV file now checks the first fiber-descent primitives
   `complexRealFiberTranslateSchwartzCLM`,
   `complexRealFiberIntegral_fiberTranslate`,
   `complexRealFiberIntegral_schwartzTensorProduct₂`,
   `translateSchwartz_translateSchwartz`,
   `complexTranslateSchwartz_complexTranslateSchwartz`,
   `shearedProductKernelFunctional`, and
   `IsComplexRealFiberTranslationInvariant`, plus
   `complexRealFiberTranslate_shearedTensor_eq`.  The same SCV substrate now
   checks the pure coordinate transport needed for the mixed fiber
   factorization: `headBlockShift`, `realBlockFlattenCLE`,
   `complexToFinTwoCLE`, `complexChartRealFlattenCLE`, `finAppendCLE`,
   `mixedChartFiberFirstCLE`, its head/tail real-imaginary apply lemmas,
   `mixedChartFiberFirstCLE_symm_headBlockShift`, and the sign-sensitive
   transport identity `mixedChartFiberFirstCLE_translate`.  The transported
   fiber-integral identity
   `complexRealFiberIntegral_eq_transport_integrateHeadBlock`, the pure-SCV
   head-block factorization theorem, and the mixed
   `map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant`
   theorem are now checked.  The normalized-cutoff consumer is also checked in
   `SCV/DistributionalEOWKernelFactorization.lean`:
   `SCV.schwartzTensorProduct₂CLMRight`,
   `SCV.complexRealFiberTranslationDescentCLM`, and
   `SCV.map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant`.
   The next proof-doc/Lean target is therefore the product-kernel extension and
   translation-covariant descent layer:
   `SCV.schwartzKernel₂_extension`,
   `SCV.translationCovariantProductKernel_descends`, and
   `SCV.distributionalHolomorphic_regular`.  The descent theorem is now
   documented with the correct global/local split:
   first prove the global pure-SCV theorem from
   `SCV.ProductKernelRealTranslationCovariantGlobal`, then derive the
   support-restricted envelope corollary from
   `SCV.ProductKernelRealTranslationCovariantLocal` after applying the fixed
   cutoff.  The remaining gap before the sheared product-kernel descent is the
   mixed product-tensor density/kernel-extension theorem: product covariance is
   currently an equality on `schwartzTensorProduct₂` tests, and promotion to all
   mixed Schwartz tests must go through `schwartzKernel₂_extension` or an
   equivalent uniqueness principle.  Before that density promotion, the next
   100%-ready Lean slice is the tensor-level sign theorem
   `SCV.shearedProductKernel_fiberTranslate_shearedTensor_eq_self_of_productCovariant`:
   combine `SCV.complexRealFiberTranslate_shearedTensor_eq` with global product
   covariance at `-a` and
   `SCV.translateSchwartz_translateSchwartz` to prove that the sheared
   functional is invariant on every sheared product tensor.  This closes the
   exact OS-II sign/covariance calculation on the generator family without
   pretending that product-tensor density has already been proved.  The next
   100%-ready promotion theorem is conditional on the precise dense-span
   blocker `SCV.ShearedProductTensorDense m`: define
   `SCV.shearedProductTensorSet` as the sheared `schwartzTensorProduct₂`
   generator family, take its complex linear span, prove equality of the two
   continuous functionals on that span by `Submodule.span_induction`, and use
   the closed-equalizer dense-set argument to obtain
   `SCV.shearedProductKernel_fiberInvariant_of_productCovariant_of_shearedProductTensorDense`.
   Combining that with the checked normalized fiber factorization gives
   `SCV.translationCovariantProductKernel_descends_of_shearedProductTensorDense`.
   This is a genuine reduction: all remaining unproved mathematical content is
   isolated in `SCV.ShearedProductTensorDense m`, equivalent to the mixed
   two-space product-density/kernel-extension theorem.  The conditional
   promotion/descent package is now checked in
   `SCV/DistributionalEOWProductKernel.lean`; the next proof-doc task is to
   make `SCV.ShearedProductTensorDense m`/`SCV.schwartzKernel₂_extension`
   itself Lean-ready without importing the Wightman `schwartz_nuclear_extension`
   axiom.
   The first Lean-ready part of that density task is now checked: define the
   unsheared simple-product generator family
   `SCV.productTensorSet m`, its span `SCV.productTensorSpan m`, and the
   standard blocker `SCV.ProductTensorDense m`.  Then prove
   `SCV.shearedProductTensorDense_of_productTensorDense` by transporting
   density through
   `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
     (SCV.realConvolutionShearCLE m)`.  The checked proof should use
   `SCV.shearedProductTensorSet_eq_image_productTensorSet`,
   `Submodule.map_span`,
   `Submodule.dense_iff_topologicalClosure_eq_top`, surjectivity from
   `SCV.compCLMOfContinuousLinearEquiv_symm_left_inv`, and
   `DenseRange.topologicalClosure_map_submodule`.  The consumer corollary
   `SCV.translationCovariantProductKernel_descends_of_productTensorDense`
   simply feeds this transported density into the already checked
   sheared-density descent theorem.  This is not a wrapper inflation: it
   replaces the shear-specific blocker by the standard unsheared product
   Schwartz density theorem, which is exactly the remaining functional-analytic
   content of `SCV.schwartzKernel₂_extension`.
   The next density proof is now pinned to a pure-SCV/GaussianField route, not
   to Wightman `schwartz_nuclear_extension`.  Add
   `SCV/ComplexSchwartz.lean` with `SCV.schwartzRealPartCLM`,
   `SCV.schwartzImagPartCLM`, `SCV.schwartzOfRealCLM`, and
   `SCV.complexSchwartzDecomposeCLE`, importing no Wightman files.  These
   SCV-owned names deliberately avoid colliding with the already existing
   Wightman `SchwartzMap.*` decomposition declarations.  Add
   `SCV/SchwartzExternalProduct.lean` for the checked external product
   `(x,y) ↦ φ x * ψ y`, and `SCV/ProductDensity.lean` for
   `SCV.twoBlockProductSchwartz`, `SCV.flatMixedCLM`,
   `SCV.flattenMixedFunctional`, and the bridge
   `SCV.flatTwoBlockProduct_eq_mixedProduct`.  The next theorem in that
   product-density companion proves, for `0 < m`, that any mixed-chart
   complex continuous linear functional vanishing on all
   `SCV.schwartzTensorProduct₂ φ ψ` is zero.  The proof transports the
   functional through `SCV.mixedChartFiberFirstCLE m`, uses
   `GaussianField.productHermite_schwartz_dense (D := ℝ) (m + m*2)` on the
   flat domain `Fin (m + m*2) -> ℝ`, splits each one-dimensional Hermite
   product into the first `m` real-fiber coordinates and the last `m*2`
   flattened complex-chart coordinates, and then reconstructs complex-valued
   tests from real/imaginary parts with `SCV.complexSchwartzDecomposeCLE`.
   This product-density companion is now checked through the final density
   theorem: `SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts`,
   `SCV.mixedProductCLM_zero_of_zero_on_productTensor`,
   `SCV.ProductTensorDense_of_pos`, `SCV.ProductTensorDense_zero`, and
   `SCV.ProductTensorDense_all`.  The final `SCV.ProductTensorDense_of_pos`
   is the same Hahn-Banach
   separation argument as `Wightman/Reconstruction/DenseCLM.lean`, with the
   new pure-SCV CLM-uniqueness theorem replacing Wightman nuclear uniqueness.
   The `m = 0` case must be a direct singleton-domain proof using the constant
   product tensor; it is not covered by GaussianField's positive-dimensional
   product-Hermite theorem.  The resulting implementation targets are:

   ```lean
   theorem SCV.flatTwoBlockProduct_eq_mixedProduct
   theorem SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts
   theorem SCV.mixedProductCLM_zero_of_zero_on_productTensor
   theorem SCV.ProductTensorDense_of_pos
   theorem SCV.ProductTensorDense_zero
   theorem SCV.ProductTensorDense_all
   ```

   `SCV.ProductTensorDense_all` now feeds directly into the already checked
   `SCV.translationCovariantProductKernel_descends_of_productTensorDense` via
   the new `SCV.translationCovariantProductKernel_descends`, removing the
   product-kernel density blocker from theorem 2.
   The local distributional-EOW support-preservation layer is now checked in
   `SCV/DistributionalEOWSupport.lean`, not introduced as a new theorem
   wrapper.  It proves `SCV.KernelSupportWithin_hasCompactSupport`, because
   the production predicate is only closed-ball topological-support containment
   and compact support follows from finite-dimensional compactness of closed
   balls.  It also proves
   `SCV.directionalDerivSchwartzCLM_tsupport_subset`,
   `SCV.directionalDerivSchwartzCLM_supportsInOpen`,
   `SCV.dbarSchwartzCLM_tsupport_subset`, and `SCV.SupportsInOpen.dbar`.
   These are the exact lemmas consumed by the upcoming
   `regularizedEnvelope_productKernel_dbar_eq_zero` integration-by-parts
   package: they ensure every `dbarSchwartzCLM` test remains compactly
   supported inside the same open set `U0`.
   The next `∂bar` algebra slice is also fixed at theorem level:
   `SCV/DistributionalEOWDbar.lean` proves
   `SCV.integral_mul_directionalDerivSchwartzCLM_right_eq_neg_left`,
   `SCV.integral_mul_dbarSchwartzCLM_right_eq_neg_left`, and
   `SCV.integral_mul_dbarSchwartzCLM_right_eq_zero_of_dbar_eq_zero`.  The file
   now also proves
   `SCV.integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz`,
   the algebraic endpoint of the local cutoff argument.  Its hypotheses are
   exactly the data the cutoff must produce: a Schwartz representative `G`
   agreeing with the holomorphic factor on
   `tsupport (dbarSchwartzCLM j φ)` and satisfying
   `dbarSchwartzCLM j G = 0` on `tsupport φ`.
   The first cutoff subtheorem is now checked in
   `SCV/DistributionalEOWCutoff.lean`:
   `SCV.exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen`.  It uses
   nested thickenings of the compact set `K = tsupport φ ⊆ U`, applies
   `exists_contMDiff_support_eq_eq_one_iff` to
   `thickening r₂ K` and `closure (thickening r₁ K)`, and returns a smooth
   real cutoff equal to one on an open neighborhood of `K` with compact
   topological support inside `U`.
   The representative theorem is now checked in
   `SCV/DistributionalEOWRepresentative.lean`:
   `SCV.exists_local_schwartz_representative_eq_on_open` forms the
   zero-extended compactly supported smooth function `χ * F`, converts it into
   a Schwartz map, and proves agreement with `F` on the cutoff neighborhood.
   The pointwise Cauchy-Riemann theorem
   `SCV.dbarSchwartzCLM_eq_zero_on_of_eqOn_holomorphic` derives local
   coordinate `∂bar` vanishing from
   `hF_holo.analyticOnNhd_of_finiteDimensional hU_open`.  These feed
   `SCV.exists_local_dbarClosed_schwartz_representative`, and
   `SCV.integral_holomorphic_mul_dbarSchwartz_eq_zero` follows immediately by
   the checked localization lemma.  The product-kernel consumer
   `SCV.regularizedEnvelope_productKernel_dbar_eq_zero` is now checked too:
   it applies the product-kernel representation to
   `dbarSchwartzCLM j φ`, using `SupportsInOpen.dbar`, and then invokes
   `SCV.integral_holomorphic_mul_dbarSchwartz_eq_zero` for the scalar
   holomorphic kernel `G ψ`.  The continuity-passage theorem
   `SCV.translationCovariantKernel_distributionalHolomorphic` is now checked
   under the concrete approximate-identity hypotheses
   `∀ᶠ i, KernelSupportWithin (ψι i) r` and
   convergence of `realConvolutionTest θ (ψι i)` to `θ` in the Schwartz
   topology for every `θ`.  The next genuine theorem-2 SCV target is therefore
   the approximate-identity construction that supplies those two hypotheses:
   `SCV.exists_normalized_schwartz_bump_kernelSupportWithin`,
   `SCV.exists_shrinking_normalized_schwartz_bump_sequence`,
   `SCV.tendsto_realConvolutionTest_of_shrinking_normalized_support`, and
   `SCV.exists_realConvolutionTest_approxIdentity` are now checked.  The
   implemented proof uses the exact Lean slots recorded in
   `docs/scv_infrastructure_blueprint.md`: kernel `L¹` mass from real
   nonnegative normalization, `norm_realEmbed_le`, `continuous_realEmbed`,
   support-to-zero from `KernelSupportWithin`, the translated-derivative
   identity, integrability of the translated derivative kernel, zeroth-order
   and all-orders derivative-through-convolution identities, the global
   mean-value linear small-translation estimate in Schwartz seminorms, and the
   final `WithSeminorms` convergence argument.
   Because `SCV/DistributionalEOWKernel.lean` is now a checked, sorry-free
   1000-line support file, the next implementation stage uses new pure-SCV
   companions rather than growing it.  `SCV.HeadBlockIntegral` is now
   implemented directly as a finite-dimensional real fiber integral, adapting
   the checked `complexRealFiberIntegral` estimates to the base/fiber product
   `((Fin n -> ℝ) × (Fin m -> ℝ))`; the public theorem
   `SCV.integrateHeadBlock_apply_finAppend` is checked and reduces by the
   continuous-linear equivalence `headTailAppendCLE`.  The corresponding mixed
   chart transport theorem
   `SCV.complexRealFiberIntegral_eq_transport_integrateHeadBlock` is checked in
   `SCV/DistributionalEOWKernelTransport.lean`.  The existing Wightman
   `SliceIntegral.lean`, `BlockIntegral.lean`, and
   `HeadBlockTranslationInvariant.lean` files remain source patterns only and
   are not imported into SCV.  The next descent-side checked lemma is now also
   in `SCV.HeadBlockIntegral`: `integrateHeadBlock_translate_head`, proving
   that the quotient map is invariant under translating the integrated head
   coordinates.  The remaining head-block factorization proof is pinned to the
   recursive quotient descent in the checked Wightman source pattern: prove
   the one-coordinate quotient through `sliceIntegral` using the
   finite-dimensional `headFiberAntideriv`, then induct over the head block.
   The direct quotient algebra needed by that
   induction is now also checked in `SCV.HeadBlockIntegral`:
   `integrateHeadBlock_zero`, `integrateHeadBlock_add`, and
   `integrateHeadBlock_sub`.  `SCV/TranslationDifferentiation.lean` now checks
   the QFT-free translate difference-quotient theorem, and
   `SCV.HeadBlockIntegral` now checks
   `IsHeadBlockTranslationInvariantSchwartzCLM` and
   `map_lineDeriv_headBlockShift_eq_zero`, so invariant functionals are known
   to annihilate head-coordinate derivatives.  `SCV/SchwartzPrependField.lean`
   now checks the collision-free pure-SCV fixed-head product package
   `SCV.tailCLM`, `SCV.prependField`, and `SCV.prependFieldCLMRight`.
   `SCV/HeadFiberAntideriv.lean` now checks the first slice-integral batch:
   `tailInsertCLM`, `sliceIntegralRaw`, the Fubini theorem
   `integral_sliceIntegralRaw`, the slice decay majorants, differentiated
   slice formulas through `contDiff_sliceIntegralRaw`,
   `decay_sliceIntegralRaw`, `sliceIntegral`, `integrable_sliceSection`, the
   complex algebra/prepend identities including `sliceIntegral_prependField`,
   and the `iicZeroSlice` derivative/`ContDiff` package.
   `SCV/HeadFiberAntiderivInterval.lean` now checks `hasDerivAt_integral_Iic`,
   `intervalPiece`, the product differentiability split,
   `contDiff_intervalPiece`, `headFiberAntiderivRaw`,
   `headFiberAntiderivRaw_eq_interval_add_iic`, and
	   `lineDeriv_headFiberAntiderivRaw`.  `SCV/HeadFiberAntiderivDecay.lean`
	   now checks the remaining head-fiber work: zero-slice preservation under
	   pure-tail derivatives, the raw primitive derivative identities, the
	   `Set.Ioi` complementary-tail representation, zeroth-order and full
	   iterated-derivative decay, and final `headFiberAntideriv` Schwartz
	   packaging with pointwise and operator-form head-direction FTC.  No
	   Wightman import is used for these extractions.  The
	   one-coordinate descent layer in `SCV/HeadBlockDescent.lean` now checks:
	   head-translation invariant functionals kill head derivatives, vanish on
	   zero `sliceIntegral`, factor through `sliceIntegral` using a concrete
	   normalized bump, and compare any two tests with equal `sliceIntegral`.
	   The general head-block descent layer in `SCV/HeadBlockDescent.lean` also
	   now checks: the pure finite-dimensional reindexing API, the fixed-tail
	   head section, `integrateHeadBlock_sliceIntegral_reindex`, the reindexed
	   head-block translation identities, preservation of remaining-head
	   invariance under one-coordinate descent, and
	   `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV`.
	   The mixed-chart consumer in
	   `SCV/DistributionalEOWKernelTransport.lean` now also checks
	   `map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant`,
	   transporting fiber-translation invariance through
	   `mixedChartFiberFirstCLE` and using
	   `complexRealFiberIntegral_eq_transport_integrateHeadBlock` plus the
	   checked head-block descent theorem.
	   The general proof uses a documented
	   SCV-specific bridge: because `SCV.integrateHeadBlock` is the direct
	   finite-dimensional integral rather than the old recursive definition,
	   it first proves `integrateHeadBlock_sliceIntegral_reindex` by the fixed-tail
	   `integral_sliceIntegralRaw`/Fubini argument recorded in
	   `docs/scv_infrastructure_blueprint.md`.  The blueprint now fixes the
	   exact Lean route for that bridge: extract a pure SCV
	   `schwartzPartialEval₂` package, define `fixedTailHeadSection` by
	   partial evaluation after `finAppendCLE`, prove the cast identity by the
	   three finite-index cases, and apply the already checked
	   `integral_sliceIntegralRaw`.  The recursive theorem transcript is also
	   pinned to the checked Lean route: the `m = 0` base case uses the
	   zero-dimensional volume/Dirac identity and
	   `Fin.append default (castFinCLE (Nat.zero_add n) x) = x`, and the
	   successor step uses the new direct/recursive bridge to convert equality
	   of full head-block integrals into equality of the sliced remaining
	   integrals before applying the induction hypothesis.
	   The
	   scratch algebra in
   `test/proofideas_head_block_helpers.lean` has been independently checked:
   it contains 19 proved helper theorems, not the 15 recorded in
   `agents_chat.md` #1313.  Port only the helpers consumed by the immediate
   proof transcript; do not turn the scratch inventory into a wrapper layer.
	   The proof-doc gap exposed by the source audit is now closed in
	   `docs/scv_infrastructure_blueprint.md`: the precursor extraction, the
	   first `HeadFiberAntideriv.lean` slice, and
	   `HeadFiberAntiderivInterval.lean` and `HeadFiberAntiderivDecay.lean` are
	   now checked.  The blueprint records the exact declaration order for the
	   decay file and the proof transcript that was implemented.  The next local
	   file should be `SCV/HeadBlockDescent.lean`, the recursive quotient-descent
	   port of the checked Wightman source pattern rather than a free-floating
	   wrapper layer.
   The #1307 audit has been folded into the route: `LocalTranslateMargin` is
   only the explicit closed-ball real-translation support condition, the final
   `SCV.local_distributional_edge_of_the_wedge_envelope` theorem must include
   uniqueness on the constructed open set, the
   `distributionalHolomorphic_regular` input is preceded by a concrete
   regularity package, and the OS45 boundary-value step requires a
   compact-subcone-uniform strengthening of
   `bvt_boundary_values` derived from the OS-II polynomial-growth boundary
   value theorem.  In particular, `bvt_boundary_values` as currently checked is
   raywise in `η`; the theorem-2 consumer needs the documented
   `TendstoUniformlyOn` theorem over every compact direction set before the
   SCV envelope can be applied.
   The next proof-doc frontier is now exactly
   `SCV.distributionalHolomorphic_regular`.  The blueprint records the Lean
   helper sequence: `dzSchwartzCLM` and its support lemmas, the checked
   coordinate-Laplacian identity
   `complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz`, the reduction from
   distributional `∂bar`-holomorphy to local harmonicity, the localized Weyl
   lemma/parametrix for the real Laplacian after transport from the plain
   chart to a Euclidean model, the checked `pointwiseDbar`, Euclidean
   chart/Schwartz transport bridges, coordinate-direction transport,
   Laplacian transport, transported distribution, and support transport,
   plus support transport in both directions, the volume-preserving
   chart-change theorem, and the Euclidean-representative pullback theorem.
   The Euclidean Weyl proof route is now pinned to the pure mollifier
   scale-invariance proof in `docs/scv_infrastructure_blueprint.md`; after it
   lands, extraction
   of pointwise Cauchy-Riemann equations from the smooth representative using the checked
   `∂bar` integration-by-parts theorem, and conversion from real smoothness
   plus CR equations to `DifferentiableOn ℂ`.
   The initial coordinate and trace-membership support
   `BHW.configPermCLE`, `BHW.os45CommonChartCLE`,
   `BHW.wickRotate_ordered_mem_acrOne`,
   `BHW.adjacent_wick_traces_mem_acrOne`, and
   `BHW.os45CommonChart_real_mem_pulledRealBranchDomain_pair` is checked in
   `OSToWightmanLocalityOS45CommonChart.lean` and
   `OSToWightmanLocalityOS45TraceMembership.lean`, so the next unresolved proof
   document/Lean targets are the pure-SCV local distributional envelope theorem
   and its OS45 instantiation.
   `BHW.sourceRealEnvironment_of_os45JostPatch` supplies the Gram environment
   for that same `V`; and
   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII` fills the
   eleven fields of `SelectedAdjacentDistributionalJostAnchorData` before the
   already checked bridge constructs
   `BHW.SourceDistributionalAdjacentTubeAnchor`.
   The theorem-2 blueprint now also gives the full scalar-coordinate
   Hall-Wightman source packet needed after those suppliers are available:
   checked Gram-permutation/domain definitions, the
   `SourceScalarRepresentativeData` package, the ordinary extended-tube scalar
   representative existence theorem, the compact-test-to-pointwise real-patch
   conversion, adjacent seed equality on the Gram environments, the
   scalar-overlap continuation theorem on `S''_n`, and the final Lean
   transcript closing
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`.
   The compact-test-to-pointwise conversion, adjacent seed equality, and final
   PET branch transcript are now checked in Lean; the two remaining source
   obligations are the Hall-Wightman scalar representative existence theorem
   and the Hall-Wightman scalar-overlap continuation theorem.
5. Streater-Wightman Theorem 2-11 has now been audited as another statement of
   the BHW analytic-continuation theorem, not as a source for the missing
   active-gallery theorem. Streater-Wightman Figure 2-4 remains only the
   adjacent common-real-environment input; it does not supply a global finite
   chamber gallery.
6. Jost, *The general theory of quantized fields*, p. 83, second theorem, has
   been page-audited in the local image PDF. It is the OS I §4.5 boundary
   locality theorem: Wightman properties except locality plus total symmetry
   imply locality. The remaining Slot-10 work is the Lean translation into the
   canonical-shell pairing theorem, not source identification.
7. The theorem-2 Slot-6/Slot-7 interface no longer has two active branches.
   Use the direct source-backed BHW single-valuedness theorem on `S''_n`; do
   not route theorem 2 through `petOrbitChamberConnected_of_two_le` or a
   common-forward-tube fixed-orbit gallery.

## 1. What "100% implementation-ready" means

A proof doc counts as complete only when all of the following are true.

1. The theorem route is unique.
   There is one endorsed theorem path, and alternate routes are either deleted
   or explicitly quarantined.
2. The theorem surfaces are fixed.
   The named theorem packages are part of the implementation contract, not loose
   suggestions.
3. The helper-theorem packaging is fixed.
   If the later Lean code is allowed a packaging convenience, the exact allowed
   form is documented.
4. The proof transcript is explicit.
   The doc says which theorem is proved first, which theorem consumes it next,
   and how the proof moves mathematically from one to the next.
5. Existing repo consumers are named exactly.
   The doc does not say "use existing infrastructure"; it says which theorem
   names are consumed.
6. Representation constraints are explicit.
   If the current Lean encoding differs from the paper-level language, the doc
   says exactly how the implementation should adapt without changing the route.
7. Historical alternatives are fenced off.
   Earlier false routes, wrapper-heavy routes, or broader theorem surfaces are
   marked as forbidden rather than left as optional memory.
8. Exit criteria are checkable.
   The doc can be audited by search for unresolved wording and by theorem-name
   cross-checks.

## 2. Global completion protocol

Every proof-doc completion pass should follow this order.

1. Search for tentative wording:
   - `candidate`
   - `if needed`
   - `if easiest`
   - `may shift`
   - `placeholder`
   - `future theorem slot`
   - `fallback`
   - `later Lean`
2. Classify each hit as:
   - acceptable implementation commentary,
   - harmless historical note,
   - or a real mathematical/documentation gap.
3. For every real gap:
   - fix the route,
   - fix the theorem names,
   - fix the proof-package order,
   - update the global triage docs.
4. Re-audit the nearest downstream and upstream docs so the fix does not leave
   inconsistent language elsewhere.
5. Record any production-relevant doc change in `agents_chat.md` append-only.

## 3. Completion order for the remaining docs

The remaining hardening work should proceed in this order.

### Phase A. Active OS-route frontiers

These are the highest-priority docs because Claude’s production work depends on
them directly.

1. `docs/theorem3_os_route_blueprint.md`
2. `docs/theorem2_locality_blueprint.md`
3. `docs/theorem4_cluster_blueprint.md`
4. `docs/sorry_triage.md`
5. `docs/mathlib_gap_analysis.md`

Completion criterion for Phase A:

1. theorem 2/3/4 each have exactly one endorsed route;
2. each package theorem has a fixed name;
3. each doc explicitly identifies which existing production theorems are
   consumers and which new theorem packages are still missing;
4. no route-level wording still allows fallback to discarded shells, K2
   wrappers, or raw-topology restarts.

### Phase B. Core analysis support

These docs control the mathematical suppliers for theorem 2/3 and general `k`.

1. `docs/scv_infrastructure_blueprint.md`
2. `docs/nuclear_spaces_blueprint.md`
3. `docs/general_k_continuation_blueprint.md`
4. `docs/os1_detailed_proof_audit.md`
5. `docs/os2_detailed_proof_audit.md`

Completion criterion for Phase B:

1. every SCV supplier is broken into theorem packages rather than invoked as
   "SCV machinery";
2. the nuclear-space doc has one endorsed route and a blocked-only fallback;
3. the general-`k` doc fixes file boundaries, theorem slots, indexing, and SCV
   imports before implementation;
4. OS I / OS II audit docs point to exact local theorem-package suppliers and
   no longer leave hidden paper steps implicit.

### Phase C. Downstream reconstruction side lanes

These docs should be hardened after Phases A-B because they consume A-B.

1. `docs/gns_pipeline_blueprint.md`
2. `docs/wightman_uniqueness_blueprint.md`
3. `docs/r_to_e_blueprint.md`
4. `docs/bhw_permutation_blueprint.md`

Completion criterion for Phase C:

1. no theorem surface is still described as "should be possible once...";
2. SCV/nuclear inputs are named exactly;
3. no reverse-direction positivity argument quietly reuses a forward theorem;
4. uniqueness and permutation packages state exact dependency order.

### Phase D. Operator-algebra side backlog

These should be documented precisely, but remain lower priority than A-C.

1. `docs/vna_infrastructure_blueprint.md`
2. `docs/vna_triage.md`

Completion criterion for Phase D:

1. the Stone/spectral route is fixed at the theorem-package level;
2. predual/KMS/modular packages no longer blur foundational and consumer layers;
3. the first theorem to implement in each file is fixed.

## 4. File-by-file acceptance criteria

## 4.1. `theorem3_os_route_blueprint.md`

This doc is complete only when:

1. Package A through Package I each have fixed theorem names;
2. Package C is explicitly marked as false legacy infrastructure, not as a live
   theorem with an active proof strategy;
3. Package I is stated on the corrected Section 4.3 transformed-image theorem
   surface, with the transport codomain on the Section-4.3 half-space
   Schwartz side rather than either
   a support restriction `tsupport ⊆ PositiveEnergyRegion` or a false
   `DenseRange` claim in full `SchwartzNPoint d n`;
4. Package I has concrete theorem slots for the explicit `(4.19)`-`(4.20)`
   test-function transform, the transformed image, its half-space dense-range
   paper theorem, the transport map on that image, the quadratic identity
   there, and the final public closure theorem;
5. any surviving mention of Packages F/G/H is clearly marked as withdrawn /
   historical, not endorsed implementation guidance;
6. the exact legacy-consumer status after Package C is named;
7. the branch-`3b` support route is fixed at the concrete
   `PartialFourierSpatial.lean` companion-file level rather than the withdrawn
   abstract Schwartz-helper route;
8. the support-work checklist is satisfied literally.

## 4.2. `theorem2_locality_blueprint.md`

This doc is complete only when:

1. the continuity route is fixed on the flattened regular representation;
2. Route B is fixed as the primary geometry route;
3. Route A is documented as blocked-only fallback;
4. ET-support and open-edge theorem slots are fully named;
5. no section still treats continuity or geometry as abstract "candidate"
   choices.

## 4.3. `theorem4_cluster_blueprint.md`

This doc is complete only when:

1. theorem-3-to-one-factor extraction is spelled out through exact theorem
   names;
2. `normalizedZeroDegreeRightVector` has a literal definition and structural
   lemmas;
3. theorem-package names are fixed, not illustrative;
4. theorem 4 is visibly pure consumer work after theorem 3.

## 4.4. `general_k_continuation_blueprint.md`

This doc is complete only when:

1. every Chapter V / VI package has a fixed theorem-slot inventory;
2. the envelope/Malgrange-Zerner step is explicit and not a black box;
3. file boundaries and import order are fixed;
4. the SCV dependency surface is named exactly;
5. the trusted-vs-untrusted checklist is explicit.

## 4.5. `scv_infrastructure_blueprint.md`

This doc is complete only when:

1. the one-point forward-tube package has an explicit proof transcript;
2. the flattened regular constructor route is fixed;
3. Vladimirov-Tillmann and Bochner packages are split into real theorem
   packages;
4. no consumer doc needs to invent its own boundary-value constructor.

## 5. Audit queries that must return clean

Before declaring the proof docs complete, rerun searches like:

```text
rg -n "candidate route|if easiest|may shift|future theorem slot|primary route|fallback route|placeholder" docs/*.md
```

and manually justify every remaining hit.

Also rerun theorem-name cross-checks against the live code for:

1. theorem 2 consumer theorems,
2. theorem 3 consumer chain,
3. theorem 4 extraction theorems,
4. SCV one-point constructors,
5. GNS matrix-coefficient bridge dependencies.

## 6. Definition of done

The proof-doc stack is complete only when:

1. every active frontier theorem has one endorsed route;
2. every side-lane theorem package has fixed names or an explicitly quarantined
   blocked-only fallback;
3. the global docs (`sorry_triage.md`, `mathlib_gap_analysis.md`) agree with
   the per-theorem blueprints;
4. production work can proceed by proving named theorem packages rather than by
   making fresh mathematical choices.
5. every named external theorem is separated into source-backed content and any
   additional derived formalization obligation, with no derived obligation
   mislabeled as a verbatim paper theorem.
