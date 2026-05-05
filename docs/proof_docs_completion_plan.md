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

Current theorem-2 BHW correction: earlier text in these documents sometimes
used "fixed-`w` chamber route" for two different objects.  The common
fixed-`w` permuted-forward-tube gallery is rejected, because distinct ordinary
permuted forward-tube sectors are disjoint.  The reachable-label `hOrbit`
theorem `petOrbitChamberConnected_of_two_le` is weaker than that rejected
common-witness gallery, but it is still an additional pointwise
complex-Lorentz-orbit stratification theorem.  It is not the strict OS-paper
implementation gate for theorem 2.  Gemini Deep Research interaction
`v1_ChZjT1h1YWRpZUU1LThfdU1QMi1LRGVBEhZjT1h1YWRpZUU1LThfdU1QMi1LRGVB`
confirmed this theorem-shape correction: `hOrbit` should be documented as an
extra custom geometric theorem if pursued, while the faithful OS I §4.5 route
targets direct source-backed BHW single-valuedness on `S''_n`.

Current theorem-2 implementation ledger: the immediate Lean route is
selected-adjacent OS/Jost source data plus the source-backed BHW
single-valuedness packet on `S''_n`, not BHW/PET monodromy through `hOrbit`.
The next implementation gate is:

1. `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII`, built from
   the OS45 common-chart/EOW supplier and the Hall-Wightman scalar-product
   real-environment theorem;
2. the checked projection to
   `BHW.SourceDistributionalAdjacentTubeAnchor`;
3. checked local source support in `BHWPermutation/SourceExtension.lean`;
4. the direct source frontier
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
   followed by
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry`,
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry`, and the
   OS specialization `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.

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
   replacement is the source-backed Hall-Wightman/BHW compatibility theorem:
   selected adjacent OS/Jost data supply
   `BHW.SourceDistributionalAdjacentTubeAnchor`, and the source theorem proves
   single-valued continuation on `S''_n`.  The checked lower-layer BHW/PET
   monodromy interface remains useful conditional infrastructure, but the
   reachable-label `hOrbit` theorem is an extra pointwise orbit-stratification
   statement and is not the immediate theorem-2 implementation frontier.  The
   genuine remaining BHW geometry frontier is the scalar-product source
   overlap and cover-reaching proof in
   `BHWPermutation/SourceExtension.lean`;
   `BHWPermutation/PermutationFlow.lean` is still forbidden as a theorem-2
   source theorem because its current top-level BHW theorem depends on
   `IsLocallyCommutativeWeak`.
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
   `BHW.sourceDistributionalUniquenessSetOnVariety_mono`.  This OS-supplier
   Gram-environment layer is now checked in
   `BHWPermutation/SourceDistributionalUniqueness.lean` as
   `sourceDistributionalUniquenessSetOnVariety_of_open_jost_patch` and
   `exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch`: a
   nonempty open Jost patch has a Gram image which is a variety-level
   uniqueness environment.  The regular-stratum
   definitions themselves are now checked in Lean:
   `sourceGramExpectedDim`, `sourceConfigurationSpan`,
   `sourceComplexConfigurationSpan`, `SourceGramRegularAt`, and
   `SourceComplexGramRegularAt`, together with the concrete template
   `sourceFullSpanTemplate`.  The algebraic tangent support is also now
   checked in Lean: `sourceRealGramDifferential`,
   `sourceComplexGramDifferential`,
   `sourceRealMinkowskiGram_hasFDerivAt`,
   `contDiff_sourceRealMinkowskiGram`,
   `sourceSelectedGramCoord`, `sourceSelectedSymCoordSubspace`,
   `linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero`,
   `span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero`,
   `sourceRealGramDifferential_symm`,
   `sourceSelectedGramCoord_differential_mem`,
   `minkowskiInner_dualVectorOfLinearFunctional`,
   `exists_minkowski_dual_family_of_linearIndependent`,
   `exists_minkowski_dual_sourceRows_of_sourceRegularMinor_ne_zero`,
   `sourceRealGramDifferential_apply_eq_minkowskiInner`,
   `minkowskiInner_sum_smul_dual_left`,
   `sourceMinkowskiInner_sum_smul_left`,
   `sourceMinkowskiInner_sum_smul_right`,
   `sourceMinkowskiInner_add_right`,
   `sourceMinkowskiInner_smul_right`,
   `sourceMinkowskiInner_left_nonDegenerate`,
   `sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family`,
   `sourceSelectedGramCoord_comp_differential_range_eq`,
   `sourceRows_coefficients_of_sourceRegularMinor_ne_zero`,
   `sourceRealMinkowskiGram_apply_eq_minkowskiInner`,
   `sourceSelectedIndex_surjective_of_le`,
   `sourceSelectedRows_span_top_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero`,
   `sourceRealGramMap_constant_on_selectedVerticalFibers`,
   `sourceRealGramDifferential_eq_zero_of_selectedGramCoord_eq_zero`,
   `sourceSelectedGramCoord_injective_on_differential_range`,
   `sourceSelectedGramDifferentialToSym`,
   `sourceSelectedRealGramMap`,
   `sourceSelectedRealGramMap_hasStrictFDerivAt`,
   `sourceSelectedGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedGramDifferentialToSym_ker_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedRealGramMap_implicit_chart_of_nonzero_minor`,
   `sourceSelectedUpperPair`, `sourceSelectedSkewCoord`,
   `sourceSelectedSkewCoord_ker`, `sourceSelectedSkewCoord_surjective`,
   `card_sourceSelectedUpperPair`, `finrank_sourceSelectedSymCoordSubspace`,
   `sourceRealGramDifferential_rank_of_exists_nonzero_minor`,
   `sourceRealGramDifferential_rank_of_regular`,
   `sourceComplex_regular_of_real_regular`,
   `sourceComplexGramDifferential_realEmbed`,
   `sourceRealGramTangentSpaceAt`, `sourceComplexGramTangentSpaceAt`,
   `SourceComplexifiedRealTangentEqualsComplexTangent`, and
   `IsHWRealEnvironment`.  The tangent-complexification support theorem
   `sourceComplexGramDifferential_realEmbed_range_eq_complex_span` is now
   checked too: at a real source point, the complex differential range is the
   complex span of the real differential range.  The maximal-totally-real
   tangent packet is now checked in
   `BHWPermutation/SourceComplexTangent.lean`: it proves the easy tangent
   inclusions, complex selected-row span transfer, shared real coefficient
   expansion, selected Schur-complement differential formula, complex selected
   differential surjectivity by real/imaginary splitting, the hard theorem
   `sourceComplexGramTangent_subset_realEmbed_range_of_regular`, and
   `sourceComplexifiedRealTangentEqualsComplexTangent_of_regular`.  The local
   Hall-Wightman real-environment supplier
   `sourceRealGramMap_realEnvironmentAt_of_regular` is also checked: it shrinks
   a prescribed source neighborhood by `JostSet`, uses the checked relative-open
   source Gram image theorem, and fills `IsHWRealEnvironment` with Jost
   realizers and the new maximal-totally-real tangent theorem.  The
   regular-locus
   template/minor support is now
   checked too: `sourceTemplateDomainIndex`, `sourceTemplateCoordIndex`,
   `sourceTemplateDomainIndex_injective`,
   `sourceTemplateCoordIndex_injective`,
   `sourceFullSpanTemplate_basisVector`,
   `linearIndependent_sourceFullSpanTemplate_basisBlock`,
   `sourceFullSpanTemplate_regular`, `sourceRegularMinor`,
   `continuous_sourceRegularMinor`,
   `exists_nonzero_coordinate_minor_of_linearIndependent`,
   `sourceGramRegularAt_of_exists_nonzero_minor`,
   `exists_nonzero_minor_of_sourceGramRegularAt`, and
   `sourceGramRegularAt_iff_exists_nonzero_minor`, plus openness of the
   regular locus as `isOpen_sourceGramRegularAt` and the canonical template
   minor facts `sourceFullSpanTemplate_regularMinor_eq_one` and
   `sourceFullSpanTemplate_regularMinor_ne_zero`, plus the determinant-line
   density package `sourceCanonicalRegularMinorLinePolynomial`,
   `sourceCanonicalRegularMinorLinePolynomial_leadingCoeff`,
   `sourceCanonicalRegularMinorLinePolynomial_ne_zero`,
   `sourceCanonicalRegularMinorLinePolynomial_eval`,
   `sourceCanonicalRegularMinor_nonzero_dense`, and
   `dense_sourceGramRegularAt`.  The post-cleanup rank-stage support now lives
   in the small companion module `BHWPermutation/SourceRegularRank.lean`,
   rather than further growing `SourceExtension.lean`.  The theorem-2
   blueprint also gives proof skeletons for the three supplier facts:
   maximal-span density/open regular locus via determinant minors, regular
   Gram-map rank/local real-environment via the explicit selected-coordinate
   rank theorem and a selected-coordinate constant-rank chart for the finite
   source Gram map, and Hall-Wightman real-environment uniqueness via local
   maximal-totally-real selected-coordinate charts plus analytic continuation on
   the irreducible scalar-product variety.  These supplier facts are now
   checked and consumed by the open-Jost-patch uniqueness theorem.  The analytic
   bookkeeping lemma `SourceVarietyHolomorphicOn.sub` is now checked in
   `SourceExtension.lean`.  The complex selected-coordinate local-IFT substrate
   is also checked in `SourceComplexChart.lean`
   (`contDiff_sourceMinkowskiGram`,
   `sourceMinkowskiGram_hasFDerivAt`,
   `sourceSelectedComplexSymCoordSubspace`,
   `sourceSelectedComplexGramDifferentialToSym`,
   `sourceSelectedComplexGramMap`,
   `sourceSelectedComplexGramMap_hasStrictFDerivAt`,
   `sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedComplexGramMap_implicit_chart_of_nonzero_minor`,
   `sourceSelectedSymCoordKey`,
   `sourceSelectedComplexSymCoordKeyEquiv`,
   `sourceSelectedRealSymCoordKeyEquiv`,
   `sourceSelectedSymCoordRealComplexify`,
   `sourceSelectedComplexSymCoordKeyEquiv_real_slice`,
   `sourceSelectedComplexSymCoordFinEquiv`,
   `sourceSelectedRealSymCoordFinEquiv`,
   `sourceSelectedComplexSymCoordFinEquiv_real_slice`,
   `sourceComplexRegularMinor`,
   `continuous_sourceComplexRegularMinor`,
   `sourceComplexRegularMinor_realEmbed`,
   `exists_nonzero_complex_coordinate_minor_of_linearIndependent`,
   `sourceComplexGramRegularAt_of_exists_nonzero_minor`,
   `exists_nonzero_minor_of_sourceComplexGramRegularAt`,
   `sourceComplexGramRegularAt_iff_exists_nonzero_minor`,
   `isOpen_sourceComplexGramRegularAt`,
   `linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero`,
   `span_sourceComplexRows_eq_sourceComplexConfigurationSpan_of_sourceComplexRegularMinor_ne_zero`,
   `sourceSelectedComplexRows_span_top_of_sourceComplexRegularMinor_ne_zero`,
   `sourceComplexStdBasis_sum`,
   `sourceComplexMinkowskiDualVectorOfLinearFunctional`,
   `sourceComplexMinkowskiInner_dualVectorOfLinearFunctional`,
   `exists_sourceComplexMinkowski_dual_family_of_linearIndependent`,
   `exists_sourceComplexMinkowski_dual_sourceRows_of_sourceComplexRegularMinor_ne_zero`,
   `sourceComplexMinkowskiInner_sum_smul_dual_left`,
   `sourceSelectedComplexGramCoord_comp_differential_range_eq_of_sourceComplexRegularMinor_ne_zero`,
   `sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero`,
   `sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor`,
   `sourceComplexRows_coefficients_of_sourceComplexRegularMinor_ne_zero`,
   `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop`,
   `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero`,
   `sourceComplexGramMap_constant_on_selectedVerticalFibers`,
   `sourceComplexGramMap_localRelOpenImage_in_open_of_complexRegular`,
   `sourceSelectedComplexRows_span_top_of_selectedComplexGramCoord_eq_regular`,
   `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety`,
   `sourceComplexGramMap_localRelOpenImage_in_open_of_realRegular`,
   `contDiff_sourceSelectedComplexGramMap_of_injective`,
   `sourceSelectedComplexGramKernelProjection`,
   `sourceSelectedComplexGramKernelProjection_apply_ker`,
   `sourceSelectedComplexGramProdMap`,
   `contDiff_sourceSelectedComplexGramProdMap`,
   `sourceSelectedComplexGramProdMap_hasFDerivAt`,
   `sourceSelectedComplexGramProdMap_fderiv`,
   `sourceSelectedComplexGramProdMap_base_fderiv_isInvertible`,
   `sourceSelectedComplexGramProdMap_local_invertible_nhds`,
   `sourceSelectedComplexGramImplicitChart`,
   `sourceSelectedComplexGramImplicitChart_apply`,
   `sourceSelectedComplexGramImplicitChart_mem_source`,
   `sourceSelectedComplexGramImplicitChart_self`,
   `sourceSelectedComplexZeroKernelTargetCLM`,
   `sourceSelectedComplexZeroKernelTargetCLM_apply`,
   `sourceSelectedComplexGramZeroSection_differentiableOn`,
   `sourceSelectedComplexGramZeroSection_selectedGram`,
   `sourceSelectedComplexGramZeroSection_base`,
   `sourceSelectedComplexGramFlatCoordCLM`,
   `sourceSelectedComplexGramFlatCoordCLM_apply`,
   `sourceSelectedComplexGramFlatCoordCLM_source`,
   `sourceSelectedComplexGramCoord_eq_of_flatCoord_eq`,
   `sourceSelectedComplexGramZeroSection_image_eq_flatCoord_preimage`,
   `sourceSelectedComplexGramZeroSection_image_relOpen`,
   `sourceSelectedComplexGramZeroSection_gram_differentiableOn`,
   `exists_sourceSelectedComplexGramZeroSection_good_ball`,
   `sourceSelectedComplexSymCoordFinEquiv_symm_real_slice`,
   `sourceSelectedRealGramImplicitChart`,
   `sourceSelectedRealGramImplicitChart_mem_source`,
   `sourceSelectedRealGramImplicitChart_self`,
   `sourceSelectedRealGramImplicitChart_fst`,
   `sourceSelectedRealZeroKernelTargetCLM`,
   `sourceSelectedRealZeroKernelTargetCLM_apply`,
   `sourceSelectedRealGramZeroSection_selectedGram`,
   `sourceSelectedRealGramZeroSection_base`,
   `sourceSelectedRealGramZeroSection_continuousOn`,
   `sourceSelectedComplexGramZeroSection_real_slice_gram`,
   `exists_sourceSelectedRealGramZeroSection_good_ball`,
   `sourceSelectedComplexGramBaseCoord_real_slice`,
   `sourceComplexGramVariety_selectedChart_of_realRegular`,
   `SourceVarietyHolomorphicOn.comp_differentiableOn_chart`,
   and `sourceVariety_localChart_totallyReal_zero`,
   all sorry-free).  The global identity support has started with the checked
   Minkowski-to-dot reduction
   `complexMinkowskiToDotLinearEquiv`,
   `sourceComplexMinkowskiInner_eq_dot_after_equiv`,
   `sourceMinkowskiGram_eq_dotGram_after_equiv`, and
   `sourceComplexGramVariety_eq_dotGram_range` in
   `BHWPermutation/SourceComplexGlobalIdentity.lean`.  The remaining
   symmetric-space definitions and inclusions
   `sourceSymmetricMatrixSpace`, `sourceMatrixMinor`,
   `sourceSymmetricRankLEVariety`, `sourceComplexDotGram_symm`,
   `sourceComplexDotGram_mem_sourceSymmetricMatrixSpace`, and
   `sourceComplexGramVariety_subset_sourceSymmetricMatrixSpace` are checked
   there too.  The determinant/minor forward inclusion is now checked as
   `sourceComplexDotGram_minor_eq_zero`,
   `sourceComplexDotGram_mem_sourceSymmetricRankLEVariety`, and
   `sourceComplexGramVariety_subset_sourceSymmetricRankLEVariety`; the next
   diagonal square-root substep is checked as `complexSquareRootChoice`,
   `complexSquareRootChoice_mul_self`, and
   `sourceComplexDiagonal_factorization_self`.  The orthogonal-diagonalization
   spine is now also checked as `bilinform_orthogonal_basis_expansion`,
   `sourceMatrix_toBilin_isSymm`,
   `sourceSymmetricMatrix_exists_orthogonal_coordinate_expansion`,
   `sourceSymmetricMatrix_factorization_finrank`, and
   `sourceSymmetricMatrix_factorization_self`.  This proves the unrestricted
   complex symmetric `Z = A * Aᵀ` factorization in `n` coordinates.  The
   rank-compression theorem is now checked as
   `complex_symmetric_matrix_factorization_of_rank_le`, and the rank-defined
   reverse inclusion into the source variety is checked as
   `sourceComplexGramVariety_mem_of_symmetric_rank_le`.  The minor-to-rank
   bridge is now checked as `sourceMatrix_rank_le_of_minors_eq_zero`, with
   row/column extraction support
   `exists_linearIndependent_rows_of_rank_ge` and
   `exists_nondegenerate_square_submatrix_of_rank_ge`.  The converse rank-to-
   minor direction and rank-stratum API are checked as
   `matrix_rank_ge_of_nondegenerate_square_submatrix`,
   `sourceMatrix_minors_eq_zero_of_rank_le`,
   `sourceSymmetricRankLEVariety_eq_rank_le`,
   `sourceSymmetricRankExactStratum`, and
   `sourceSymmetricRankExactStratum_subset_rankLE`, with the positive-rank
   difference characterization
   `sourceSymmetricRankExactStratum_eq_rankLE_diff`.  Thus the full algebraic
   identification is checked as
   `sourceComplexGramVariety_eq_rank_le`, with stratum inclusion
   `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety` also
   checked.  The closedness/regular-locus topology needed for the singular
   closure stage is now also checked:
   `continuous_sourceMatrixMinor`, `isClosed_sourceSymmetricMatrixSpace`,
   `isClosed_sourceSymmetricRankLEVariety`,
   `isClosed_sourceComplexGramVariety`,
   `sourceComplexGramVariety_diff_lowerRank_eq_rankExact`, and
   `sourceSymmetricRankExactStratum_relOpenIn_sourceComplexGramVariety`.  The
   first Schur-complement regular-patch obstruction is checked as
   `matrix_rank_ge_card_of_nondegenerate_square_submatrix` and
   `schur_complement_entry_eq_zero_of_rank_le`: on an invertible principal
   block, rank at most the block size forces every Schur-complement entry to
   vanish.  The converse graph-to-rank half is checked as
   `rank_fromBlocks_zero₂₂_le_card_left` and
   `rank_fromBlocks_le_of_schur_complement_eq_zero`: Schur-complement zero
   forces rank at most the principal-block size via mathlib's LDU
   factorization and elementary row-span rank control of `fromBlocks A 0 0 0`.
   The arbitrary-coordinate packaging is checked as
   `toBlocks₂₁_eq_transpose_toBlocks₁₂_of_symm`,
	   `schur_complement_entry_eq_zero_of_rank_le_reindex`, and
	   `rank_le_of_reindexed_schur_complement_eq_zero`, transporting the canonical
	   Schur equivalence through `Matrix.reindex` for any equivalence
	   `ι ≃ r ⊕ q`.  The principal-patch graph characterization is now checked in
	   `BHWPermutation/SourceComplexSchurPatch.lean` as
	   `rank_eq_card_iff_reindexed_schur_complement_eq_zero`,
	   `sourceSymmetricRankExactStratum_iff_reindexed_schur_complement_eq_zero`,
	   and `sourceComplexGramVariety_iff_reindexed_schur_complement_eq_zero`:
	   on an invertible selected principal block of size `d + 1`, membership in
	   the source complex Gram variety is exactly symmetry plus vanishing
	   Schur complement.  This is the local graph model needed for the
	   Hall-Wightman regular-rank stratum, not a wrapper around the identity
	   theorem.  The rectangular all-minor implementation cover is also checked
	   in the same file: `reindexedRectSchurComplement`,
	   `rank_fromBlocks_zero₂₂_le_card_left_rect`,
	   `schur_complement_entry_eq_zero_of_rank_le_rect`,
	   `rank_fromBlocks_le_of_schur_complement_eq_zero_rect`,
	   `rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero`,
	   `sourceSymmetricRankExactStratum_iff_reindexed_rect_schur_complement_eq_zero`,
	   and `sourceComplexGramVariety_iff_reindexed_rect_schur_complement_eq_zero`.
	   This lets the regular-stratum cover use the already checked arbitrary
	   nonzero-minor extraction, while the principal-patch theorem remains the
	   Hall-Wightman-facing specialization.  The selected-minor complement
	   packaging is also checked as `selectedIndexComplement`,
	   `selectedIndexSumEquiv`, `selectedIndexSumEquiv_apply_selected`,
	   `selectedIndexSumEquiv_toBlocks₁₁`,
	   `isUnit_selectedIndexSumEquiv_toBlocks₁₁_det`, and
	   `sourceComplexGramVariety_iff_selected_rect_schur_complement_eq_zero`.
	   Thus an actual nonzero minor `sourceMatrixMinor n (d+1) I J Z ≠ 0`
	   directly produces the rectangular Schur chart of the source Gram variety.
	   The cover extraction is now checked as
	   `sourceMatrixMinor_ne_zero_left_injective`,
	   `sourceMatrixMinor_ne_zero_right_injective`,
	   `exists_sourceMatrixMinor_ne_zero_of_sourceSymmetricRankExactStratum`,
	   `exists_selected_rect_schur_chart_of_sourceSymmetricRankExactStratum`,
	   and
	   `exists_selected_rect_schur_chart_of_sourceComplexGramVariety_rankExact`:
	   every rank-exact point yields injective selected row/column maps, a
	   nonzero selected minor, and the selected Schur graph equivalence for the
	   source complex Gram variety on the resulting patch.  The corresponding
	   topology is checked as `isOpen_sourceMatrixMinor_ne_zero`,
	   `sourceMatrixMinor_ne_zero_relOpenInSourceComplexGramVariety`, and
	   `sourceComplexGramVariety_regularSelectedMinorPatch_relOpen`: selected
	   determinant-nonzero patches, and their intersections with the regular
	   rank-`d+1` stratum, are relatively open in the source complex Gram
	   variety.  The selected-chart dimension count is checked in the new small
	   companion `BHWPermutation/SourceComplexDimension.lean` as
	   `finrank_sourceSelectedComplexSymCoordSubspace`: the selected complex
	   symmetric-coordinate subspace has finrank
	   `n*m - m*(m-1)/2`, using the existing real dimension theorem and the
	   checked real/complex coordinate-key equivalences.  The same companion
	   now carries the lower-rank codimension arithmetic:
	   `sourceRankExactChartDim_sub_previous` proves the paper formula
	   `dim(rankExact D) - dim(rankExact (D-1)) = n-D+1`, and
	   `finrank_sourceSelectedComplexSymCoordSubspace_lowerRankCodim_ge_two`
	   gives codimension at least two in the singular case `D < n`.  The
	   complex source-density packet is now checked too in
	   `BHWPermutation/SourceComplexDensity.lean`: it complexifies
	   `sourceFullSpanTemplate`, uses the determinant polynomial of the
	   canonical regular minor along
	   `z + t • sourceComplexFullSpanTemplate d n`, and proves
	   `dense_sourceComplexGramRegularAt`.  The next implementation target in
	   that companion is now Lean-ready: under the necessary hard-range
	   hypothesis `d + 1 <= n`, a nonzero complex regular source minor makes the
	   selected Gram rows linearly independent; row-rank comparison gives
	   `d + 1 <= rank(sourceMinkowskiGram d n z)`, and the checked
	   `sourceComplexGramVariety_eq_rank_le` upper bound upgrades every regular
	   source Gram matrix to membership in
	   `sourceSymmetricRankExactStratum n (d + 1)`.  The immediate density
	   corollary is also Lean-ready: for any point of the source complex Gram
	   variety and any ambient open neighborhood, choose a source realization,
	   pull the neighborhood back along the continuous Gram map, use
	   `dense_sourceComplexGramRegularAt`, and push the chosen regular source
	   point forward with the rank-exact bridge.  Closedness of
	   `sourceComplexGramVariety d n` and
	   `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety` then
	   give
	   `closure (sourceSymmetricRankExactStratum n (d + 1)) =
	    sourceComplexGramVariety d n`.  The consumer corollary is now pinned:
	   every nonempty relatively open subset of `sourceComplexGramVariety d n`
	   meets `sourceSymmetricRankExactStratum n (d + 1)`, obtained by applying
	   `mem_closure_iff` to the ambient-open representative of the relatively
	   open set.  The checked consumer upgrades this to relative
	   density inside each relatively open source-variety domain `U`, and then
	   proves the pure continuity-extension lemma: if a continuous scalar-product
	   representative on `U` vanishes on
	   `U ∩ sourceSymmetricRankExactStratum n (d + 1)`, it vanishes on all of
	   `U`.  The production `SourceVarietyHolomorphicOn` hypothesis now also
	   exposes `ContinuousOn` by local ambient differentiability through the
	   checked `SourceVarietyHolomorphicOn.continuousOn`, so the
	   continuity-extension lemma applies directly to theorem-2 representatives.
	   The easy-arity algebraic reduction is now pinned next: when
	   `n <= d + 1`, `sourceComplexGramVariety d n` equals
	   `sourceSymmetricMatrixSpace n`, since the rank bound in
	   `sourceComplexGramVariety_eq_rank_le` is automatic.
	   The full symmetric affine coordinate model for this easy branch is now
	   checked too: `sourceFullSymCoordMapCLM`,
	   `sourceFullSymCoordMap_mem_sourceSymmetricMatrixSpace`,
	   `continuous_sourceFullSymCoordMap`,
	   `differentiable_sourceFullSymCoordMap`,
	   `sourceSymmetricMatrixSpace_eq_range_sourceFullSymCoordMap`, and
	   `isOpen_sourceFullSymCoordMap_preimage_of_relOpen_of_le` identify the
	   symmetric affine space with selected symmetric coordinates and turn
	   relatively open easy-branch source-variety domains into honest open
	   finite-dimensional complex coordinate domains.  The connectedness
	   transport is now checked as
	   `isConnected_sourceFullSymCoordMap_preimage_of_relOpen_of_le`, using the
	   inverse coordinate map on the subtype `U`.  The easy-branch identity
	   theorem itself is now checked as
	   `sourceComplexGramVariety_identity_principle_easy`: it applies the
	   ordinary SCV identity theorem to `H ∘ sourceFullSymCoordMap n` on the
	   open connected coordinate domain and pushes equality back to `U`.  The
	   final global theorem is now checked as the intended short arity split:
	   use this checked easy theorem when `n <= d + 1`; when `d + 1 < n`, use
	   the checked regular-rank-stratum identity theorem and then invoke the
	   already checked rank-exact density/continuity extension.
	   The theorem-2 blueprint separates the strict branch into two genuine
	   packets: the local identity propagation packet, using the checked BHW
	   selected complex Gram chart / local image infrastructure rather than a new
	   Schur-wrapper layer, and the connected-regular-locus theorem for connected
	   relatively open subsets of the irreducible normal symmetric rank-bounded
	   variety.  Both are now checked.  This is the Hall-Wightman
	   irreducibility/normality content; it is not a corollary of density alone.
	   A principal-minor Schur cover is mathematically valid over `ℂ` and is the
	   route now used for the singular local-basis branch, via the checked
	   nonzero-principal-minor cover theorem.  The first algebraic bridge on this route is
	   now checked in `BHWPermutation/SourceComplexDensity.lean`:
	   `sourceMinkowskiGram_rank_le_sourceComplexConfigurationSpan_finrank` and
	   `sourceSymmetricRankExactStratum_exists_complexRegular_realization`.
	   The local complex-regular image packet is also checked there as
	   `sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`,
	   giving the connected source ball and relatively open rank-exact image
	   needed for the local identity-propagation theorem.  The pullback helper
	   `SourceVarietyHolomorphicOn.comp_sourceMinkowskiGram` and the local
	   propagation theorem
	   `sourceComplexGramVariety_rankExact_local_identity_near_point` are now
	   checked as well.  The conditional global propagation theorem
	   `sourceComplexGramVariety_rankExact_identity_principle_of_connected` is
	   now checked too: from connectedness of
	   `U ∩ sourceSymmetricRankExactStratum n (d + 1)`, it proves the full
	   rank-exact identity principle by a nonempty clopen zero-patch argument;
	   `sourceComplexGramVariety_identity_principle_of_connected_rankExact` then
	   extends the result to all of `U` via the checked dense-rank-exact
	   continuity theorem.  The strict source-side blocker was the global
	   connected regular-locus theorem; it is now checked, as are local
	   Schur/chart propagation, identity-principle assembly, and dense-extension
	   assembly.  The theorem-2 blueprint refines this global theorem into a
	   checked strict connectedness packet: the pure topological assembly
	   lemma
	   `sourceComplexGramVariety_rankExact_inter_relOpen_isConnected_of_local_basis`
	   is now checked.  The packet it reduced to has now also been closed: the
	   source-specific local connected rank-exact basis theorem, the connected
	   regular local-image strengthening, and the connected rank-exact cone lemma
	   are all checked.  The principal minor support lemma for symmetric matrices is
	   now checked in `BHWPermutation/SourceComplexSchurPatch.lean`; it uses
	   the checked complex symmetric rank factorization to turn a full-rank row
	   minor of `A` in `Z = A Aᵀ` into a nonzero principal minor of `Z`.
	   The Schur-complement rank-additivity theorem for singular
	   principal blocks is now checked in
	   `BHWPermutation/SourceComplexSchurPatch.lean`, together with direct
	   source-rank `≤` and exact-rank Schur consequences.  The hard mathematical
	   proof was the source local-basis theorem, i.e. Hall-Wightman's local
	   irreducibility/normality of the symmetric scalar-product determinantal
	   variety; it is now checked by genuine Schur product charts plus the
	   connected rank-exact cone lemma, with no zero-Schur wrapper hiding the
	   lower-rank singular case.  The cone lemma is proved through real
	   finite-dimensional content: nonzero scalar rank invariance, cone
	   invariance of `sourceSymmetricRankExactStratum`, dot-Gram scaling,
	   path-connectedness of the full-rank complex source-configuration
	   Stiefel space using `MatrixLieGroup.GL_isPathConnected`, and the
	   small-ball radial contraction argument.  The implementation should not
	   cite "rank-exact cone connectedness" as an opaque geometric black box.
	   The first cone support file is now checked as
	   `BHWPermutation/SourceComplexCone.lean`: it proves scalar rank
	   invariance, exact-stratum cone invariance, dot-Gram scaling, the
	   full-rank configuration predicate, the selected/standard coordinate
	   frames and their full-rank membership, left/right determinant-unit action
	   invariance for full-rank configurations, the corresponding left/right
	   `GL` path-joining lemmas, existence of a nonzero selected row minor for
	   every full-rank configuration, the selected-minor contraction to the
	   coordinate frame, the selected-frame-to-standard-frame path, full
	   Stiefel-space path-connectedness, continuity of the dot-Gram map, the
	   map from full-rank configurations to the exact stratum, the
	   exact-stratum full-rank dot-Gram representative theorem, the image
	   equality for the exact stratum, and path-connectedness of the exact
	   symmetric rank stratum.  It now also checks the radial endpoint paths
	   inside centered balls, the compact norm bound for an arbitrary path, the
	   scaled middle path, the path-connectedness of
	   `Metric.ball 0 ε ∩ sourceSymmetricRankExactStratum m r` for every
	   `r ≤ m`, and the final neighborhood form
	   `sourceSymmetricRankExactCone_small_connected`.  The cone blocker is
	   therefore closed.  The blueprint now spells out the next singular
	   Schur-product implementation packet.  Its first production layer is now
	   checked in `BHWPermutation/SourceComplexSchurGraph.lean`: the principal
	   Schur graph `sourcePrincipalSchurGraph`, its block-recovery and
	   Schur-complement recovery lemmas, symmetry of the graph, and the
	   rank-`≤`/rank-exact graph equivalences using the checked principal Schur
	   rank theorem.  The cone theorem has also been transported to arbitrary
	   finite complement index types in
	   `BHWPermutation/SourceComplexConeTransport.lean`, so the Schur complement
	   coordinate no longer has a `Fin`-only type mismatch.  The singular
	   local-basis work is now checked: it constructs the product neighborhood
	   around a lower-rank point and proves the final continuous-image
	   connectedness argument feeding
	   `sourceComplexGramVariety_local_rankExact_connected_basis`.  This is
	   genuine Hall-Wightman finite-dimensional geometry, not a wrapper around
	   the local-basis theorem.  The determinant-unit inverse-continuity lemma
	   `continuousOn_matrix_inv_of_isUnit_det` is now checked in
	   `SourceComplexSchurGraph.lean`; the graph-continuity theorem
	   `continuousOn_sourcePrincipalSchurGraph` is now checked there as well,
	   with a coordinatewise proof expanding only the finite lower-right
	   Schur term.  The product-neighborhood extraction theorem
	   `exists_sourcePrincipalSchurGraph_product_subset_open` is now checked:
	   from an open ambient neighborhood `N0` of the graph point it returns open
	   `A`, `B`, and `S` neighborhoods whose whole graph image lies in `N0`, with
	   the `A` neighborhood contained in the determinant-unit locus.  The
	   graph-image connectedness theorem
	   `isConnected_sourcePrincipalSchurGraph_rankExact_image` and the
	   rank-exact image-subset theorem
	   `sourcePrincipalSchurGraph_rankExact_image_subset` are now checked too.
	   The `A`-factor local topology is now checked through
	   `isOpen_matrix_det_isUnit`, `exists_pos_ball_subset_isUnit_det`, and
	   `isConnected_symmetric_matrix_ball`; these use the concrete Frobenius
	   matrix norm scope for finite-dimensional matrix balls.  The rectangular
	   `B`-factor ball connectedness is now checked as `isConnected_matrix_ball`.
	   The Schur-coordinate continuity needed for relative openness is now
	   checked too:
	   `continuousOn_principalBlock_invEntry` and
	   `continuousOn_reindexedPrincipalSchurComplement`.
	   The finite matrix lemma `matrix_eq_zero_of_rank_eq_zero` is checked, so
	   the singular basepoint Schur complement can be converted from rank zero
	   to the zero matrix after Schur rank additivity.
	   The Schur chart inverse-coordinate equality
	   `sourcePrincipalSchurGraph_coordinates_eq_of_symmetric` is now checked:
	   a symmetric matrix on a determinant-unit principal patch is exactly the
	   graph of its principal block, rectangular block, and Schur-complement
	   coordinate.  This supplies the forward inclusion needed for the final
	   equality between `V ∩ rankExact` and the Schur graph image.
	   The coordinate symmetry lemmas
	   `principalBlock_transpose_eq_of_symmetric` and
	   `reindexedRectSchurComplement_transpose_eq_of_symmetric` are also checked,
	   so a symmetric source matrix lands in the symmetric `A` and `S` factors of
	   the singular product chart.
	   The ambient Schur-coordinate openness theorem
	   `isOpen_sourcePrincipalSchurCoordinatePatch` is now checked too: open
	   conditions on `N0`, the principal block, rectangular block, and
	   Schur-complement coordinate cut out an open determinant-unit patch in the
	   ambient matrix space.  The final relative-open chart is therefore exactly
	   this patch intersected with `sourceComplexGramVariety d n`.
	   The exact graph-image equality
	   `sourcePrincipalSchurGraph_rankExact_image_eq_coordinatePatch` is now
	   checked: once the parameter product has been shrunk so its graph lies in
	   the requested ambient neighborhood `N0`, the rank-exact part of the Schur
	   coordinate patch is precisely the graph image of
	   `Aset × Bset × (Sset ∩ rankExact)`.
	   The open-coordinate variant
	   `sourcePrincipalSchurGraph_rankExact_image_eq_openCoordinatePatch` is now
	   checked as well, so the final local-basis proof can use the open `A`
	   neighborhood for relative openness and the symmetric `A` factor for
	   connectedness without redoing set algebra.
	   The singular topology target is now checked as
	   `sourceComplexGramVariety_local_rankExact_connected_basis_singular`: it
	   constructs the actual `Aset`, `Bset`, and `Sset` around a lower-rank
	   point and proves the final radius-shrinking and assembly for the singular
	   local-basis theorem.  The regular rank branch of that local-basis
	   theorem has also been tightened:
	   `sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`
	   now returns `IsConnected O` for the produced relatively open
	   rank-exact image, proved by showing that `O` is exactly the continuous
	   source-Gram image of the connected source ball.  The regular branch is
	   now checked as
	   `sourceComplexGramVariety_local_rankExact_connected_basis_regular`.
	   The full local-basis theorem is now checked as
	   `sourceComplexGramVariety_local_rankExact_connected_basis`, splitting
	   between the checked regular branch and checked singular Schur product-chart
	   branch.  This closes
	   `sourceComplexGramVariety_rankExact_inter_relOpen_isConnected`,
	   `sourceComplexGramVariety_rankExact_identity_principle`, and the final
	   `sourceComplexGramVariety_identity_principle` in
	   `BHWPermutation/SourceComplexDensity.lean`.
	   The pairwise
	   `sourceDistributionalUniquenessSetOnVariety_of_realEnvironment` proof is
	   now checked in `BHWPermutation/SourceDistributionalUniqueness.lean` as the
	   direct `H := Φ - Ψ` consumer, not a wrapper ladder.  Deep Research audit
   `v1_ChdsVFR2YVpiQUN0U1lfdU1Qa1pidjZBMBIXbFRUdmFaYkFDdFNZX3VNUGtaYnY2QTA`
   agrees with the rank-bounded-variety and irreducible-analytic-identity
   theorem shape, and flags the same hidden obligations: strong/local-ambient
   holomorphy, singular lower-rank handling, and analytic irreducibility of the
   source symmetric determinantal variety.  The blueprint now also records the
   needed complex symmetric rank factorization and warns that the source-space
   pullback shortcut is insufficient unless it proves the same irreducibility /
   monodromy content.  The local chart target is relative openness in
   the scalar-product variety; it is not the false affine claim that the Gram
   image contains an open subset of `G0 + range dG_x0`.  The algebraic
   selected-coordinate uniqueness step
   `sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero`
   and its chart consequence
   `sourceRealGramMap_constant_on_selectedVerticalFibers` are now checked.
   This replaces the earlier vertical-path/integration idea: on one fixed
   nonzero selected-minor chart, selected Gram coordinates determine the full
   Gram matrix, hence the selected implicit chart has full-Gram-constant
   vertical fibers after shrinking to the same minor chart.
   The next relative-open image step is now documented with the extra
   algebraic bridge that the chart proof genuinely needs:
   `sourceSelectedGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop`,
   `sourceSelectedRows_span_top_of_selectedGramCoord_eq_regular`, and
   `sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero_of_mem_variety`.
   These avoid the hidden false assumption that an arbitrary realization of a
   nearby Gram matrix in `sourceRealGramVariety d n` already lies in the same
   source minor chart; selected coordinates of one regular chart point must
   determine the whole Gram matrix for any realization in the variety.  This
   bridge, the open-neighborhood relative image theorem
   `sourceRealGramMap_localRelOpenImage_in_open_of_regular`, and its
   `V = Set.univ` corollary
   `sourceRealGramMap_localRelOpenImage_of_regular` are now checked in
   `BHWPermutation/SourceRegularRank.lean`.
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
   multi-variable integration constants are infinite-dimensional, and the
   final patching route has been sharpened further: derive `0 < m` from
   `C.Nonempty` and `0 ∉ C`, choose one global cone basis in `C`, use a
   fixed-basis local chart-window theorem at every edge point, transport each
   coordinate envelope back through the complex affine chart equivalence, and
   patch only after the fixed positive coordinate cone supplies common
   identity-theorem seeds on overlaps.  This rules out the per-point-basis
   shortcut that would leave overlap compatibility unjustified.  The false
   polynomial-correction shortcut is not used.  The checked
   real-mollification infrastructure in `SCV/LocalDistributionalEOW.lean`
   now supplies the checked regularized common-boundary extraction
   `SCV.localRealMollify_commonContinuousBoundary_of_clm`.  The nonzero-envelope
   recovery layer is also checked through the exact QFT-free substrate:
   `SCV.complexTranslateSchwartz`, `SCV.schwartzTensorProduct₂`,
   `SCV.realConvolutionTest`,
   `SCV.translationCovariantProductKernel_descends`,
   `SCV.distributionalHolomorphic_regular`,
   `SCV.regularizedEnvelope_productKernel_dbar_eq_zero`,
   `SCV.translationCovariantKernel_distributionalHolomorphic`,
   `SCV.regularizedEnvelope_holomorphicDistribution_from_productKernel`,
   `SCV.regularizedEnvelope_pointwiseRepresentation_of_productKernel`,
   `SCV.regularizedEnvelope_deltaLimit_agreesOnWedges`, and
   `SCV.regularizedEnvelope_chartEnvelope_from_productKernel`.  The remaining
   theorem-2 SCV work is upstream of that checked consumer: extract the local
   continuous EOW theorem and construct the regularized local EOW
   product-kernel family with the exact `K,G,hcov,hG_holo,hK_rep` fields.  The
   checked downstream consumer uses `bvt_F_acrOne_package` to prove vanishing.
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
   The first Euclidean moving-kernel layer for that Weyl route, including
   reflected support control, derivative commutation, first-order translation
   seminorm estimates, the pointwise quotient-derivative identity,
   compact-kernel continuity, Schwartz-topology difference-quotient
   convergence, and the one-parameter derivative theorem for reflected
   regularizations, is now checked in `SCV/EuclideanWeyl.lean`.  The next
   proof-doc/implementation frontier has advanced through the direction-uniform
   Fréchet remainder estimate, the scalar
   `hasFDerivAt_regularizedDistribution` theorem, and
   `contDiff_regularizedDistribution` in the new
   `SCV/EuclideanWeylFrechet.lean` companion file.  The checked ladder is
   recorded down to Lean pseudocode in `docs/scv_infrastructure_blueprint.md`:
   package `LineDeriv.bilinearLineDerivTwo ℝ φ` as
   `euclideanSecondLineDerivDirectionCLM`, expand the diagonal in the
   `EuclideanSpace.basisFun ι ℝ` basis, bound coordinates using
   `EuclideanSpace.norm_sq_eq` plus `Finset.single_le_sum`, apply a finite-sum
   seminorm triangle inequality to get
   `exists_seminorm_secondLineDeriv_unit_bound`, promote it to the translated
   second-derivative bound, obtain the uniform quotient and quadratic
   remainder estimates, and compose the resulting Schwartz-topology limit with
   the reflected functional, then close `ContDiff` by finite-order induction
   using `contDiff_succ_iff_hasFDerivAt` and `contDiff_clm_apply_iff`.  The
   normalized Euclidean bump substrate is now checked in
   `SCV/EuclideanWeylBump.lean`: normalized compact bumps, real-valued
   nonnegativity, support in `closedBall 0 ε`, and zero integral/compact
   support for differences.  The profile-scaling weighted-mass subpackage is
   now also checked in the same file, through Euclidean raw-integral scaling,
   one-variable weighted raw-mass scaling, and radius-independence of the
   normalized weighted mass.  The bump-subprofile support, plateau, and
   norm-equality facts are checked as well.  The first finite-interval radial
   Poisson substrate is now checked in `SCV/EuclideanWeylPoisson.lean`: radial
   mass and primitive definitions, the FTC derivative of radial mass, the
   global weighted-mass bridge from the checked `Ioi` mass to the finite ODE
   boundary condition, the near-zero mass formula, the linear primitive-derivative
   formula, the quadratic primitive profile at the origin, the away-from-zero
   radial ODE, the positive-radius scalar profile-Laplacian theorem, primitive
   vanishing outside the support radius, and the Euclidean origin
   smoothness/Laplacian theorem from the quadratic norm germ.  The off-origin
   Euclidean geometry layer is now checked through the cardinality/summation
   identities, the first Frechet derivative of the norm, the diagonal norm
   Hessian, the derivative of `y_i / ‖y‖`, the local first-derivative rewrite
   for `a ∘ ‖·‖`, the product-rule body of the radial second chain rule, the
	   off-origin profile Laplacian, the positive-half-line smoothness of the
	   radial primitive, the all-points theorem
	   `laplacian_radialPrimitiveProfile`, compact support and exact
	   topological-support radius of the norm-composed primitive, Schwartz
	   packaging, the positive-dimensional bump-difference primitive theorem
	   `exists_compact_laplacian_eq_euclideanWeylBump_sub_with_support`,
	   reflected-translate Laplacian commutation, and the harmonic bump
	   scale-invariance theorem `regularizedDistribution_bump_scale_eq`.  The
	   local ball-representative layer is now checked in
	   `SCV/EuclideanWeylRegularity.lean`: the half-margin and uniform-margin
	   closed-ball support lemmas, `euclideanWeylBallRepresentative`,
	   `euclideanWeylBallRepresentative_eq_regularized`,
	   `euclideanWeylBallRepresentative_eq_regularized_on_ball`,
	   `contDiffOn_euclideanWeylBallRepresentative`,
	   `euclideanConvolutionTest`, `euclideanConvolutionTest_apply`,
	   `euclideanConvolutionTest_apply_reflected`, and
	   `euclideanConvolutionTest_apply_reflectedTranslate`.  The remaining
	   Euclidean Weyl proof route now continues to the scalar
	   distribution-pairing identity and compact-support approximate-identity
	   representation assembly in `docs/scv_infrastructure_blueprint.md`.  The
	   pairing identity is now documented as a finite-probe/ordinary-Bochner
	   argument modelled on the checked `SCV/PaleyWiener.lean` probe
	   factorization, not as a forbidden `SchwartzMap`-valued Bochner integral.
	   The first probe slice is now explicit there and checked in
	   `SCV/EuclideanWeylProbe.lean`:
	   polynomial Euclidean weights, coordinate iterated line-derivative CLMs,
	   weighted bounded-continuous probes, the finite `euclideanProbeCLM`, and
	   the finite-dimensional domination theorem controlling
	   `SchwartzMap.seminorm` by those coordinate probes.  The Hahn-Banach
	   range factorization through this checked finite probe map is now checked
	   in the same file as
	   `euclideanSchwartzFunctional_exists_probe_factorization`, with the
	   supporting finite seminorm bound, probe-norm domination, kernel descent
	   to the probe range, and Hahn-Banach extension theorem all explicit.  The
	   componentwise Banach-valued probe integral identity and the compact-kernel
	   scalar pairing theorem are now checked in
	   `SCV/EuclideanWeylPairing.lean`: `euclideanPairingProbeFamily`,
	   compact-support integrability of that Banach-valued family,
	   `integral_euclideanPairingProbeFamily_eq_probe_convolution`, and
	   `regularizedDistribution_integral_pairing`.  The Euclidean
	   approximate-identity stage is now checked in
	   `SCV/EuclideanWeylApproxIdentity.lean`:
	   `euclideanConvolutionTest_apply_swap`,
	   `iteratedFDeriv_euclideanConvolutionTest_sub_eq_integral`,
	   `exists_weighted_iteratedFDeriv_euclideanTranslate_sub_le_linear`,
	   `tendsto_euclideanConvolutionTest_of_shrinking_normalized_support`, and
	   `exists_euclideanConvolutionTest_approxIdentity`.  The smaller-ball
	   representation theorem is now checked in
	   `SCV/EuclideanWeylRepresentation.lean` as
	   `euclidean_laplacian_distribution_regular_on_ball`, using the explicit
	   Weyl-bump sequence, scalar pairing, and constant-sequence limit
	   argument.  The next SCV subproblem is now the open-set representation
	   assembly.  The detailed route in
	   `docs/scv_infrastructure_blueprint.md` now uses the canonical Weyl ball
	   representative at each point and finite smooth partitions only on compact
	   test supports.  The remaining Lean work before the open theorem is:
	   support preservation for `χ * φ`, finite decomposition of a compactly
	   supported Schwartz test by partition functions, and the compact-support
	   integrability/finite-integral lemma for local continuous representatives.
	   These first prerequisites are now checked in
	   `SCV/EuclideanWeylOpen.lean`; the canonical-overlap lemma, smoothness of
	   the open representative, and finite compact `SmoothPartitionOfUnity`
	   bridge for `tsupport φ` are checked as well.  The ball-representation
	   theorem is now available in non-existential form as
	   `euclideanWeylBallRepresentative_represents_on_ball`.  The finite
	   summation identity and the full open-set theorem
	   `euclidean_weyl_laplacian_distribution_regular_on_open` are now checked
	   in `SCV/EuclideanWeylOpen.lean`.
	   Zero-dimensional bump-difference bookkeeping is only needed if a
	   dimension-free caller requires it.  The downstream complex-chart
	   holomorphic regularity layer is now checked in
	   `SCV/DistributionalEOWHolomorphic.lean`: the open-set Euclidean Weyl
	   theorem has been transported through `complexChartEuclideanCLE` as
	   `weyl_laplacian_distribution_regular_on_open`; the local fundamental
	   lemma for continuous-on-open functions tested against `SupportsInOpen`
	   Schwartz functions is checked; the real-smooth cutoff representative
	   with `dbar G = pointwiseDbar H` on `tsupport φ` is checked; distributional
	   `∂bar` holomorphy is converted to pointwise `pointwiseDbar = 0`; and the
	   finite-dimensional CR linear algebra now supplies
	   `differentiableOn_complex_of_contDiffOn_real_and_pointwiseDbar_zero`.
	   The final assembled theorem
	   `SCV.distributionalHolomorphic_regular` is checked with no new axioms or
	   sorrys.  The theorem-2 SCV frontier after Weyl/CR regularity moved to
	   regularized-envelope recovery, and that recovery layer is now checked
	   through the chart-assembly theorem below; the current frontier is local
	   continuous EOW extraction plus the upstream regularized-family/product-
	   kernel package.  The next small Lean bridge is now checked
	   as
	   `SCV.regularizedEnvelope_holomorphicDistribution_from_productKernel`:
	   combine product-kernel descent, the checked compact approximate identity,
	   the checked product-kernel `∂bar` consumer, and
	   `SCV.distributionalHolomorphic_regular` to obtain a holomorphic chart
	   representative for the descended distribution.  The delta-limit recovery
	   layer is now also checked in `SCV/DistributionalEOWKernelRecovery.lean`:
	   `eventually_translate_mem_open_of_shrinking_support`,
	   `integrable_continuousOn_realTranslate_mul_kernel`,
	   `regularizedEnvelope_difference_integral_identity_eventually`,
	   `regularizedEnvelope_kernelLimit_from_difference_integral`,
	   `regularizedEnvelope_kernelLimit_from_representation`,
	   `realMollifyLocal`, and
	   `regularizedEnvelope_deltaLimit_agreesOnWedges` together derive
	   `G (ψn n) z -> H z` from the actual representation integral and then
	   identify `H` with the plus/minus side functions by limit uniqueness.
	   The final checked SCV assembly theorem is now
	   `SCV.regularizedEnvelope_chartEnvelope_from_productKernel`: it applies
	   the checked product-kernel midpoint, derives the pointwise representation
	   of the recovered `H`, and then invokes the checked delta-limit wedge
	   agreement.  The remaining theorem-2 SCV frontier is therefore no longer
	   Weyl/regularity, the delta-limit estimate, or a free
	   pointwise-representation bridge; it is the local continuous EOW
	   extraction/patching and OS45 instantiation.  The bridge has been
	   decomposed and checked in `docs/scv_infrastructure_blueprint.md` through:
	   the now checked support theorem
	   `SCV.realConvolutionTest_supportsInOpen_of_translate_margin`, the now
	   checked continuity theorem
	   `SCV.continuousOn_realMollifyLocal_of_translate_margin`, the
	   checked compact-support Fubini/change-of-variables pairing theorem
	   `SCV.realConvolutionTest_pairing_eq_mollifier_pairing`, the checked
	   `SCV.regularizedEnvelope_pointwise_eq_of_test_integral_eq` endpoint, and
	   the checked supplier
	   `SCV.regularizedEnvelope_pointwiseRepresentation_of_productKernel`.
	   The first upstream regularized-family slice is now checked as well:
	   `SCV.localRealMollifySide_holomorphicOn_of_translate_margin` in
	   `SCV/LocalDistributionalEOW.lean`, proving local holomorphy of the
	   real-direction mollifier from the explicit support-translate margin.
	   The next boundary-extraction slice is also checked:
	   `SCV.regularizedBoundaryValue_continuousOn`,
	   `SCV.realMollifyLocal_eq_sliceIntegral_translate`,
	   `SCV.realMollifyLocal_eq_sliceFunctional`,
	   `SCV.exists_cutoffSliceIntegral_clm_of_continuousOn`,
	   `SCV.realMollifyLocal_eq_cutoffSliceCLM`,
	   `SCV.tendsto_cutoffSliceCLM_of_boundaryValue`,
	   `SCV.tendsto_mollified_boundary_of_clm`, and
	   `SCV.localRealMollify_commonContinuousBoundary_of_clm`.  These prove the
	   cutoff-local slice-CLM construction, evaluation of the cutoff CLM on the
	   translated mollifier kernel, convergence of those cutoff CLMs from the
	   raw distributional boundary-value hypothesis via
	   `SchwartzMap.smulLeftCLM`, and the Streater-Wightman regularized
		   common-boundary extraction.  The continuous-EOW extraction substrate is
		   now also public in `SCV/TubeDomainExtension.lean`:
		   `SCV.local_eow_extension` exposes the checked local Cauchy-polydisc
		   extension fields for global tube domains, and
		   `SCV.local_extensions_consistent` exposes the checked overlap
		   identity-theorem argument.  The local finite-dimensional geometry needed
		   to replace global tube membership is now checked in
		   `SCV/LocalContinuousEOW.lean`: the coefficient simplex, compact
		   chart-direction simplex, convex-cone inclusion, and positive-imaginary
		   normalization theorem
		   `SCV.localEOW_positive_imag_normalized_mem_simplex`.  The local
		   chart-membership replacements for the global `Phi_pos_in_tube` and
		   `Phi_neg_in_tube` steps are checked there as
		   `SCV.localEOW_chart_positive_polywedge_mem` and
		   `SCV.localEOW_chart_negative_polywedge_mem`, with the common-radius
		   two-sided package `SCV.localEOW_chart_twoSided_polywedge_mem`.  The
		   public chart-coordinate layer is checked as `SCV.localEOWRealChart`,
		   `SCV.localEOWChart`, `SCV.localEOWChart_real_imag`, and
		   `SCV.localEOWChart_twoSided_polywedge_mem`.  These are not yet the OS45
		   local-wedge theorem: the next SCV proof must splice these membership
		   lemmas into the same Cauchy-polydisc proof bodies for
		   `Ωplus`/`Ωminus`.  The remaining theorem-2 supplier
		   blocker is therefore the local
		   OS-II chart plumbing that feeds these checked SCV facts:
	   supply the plus/minus raw boundary hypotheses and the
	   cutoff-one/support-margin data in the documented
	   `sliceCLM_family_from_distributionalBoundary`, then package the resulting
	   common-boundary envelope for OS45.  This is not another distributional
	   EOW theorem and not a common-boundary wrapper.
	   The initial coordinate and trace-membership support
	   `BHW.configPermCLE`, `BHW.os45CommonChartCLE`,
	   `BHW.wickRotate_ordered_mem_acrOne`,
	   `BHW.adjacent_wick_traces_mem_acrOne`, and
	   `BHW.os45CommonChart_real_mem_pulledRealBranchDomain_pair`, together with
	   the direct-envelope packaging
	   `BHW.adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope`, is checked in
	   `OSToWightmanLocalityOS45CommonChart.lean` and
	   `OSToWightmanLocalityOS45TraceMembership.lean`.  This should now be read
	   as theorem-2 OS45 supplier plumbing, not as permission to redo
	   distributional EOW.  The pure SCV/distributional EOW infrastructure is an
	   existing input; the remaining theorem-2 task is to instantiate it in the
	   common OS45 chart and package the output as the concrete envelope consumed
	   by the checked direct-coordinate bridge.
	   The theorem-2 blueprint records the still-needed local supplier surfaces
	   `BHW.os45_adjacent_commonBoundaryEnvelope` and
	   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII`.  If the
	   implementation of
	   `SCV.local_distributional_edge_of_the_wedge_envelope` must be only a
	   QFT-free packaging of the checked local distributional-EOW machinery into
	   the exact local chart-envelope data needed here.  It must follow the
	   fixed-basis/complex-affine-transport route recorded in
	   `docs/scv_infrastructure_blueprint.md`; it is not a new theorem-2
	   assumption and not a replacement for the OS45 supplier.
	   `BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch`
	   supplies the Gram environment for that same `V`; and
	   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII` fills the
	   fields of `SelectedAdjacentDistributionalJostAnchorData` before the
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
   The compact-test-to-pointwise conversion, adjacent seed equality,
   source-variety holomorphy under Gram-coordinate permutation, and the
   real-environment uniqueness theorem
   `sourceScalarRepresentative_adjacent_eq_on_overlap_of_realEnvironment` are
   checked in Lean as sorry-free support lemmas.  The final PET branch
   transcript has been moved back to proof-doc status because it depends on
   the remaining Hall-Wightman source obligations: the scalar representative
   existence theorem and the direct source single-valuedness theorem on
   `S''_n`.  Those obligations must not appear as production `sorry`s on the
   active import path.
   The source-overlap openness half is now also checked:
   `sourceAdjacentPermutationGramOverlap_relOpen`
   and `gramEnvironment_complexify_mem_adjacentOverlap` are in production Lean.
   The later audit changed the status of the generic witness/cover package:
   the enlargement from local overlap components to the full adjacent double
   scalar-product domain is not a consequence of the local anchor fields alone.
   It is source-equivalent unless supplied by a genuine global
   Hall-Wightman/Araki reachability or source single-valuedness theorem.
   Therefore the package around
   `exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain`,
   `mem_sourceAdjacentSeedCover_of_mem_doubleDomain`,
   `sourceAdjacentSeedCover_cover_doubleDomain`, and
   `sourceDoublePermutationGramDomain_adjacent_chain` is retained only as an
   archived proof-doc decomposition, not as an active production target.
   The step-1 realization input for that archived witness theorem is already
   fixed at the checked Lean surface
   `exists_sourceExtendedTube_realizations_of_mem_doubleDomain`.
   The latest doc pass also aligns the permutation side with the actual repo
   API: use concrete swaps and `BHW.Fin.Perm.adjSwap_induction` as the Lean
   surface, and keep abstract adjacent-transposition predicates only at the
   normalization boundary.
   For theorem 2 to be 100% implementation-ready, the direct source theorem
   must not remain one compressed theorem surface.  The proof docs now expose:
   1. real-environment uniqueness on one adjacent scalar overlap component,
      which is checked in `SourceExtension.lean`;
   2. the archived witness/cover decomposition that would reduce global
      Hall-Wightman reachability to overlap components;
   3. adjacent-transposition word propagation to a general permutation.
   The theorem-2 blueprint now contains Lean-shaped theorem surfaces and proof
   transcripts for the archived package, but those surfaces are not production
   implementation targets until the global source input is supplied.  The
   archived supplier names are:
   `SourceAdjacentOverlapWitness`,
   the witness fields `overlap_relOpen`, `overlap_connected`, and
   `environment_mem_overlap`,
   `sourceAdjacentSeedCover`,
   `sourceAdjacentPermutationGramOverlap_subset_seedCover`,
   `sourceAdjacentSeedCover_eq_union`,
   `exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain`,
   `mem_sourceAdjacentSeedCover_of_mem_doubleDomain`,
   `sourceAdjacentOverlapIndex_reflTransGen`,
   `sourceAdjacentSeedCover_cover_doubleDomain`,
   `sourceDoublePermutationGramDomain_adjacent_chain`, and
   `exists_sourceExtendedTube_realizations_of_mem_doubleDomain`.
   The theorem-2 blueprint now also records the intended proof route for that
   archived package:
   the adjacent overlap is the connected component of a Hall-Wightman
   real-environment neighbourhood intersected with the adjacent double scalar
   domain; the seed cover is the union of those overlap components; the chain
   theorem comes from the cover-reaching theorem
   `sourceAdjacentSeedCover_cover_doubleDomain` together with connected-union
   propagation via `IsConnected.biUnion_of_reflTransGen`;
   the normalization step from an abstract `IsAdjacentTransposition τ` to a
   concrete `Equiv.swap i ⟨i.val + 1, hi⟩` is fixed; and the step-1 input to
   witness construction would be the checked realization theorem
   `exists_sourceExtendedTube_realizations_of_mem_doubleDomain`.  The archived
   adjacent-word package remains available only as a possible later internal
   decomposition if the direct Hall-Wightman global continuation route needs
   it, not as part of the active theorem-2 contract.
   One more theorem-shape correction is now explicit: the final overlap object
   for this route cannot honestly remain parameter-free in `(d,n,π,i,hi)`
   alone. Because it is defined from a chosen Hall-Wightman local
   neighbourhood around `hAnchor.gramEnvironment π i hi`, the final code-level
   surface must depend on that chosen neighbourhood data, directly or through a
   packaged witness derived from `hAnchor` (and possibly `hRep`). The current
   production parameter-free constant should therefore be treated only as a
   placeholder, not as the final mathematical API.
   The route decision is now explicit: this adjacent-word package is archived
   as a possible internal decomposition only.  The endorsed theorem-2 contract
   is instead the direct global Hall-Wightman continuation theorem on the
   scalar-product domain, with the checked local overlap/real-environment
   theorem (A) as local support.  This fixes the live route and quarantines the
   old word-chain detour; the remaining live source frontier is
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
   not a production `sorry` for the source-equivalent witness theorem.
   Deep Research interaction
   `v1_ChdYZXp1YWRLRUJZMjlzT0lQa1BtbXlRNBIXWGV6dWFkS0VCWTI5c09JUGtQbW15UTQ`
   agrees with the local audit: this witness theorem is too strong from an
   arbitrary `SourceDistributionalAdjacentTubeAnchor` alone.  The proof docs are
   implementation-ready only after the missing input is made explicit as either
   a global adjacent double-domain connectedness/reachability theorem or the
   direct Hall-Wightman source single-valuedness theorem on `S''_n`.
   More precisely, if the archived witness theorem is later revived, its proof
   docs must expose the Hall-Wightman local-neighbourhood selection step in
   Lean-shaped form:
   1. choose extended-tube realizations for `Z` and `τ · Z`;
   2. extract the relevant real boundary/environment data from those
      realizations;
   3. select a Hall-Wightman scalar-variety neighbourhood around that real
      data;
   4. identify the corresponding anchor label `π`;
   5. package the resulting connected overlap component as
      `SourceAdjacentOverlapWitness`.
   The correct active packaging remains two-stage:
   `SourceScalarRepresentativeData` is
   local branch data on `sourceExtendedTubeGramDomain d n`, while the global
   Hall-Wightman theorem on `M_n` / `S''_n` is the later continuation theorem
   for that branch.  The docs should not blur those two roles.
   After the latest source audit, the docs no longer treat connectedness of
   the full adjacent double scalar-product domain as automatic.  The active
   local-overlap object is the `overlap` field in
   `SourceAdjacentOverlapWitness`; the legacy parameter-free
   `sourceAdjacentPermutationGramOverlap` remains only the full adjacent double
   domain helper used by older checked support lemmas.  The seed-cover / chain
   machinery is archived unless the missing global source input is supplied.  A
   future collapse of the witness overlap to the full adjacent double domain
   would be an optimization only after a separate proof justifies it.
   One more tempting shortcut has now been ruled out explicitly: the scalar
   double-domain is not automatically the Gram-map image of the vector-valued
   adjacent overlap domain, because `sourceDoublePermutationGramDomain`
   remembers separate realizability of `Z` and `τ·Z`, not realizability by one
   common configuration `w` with both `w` and `τ·w` in `ExtendedTube`.
   Likewise, the scalar double-domain should not be treated as obviously
   conjugation-equivariant under permutation of Gram coordinates, since
   `sourceExtendedTubeGramDomain` itself is not permutation-invariant.
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
   The active Lean branch is the source-backed BHW single-valuedness packet:
   use checked local source support from
   `BHWPermutation/SourceExtension.lean`, then prove or source-import
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
   and feed its sector-equality corollary to
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.
   The common-forward-tube fixed-orbit gallery remains retired, because a
   common Lorentz witness for two ordinary permuted forward-tube chambers
   forces the labels to be equal.  The reachable-label `hOrbit` monodromy
   theorem remains conditional infrastructure, not the theorem-2 gate.  The
   locality-assuming top-level `BHW.bargmann_hall_wightman_theorem` is not an
   allowed replacement.

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
