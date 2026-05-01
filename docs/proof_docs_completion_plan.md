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

Current theorem-2 implementation ledger: the downstream Hall-Wightman/Jost
source package remains the route after the local OS45 envelope has been
constructed, but it is not the immediate Lean gate.  The immediate gate is
local Slot 1:

1. keep the checked bounded identity-order perturbation and raw real-open ball
   selector as support;
2. checked: `BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability`
   and `BHW.os45_adjacent_identity_horizontalEdge_sourcePatch` now choose the
   ordered seed inside `Ufig ∩ Upath`, shrink with compact closure, and export
   the closure-level Figure-2-4 path field;
3. current proof-document frontier: finish the upstream scalar-source inputs
   before any branch-local Lean pass:
   `BHW.sourceScalarRepresentativeData_bvt_F` via the five-stage ordinary
   Hall-Wightman source descent, and the adjacent `S'_n` package
   `BHW.os45Figure24_sourceChart_at`,
   `BHW.os45SPrime_sourcePullback_pairing_eq_permutedSchwinger`,
   `BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`,
   `BHW.os45AdjacentSPrimeScalarizationChart_of_figure24`,
   `BHW.os45AdjacentSPrimeSourceEq_of_compactWickPairingEq`,
   `BHW.os45AdjacentSPrimeScalarSeed_of_compactWickPairingEq`, and
   `BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq`;
4. only after those scalar-source inputs are proof-ready may the branch-local
   source-germ layer be implemented through the scalar-packet surfaces
   `BHW.os45OneBranchScalarGramEq_sourceInput_id`,
   `BHW.os45OneBranchScalarGramEq_sourceInput_adjacent`,
   `BHW.os45OneBranchACRBHWAgreement_of_scalarGramEq`,
   `BHW.os45OneBranchACRBHWAgreement_sourceInput`,
   `BHW.os45OneBranchACRBHWAgreement_of_sourcePatch`, and
   `BHW.os45BranchHorizontalSourceGermAt_of_oneBranch_sourcePatch`;
5. construct the identity and adjacent branch BV packets, subtract them, and
   call the checked one-chart local EOW/gluing route to produce
   `BHW.os45_adjacent_commonBoundaryEnvelope`.

Only after this Slot 1 envelope exists does the route move to
`bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII`, the checked
projection to `BHW.SourceDistributionalAdjacentTubeAnchor`, the direct source
frontier `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
and then the `S''_n` single-valuedness/Jost boundary-transfer layer.  This
downstream package is still the alternative to BHW/PET monodromy through
`hOrbit`; it must not be used to manufacture the local source-germ or EOW
inputs.

Current local Slot 1 correction: the OS45 common-chart/EOW supplier is no
longer the equal-time/post-radius plan.  The checked SCV input is
`SCV.chartDistributionalEOW_local_envelope`; the OS45 proof must instantiate
it at an ordered identity-sector horizontal edge.  The common-boundary
dependency shape is fixed,
and the branch CLM theorem slots are now exposed: the adjacent branch is the
ordinary OS-II branch for the relabelled patch `x ∘ τ`, transported back by
the OS45 reindexing identity.  The one-branch OS-II/BHW horizontal boundary
theorem is now decomposed into named source, common-germ, and branch-BV
theorems; the
compact-direction `hlocal` domain hypotheses are reduced to the documented
openness/compactness lemma once the source patch supplies closure-level edge
membership.
The bounded identity perturbation and same-patch identity geometry are
checked.  The proposed horizontal-edge forward-tube pair
and pointwise equality `Hplus = Hminus` from two applications of
`BHW.extendF_eq_on_forwardTube` are rejected: after the repo permutation action
`permAct σ z = fun k => z (σ k)`, an adjacent swap reverses the relevant
horizontal time-imaginary gap.  The replacement is a branchwise horizontal
ACR/BHW common-boundary packet: construct the identity and swapped branch
horizontal-edge CLMs `Tid` and `Tτ`, prove ACR-side and BHW-side uniform
compact-direction boundary values for each branch, subtract to get the
`hplus_bv`/`hminus_bv` input with `Tdiff = Tτ - Tid`, and only then call the
one-chart theorem.  `Tdiff` is not assumed zero and is not the final real-edge
locality distribution.  The branchwise packet is local and non-circular:
`Tid` and `Tτ` are full CLMs produced by the OS45 branchwise distributional
boundary-value theorem, on the selected ordered quarter-turn edge and the
relabelled ordered patch `x ∘ τ` respectively;
`BHW.os45QuarterTurnConfig_reindexed_realBranch_eq` then places both branches
at the same quarter-turn chart point.  The zero-diagonal Schwinger functional
and `OS.E3_symmetric` verify the compact Jost-supported Euclidean restriction
of those CLMs; they cannot by themselves define the full CLMs needed by SCV.
Nor should these CLMs be treated as direct pullbacks of the final physical
real-time distribution `bvt_W`, since the OS45 horizontal edge is real only in
the quarter-turn chart.
The later Hall-Wightman source theorem consumes the resulting compact-test
anchor and must not be used to construct it.  The global compact-direction
`bvt_W` boundary transport remains useful elsewhere.
The latest proof-doc tightening makes two additional constraints explicit.
First, the branch BV theorem may not quantify over an arbitrary side cone:
its statement must carry the compact-direction local wedge hypothesis saying
that `y + i εη` lies in the ACR branch domain and `y - i εη` lies in the
pulled BHW branch domain, uniformly for compact `K ⊆ E` and compact
`Kη ⊆ C`.  This `hlocal` field is supplied by the one-branch OS45 horizontal
domain theorem: the ordered OS45 formulas give the half-time
directions, but the BHW/Jost common-real-environment input is what puts the
horizontal edge and a small conic side window inside the correct branch
domains.  That input is now explicitly patch-level: the active theorem is the
adjacent identity-order OS45 source-patch theorem putting the selected
horizontal edge in the identity and swapped pulled branch domains.  It is not
an all-Jost pointwise formula, and it is not supplied by hope or by total
function values outside domains.  Second,
the ACR branch representative is the branch-undone quarter-turn pullback
`bvt_F (permAct β.symm ((os45QuarterTurnCLE).symm z))`; its holomorphy on the
ACR branch domain is obtained by rewriting with the permutation-symmetry field
of `bvt_F_acrOne_package`, reducing to the ordinary forward-tube
holomorphy.  The local selector
`BHW.os45_adjacent_identity_horizontalEdge_sourcePatch` is now transcript-level:
it shrinks the checked adjacent identity-order patch to a connected ball with
compact closure, so that it still carries the Wick/real trace-domain and
opposite-tube geometry fields, and also puts the selected OS45 horizontal edge
inside the two pulled BHW branch domains needed for the adjacent identity-order
patch.  This precompactness is what lets the branch-horizontal common germ be
cut off on a real neighborhood of `closure E` to produce the full Schwartz CLM
required by the checked SCV EOW theorem.  The proof-doc route for this packet
is now fixed: the source theorem is split in the theorem-2 blueprint into the
genuine one-branch germ statement `BHW.os45BranchHorizontalCommonGerm` and its
boundary-CLM consumer `BHW.os45BranchHorizontalBoundaryValue`, whose outputs
exactly match the `acr_bv` and `bhw_bv` fields of
`OS45BranchHorizontalBV`.  The route must not introduce public identity or
adjacent branch BV wrappers that merely fix the branch label and forward
generic inputs; any private assembly helper must genuinely derive the selected
branch's `hsource`, `hlocal`, common edge, and openness/compactness data before
calling the generic theorem.  The generic BV consumer now takes
only the common edge `E`, compactness/openness data, `hsource`, and `hlocal`;
Jost/order/extended-tube fields live upstream where `hsource` and `hlocal` are
proved.  Domain membership, local side windows, and precompactness do not by
themselves prove that the ACR and pulled BHW formulas are restrictions of one
holomorphic germ.
The only auxiliary cutoff lemma on this path is the pure real-analysis
Schwartz cutoff statement.  The checked theorem
`SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open` already supplies
the support-in-open projection; the branch-BV route exposes the same
construction with the additional compact-support field as
`SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open_compactSupport`, so
the regular boundary CLM can be built through the checked flat-coordinate
`SCV.exists_closedBall_integral_clm_of_continuousOn` API rather than a fresh
seminorm proof.  Because the branch theorem is on `NPointDomain d n`, the
proof first uses the flattening adapters
`BHW.exists_nPoint_schwartz_cutoff_eq_one_on_compact_subset_open_compactSupport`
and `BHW.exists_nPoint_closedBall_integral_clm_of_continuousOn`, based on
`flattenCLEquivReal n (d + 1)`, `flattenCLEquivReal_norm_eq`,
`SchwartzMap.compCLMOfContinuousLinearEquiv`, support transport by the
associated homeomorphism, and `integral_flattenCLEquivReal`.  The
boundary-limit estimate is an all-space integral localized by `φ = 0` off
`tsupport φ`, bounded by the uniform supremum on `tsupport φ × Kη` times
`∫ y, ‖φ y‖`; it must not treat an arbitrary compact support set as the
measure domain.  The common-germ neighborhood shrink is its own pure topology
lemma `BHW.exists_uniform_realEdgeAddImag_mem_open_of_compact`: compactness of
`tsupport φ × Kη` and openness of the common-germ neighborhood give one radius
so both `realEdgeAddImag y η ε` and `realEdgeAddImag y η (-ε)` stay where
`Hβ` is continuous.  This is separate from the branch-domain local-wedge
theorem.  The coordinate and compactness layer for the local horizontal
wedge is also now checked in
`OSToWightmanLocalityOS45TraceMembership.lean`: `BHW.os45ACRBranchDomain`,
`BHW.os45CommonEdge_mem_acrBranchDomain_of_ordered`,
`BHW.realEdgeAddImag`, and
`BHW.os45BranchHorizontal_localWedge_of_edgeDomain`.  These are pure
quarter-turn/topology facts and do not supply the OS-I source theorem.  The
Figure-2-4 selector and the source-patch shrink now have transcript-level
proof plans.  The next work is still proof-document completion, not Lean
implementation, until the analytic source statements have full proof
transcripts.  The theorem-2 blueprint now fixes those transcripts for
`BHW.OS45BranchHorizontalSourceGermAt`,
`BHW.os45BranchHorizontalCommonGerm`, and the boundary-CLM consumer
`BHW.os45BranchHorizontalBoundaryValue`; the next implementation work must
follow those named theorem surfaces in that order.

The source-patch selector is now checked in Lean.  The implemented theorem is
the combined anchored selector
`BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability`, not two
independently chosen selectors.  It starts from the same equal-time
Figure-2-4 witness used by
`BHW.swFigure24_adjacentPathStableNeighborhood_exists`, takes the finite
intersection of the Jost-set preimage, the two ordinary extended-tube
preimages, and the two OS45 horizontal pulled-domain preimages, and proves
anchor membership in the pulled domains from the zero-time identities
`os45CommonEdgeRealPoint 1 x0 = x0`,
`Q.symm (realEmbed x0) = realEmbed x0`, and
`permAct τ.symm (realEmbed x0) = realEmbed (x0 ∘ τ)`.  Openness comes from
`BHW.isOpen_jostSet`, `BHW.isOpen_extendedTube`,
`BHW.isOpen_os45PulledRealBranchDomain`, and the public finite-dimensional
continuity helpers for `realEmbed`, point permutations, and the identity
common-edge map.  Its path field is conditional on ordered identity-sector
membership: `Γ` is `BHW.os45Figure24IdentityPath`, and `Δ` is the checked
rotated Figure-2-4 realization from the compact-open path-stability
neighborhood.  The theorem does not compare branch values or assert that the
bare relabelled identity path is the adjacent branch.

The checked patch theorem
`BHW.os45_adjacent_identity_horizontalEdge_sourcePatch` is then a
finite-dimensional shrink: first choose the positive identity-ordered seed
inside `Ufig ∩ Upath`, then shrink inside
`Ufig ∩ Upath ∩ ordered ∩ swappedOrdered` by
`BHW.exists_connected_open_precompact_subset`.  The Wick-seed, real-edge, and
opposite-tube fields are derived from the checked ordered/extended-tube
lemmas; the closure-level ordered, pulled-domain, and Figure-2-4 path fields
are inherited from the same finite intersection.  This separation is
mandatory: the Figure-2-4 environment supplies branch domains only, while the
topology lemma supplies `closure V` containment; neither theorem invokes
`bvt_W`, `extendF` equality, or final locality.  The remaining
non-topological source content is the branch-value compatibility predicate
`BHW.OS45BranchHorizontalSourceGermAt`; domain membership alone is not enough
to identify the ACR and BHW formulas.  The theorem-2 blueprint now isolates
the predicate as a **branch-specific** canonical-germ statement using
`z ↦ extendF (bvt_F OS lgc n) (permAct β.symm (Q.symm z))`.  This is a
route-hardening correction: using the unpermuted germ
`z ↦ extendF (bvt_F OS lgc n) (Q.symm z)` for every branch would identify
the identity and adjacent branch packets before the EOW step and would revive
the retired tautological cancellation shortcut.

Post-selector proof-doc frontier: the production Lean germ-API migration is
now allowed and has started only for the existing source-variety identity and
uniqueness infrastructure.  Do not implement the Hall-Wightman scalar
representative theorem itself until the following two analytic inputs are
transcript-ready.  First, the ordinary Hall-Wightman scalar representative for the OS-II
forward-tube function must be named explicitly, for example as
`BHW.sourceScalarRepresentativeData_bvt_F`; on the theorem-2 route it carries
the ambient dimension hypothesis `hd : 2 <= d` and produces
`BHW.SourceScalarRepresentativeData (d := d) n (bvt_F OS lgc n)` from
`bvt_F_holomorphic` and the checked Lorentz-invariance theorem for `bvt_F`.
This is a Hall-Wightman/BHW source theorem, not a locality or EOW theorem.  It
must not remain a compressed black-box theorem surface.  The proof-doc
implementation contract is:

0. Dimension and analytic-space audit: Hall-Wightman is printed for
   four-vectors, while theorem 2 is stated for spacetime dimension `d + 1`.
   The proof docs must therefore carry the dimension-general replacement of
   the Hall-Wightman linear algebra: `4` becomes `d + 1`, the Lemma-2 direct
   orbit threshold `3` becomes `d`, and the local scalar-chart maximum rank is
   `min (d + 1) n`.  The theorem-2 blueprint now names the needed standard
   geometry inputs:
   `BHW.complexMinkowskiBilinear`,
   `BHW.ComplexMinkowskiNondegenerateSubspace`,
   `BHW.standardComplexSymmetricBilinear`,
   `BHW.complexLorentzVectorAction`,
   `BHW.complexMinkowskiOrthogonalModel`,
   `BHW.complexMinkowskiOrthogonalModel_preserves_bilinear`,
   `BHW.complexMinkowski_wittExtension`,
   `BHW.hwLemma3_sourceGram_localVectorRealization_smallPerturbation`,
   `BHW.hwLemma3_sourceGram_localVectorRealization`,
   `BHW.sourceComplexGramVariety_eq_sourceSymmetricRankLEVariety`,
   `BHW.sourceComplexGramVariety_eq_rank_le`,
   `BHW.sourceComplexGramVariety_normal`,
   `BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_maxRank`,
   with the determinantal normality subpacket
   `BHW.AnalyticSingularLocus`,
   `BHW.symmetricRankLEMatrixSet`,
   `BHW.sourceSymmetricRankLEVariety_schurLocalProductModel`,
   `BHW.sourceSymmetricRankLEVariety_singularLocus_eq_lowerRank`,
   `BHW.sourceSymmetricRankExactStratum_complexDimension`,
   `BHW.sourceSymmetricRankLEVariety_lowerRank_codim`,
   `BHW.sourceSymmetricRankLEVariety_lowerRank_codim_ge_two`,
   and `BHW.sourceSymmetricRankLEVariety_reduced_cohenMacaulay`,
   `BHW.sourceSymmetricRankLEVariety_cohenMacaulay`,
   `BHW.sourceSymmetricRankLEVariety_regularInCodimOne`,
   `BHW.normalAnalyticSubvariety_of_serre`, and
   `BHW.normalAnalyticSubvariety_weaklyHolomorphic_localExtension`, then
   `BHW.sourceGramVariety_normal_riemannExtension`, followed by the active
   standard-geometry predicates
   `BHW.IsRelOpenIn`, `BHW.LocallyBoundedOn`,
   `BHW.IsAnalyticSubvarietyIn`,
   `BHW.NormalAnalyticSubvariety`,
   `BHW.CohenMacaulayAnalyticSubvariety`, and
   `BHW.RegularInCodimensionOne`, plus the normality-packet support
   predicates
   `BHW.AnalyticLocalRingRegular`,
   `BHW.ReducedAnalyticSubvariety`,
   `BHW.ComplexAnalyticDimension`,
   `BHW.AnalyticCodimensionIn`, and
   `BHW.AnalyticLocalProductModelAt`.  These predicates must be genuine
   finite-dimensional SCV/local-ring notions or imports from the local SCV
   support library; they cannot be implemented as vacuous placeholders or as
   wrappers around the target scalar representative theorem.  The active
   germ API
   `BHW.SourceVarietyGermHolomorphicOn`,
   `BHW.SourceVarietyGermHolomorphicOn.continuousOn`,
   `BHW.SourceVarietyGermHolomorphicOn.of_subset_relOpen`,
   `BHW.SourceVarietyGermHolomorphicOn.sub`, and
   `BHW.SourceVarietyGermHolomorphicOn.precomp_sourcePermuteComplexGram`,
   plus the pullback and identity-principle consumers
   `BHW.SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram`,
   `BHW.SourceVarietyGermHolomorphicOn.comp_differentiableOn_chart`, and
   `BHW.sourceComplexGramVariety_identity_principle`; the continuity
   theorem must carry or derive the hypothesis
   `U ⊆ BHW.sourceComplexGramVariety d n`, supplied in this route by relative
   openness in the source variety.
   This fixes the singular-rank analytic gap in the route without asking for
   a false off-variety equality statement: for `n > d + 1`, Hall-Wightman's
   output is a holomorphic germ on the symmetric determinantal scalar-product
   variety, represented locally by ambient holomorphic charts that agree only
   on the variety.  Boundedness and continuity at singular points are used by
   the normal analytic-space Riemann/removable theorem, together with density
   of the maximal-rank locus in every relatively open source-variety patch, to
   produce those local variety-germ representatives; they do not produce one
   global ambient function holomorphic off the variety.

   The determinantal normality subpacket is now pinned to a precise proof
   order.  First, the checked Schur-graph infrastructure supplies the local
   product model: on a determinant-unit principal patch,
   `sourcePrincipalSchurGraph_rankLE_image_eq_openCoordinatePatch` identifies
   `sourceSymmetricRankLEVariety n D` with a smooth `(A,B)` factor times the
   smaller cone `BHW.symmetricRankLEMatrixSet q (D-r)` in the Schur
   coordinate, with `q` the complementary finite index type.  Second,
   this model proves the singular-locus equality
   `Sing(rank <= D) = rank <= D-1` in the range `0 < D < n`, while `D = 0`
   and `n <= D` are smooth cases.  Third, the selected-chart dimension formula
   gives codimension `n - D + 1`, hence at least two in the singular range.
   Fourth, the standard symmetric-determinantal reduced Cohen-Macaulay theorem
   is combined with Serre's criterion to produce normality.  Any Lean
   implementation must follow this packet or import this exact
   symmetric-determinantal theorem as a standard finite-dimensional
   algebraic-geometry input; it cannot replace the packet by a source-scalar
   representative wrapper.

   The theorem-2 blueprint still archives the stronger Siu/Cartan package
   `BHW.SteinOpen`,
   `BHW.sourceComplexGramVariety_closedAnalytic`,
   `BHW.sourceExtendedTubeGramDomain_domainOfHolomorphy`,
   `BHW.domainOfHolomorphy_steinAnalyticSubspace`,
   `BHW.sourceExtendedTubeGramDomain_steinAnalyticSpace`,
   `BHW.siu_steinNeighborhood_sourceGramSubspace`,
   `BHW.sourceExtendedTubeGramDomain_steinAmbientNeighborhood`,
   `BHW.sourceGramIdealSheaf_coherent`,
   `BHW.cartanB_restriction_surjective_for_coherentIdeal`,
   `BHW.cartan_surjective_restriction_sourceGramVariety`, and
   `BHW.sourceVariety_holomorphicGerm_cartanAmbientExtension`; this is now an
   optional strong-API bridge only.  It is not accepted as a Hall-Wightman
   source consequence, because the local source audit records `S'_n` as open
   and connected but not as the natural domain of holomorphy for the field
   theory functions.  Gemini Deep Research interaction
   `v1_ChZIeHYwYWE5cng1Mzd4Z19ldGRDQURREhZIeHYwYWE5cng1Mzd4Z19ldGRDQURR`
   agrees that the strong bridge is mathematically sound if Step 1 is supplied
   by an independent Bochner-Martin/invariant-quotient theorem for the scalar
   image `S'_n` (or equivalent modern extended-tube SCV input).  That verdict
   keeps the bridge available as optional SCV support, but it does not reopen
   production Lean until those additional source statements are proof-ready or
   explicitly approved as a source-import boundary.

   Implementation gate: none of the Hall-Wightman scalar representative
   surfaces in this item may move to production Lean until either the listed
   BHW/Hall-Wightman germ-support theorems have proof transcripts detailed
   enough to implement without new `sorry`/`axiom`, or the user explicitly
   approves a source-import boundary with exactly these theorem statements and
   no theorem-2/locality content.  The existing production
   `SourceScalarRepresentativeData.Phi_holomorphic` field has now been
   migrated from `BHW.SourceVarietyHolomorphicOn` to
   `BHW.SourceVarietyGermHolomorphicOn`; that migration removes the false
   global-ambient holomorphy requirement but does not by itself implement
   `BHW.sourceScalarRepresentativeData_bvt_F`.

1. `BHW.extendedTube_same_sourceGram_extendF_eq`: for `z,w ∈
   BHW.ExtendedTube d n`, equality of
   `BHW.sourceMinkowskiGram d n z` and
   `BHW.sourceMinkowskiGram d n w` implies
   `BHW.extendF F z = BHW.extendF F w`, under holomorphy of `F` on the forward
   tube and complex Lorentz invariance on forward-tube overlaps.  This is the
   ordinary Hall-Wightman branch law, not PET branch independence.  The
   scalar-rank split must be the Hall-Wightman split, not the local
   source-map-regularity predicate.  Introduce
   `BHW.sourceGramMatrixRank`, `BHW.HWSourceGramOrbitRank`, and
   `BHW.HWSourceGramLowRank`; for spacetime dimension `d + 1`, the direct
   orbit branch is scalar rank at least `min d n`, and the limiting branch is
   scalar rank `< min d n`.  In the original four-vector paper this is rank
   three or four in the hard arity range, and nonsingular scalar matrices in
   the small-arity range.  The theorem-2 blueprint now expands this into the
   Lean-facing Lemma-2 alternative:
   `BHW.hw_sameSourceGram_fiberAlternative`, the high scalar-rank orbit theorem
   with its coefficient-quotient support
   `BHW.sourceCoefficientEval`,
   `BHW.sourceCoefficientGramKernel`,
   `BHW.sourceCoefficientEval_ker_le_gramKernel`,
   `BHW.restrictedMinkowskiLeftMap`,
   `BHW.restrictedMinkowskiRadical`,
   `BHW.restrictedMinkowskiRank`,
   `BHW.sourceGramMatrixRank_eq_restrictedMinkowskiRank_range`,
   `BHW.sourceGramMatrixRank_lt_orbitThreshold_of_range_degenerate`,
   `BHW.hw_highRank_eval_range_nondegenerate`,
   `BHW.hw_highRank_eval_ker_eq_gramKernel`,
   `BHW.hw_highRank_sourceCoefficientEval_ker_eq_of_sameSourceGram`,
   `BHW.HWHighRankSpanIsometryData`, and
   `BHW.hw_highRank_spanIsometryData_of_sameSourceGram`, then
   `BHW.extendF_complexLorentzInvariant_of_cinv` with both `hF_holo` and
   `hF_cinv`, and the singular
   two-curve limit theorem
   `BHW.hw_sameSourceGram_singularLimit_extendF_eq`.  The singular data must
   expose two endpoint Lorentz-orbit curves, one from `z` and one from `w`,
   both converging to the same base configuration; value equality is then
   derived from extended-tube Lorentz invariance and continuity, not stored as
   an analytic field and not asserted as pairwise orbit equality of the two
   approximating curve values.
   `BHW.hw_sameSourceGram_fiberAlternative` itself splits into
   `BHW.hw_sameSourceGram_regular_orbit` with
   `BHW.HWSourceGramOrbitRankAt d n z` and
   `BHW.hw_sameSourceGram_singular_contractionData` with
   `BHW.HWSourceGramLowRankAt d n z`.  The low-rank branch must itself pass
   through the explicit isotropic residual-frame data
   `BHW.HWLowRankIsotropicNormalForm`,
   `BHW.hw_lowRank_isotropicNormalForm_of_sameSourceGram`, and
   `BHW.hw_lowRank_isotropicNormalForm_to_contractionData`; inside the
   normal-form theorem the independent scalar block is chosen by the checked
   symmetric principal-minor input
   `BHW.exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank`, not by an
   unspecified rank argument.  The low-rank proof must also expose the genuine
   linear algebra subfacts
   `BHW.hw_lowRank_selectedSpanFrame_of_sameSourceGram`,
   `BHW.hw_lowRank_alignedResidualFrame_of_sameSourceGram`,
   `BHW.ComplexMinkowskiNondegenerateSubspace`,
   `BHW.complexMinkowski_isotropicDualFrame_of_residualFrame`,
   `BHW.complexMinkowski_wittExtension_subspaceIsometry`,
   `BHW.complexMinkowski_isotropicContraction_partialIsometry`,
   `BHW.complexMinkowski_isotropicContractionFamily`, and
   `BHW.hw_lowRank_isotropicContraction_staysIn_extendedTube`.  The printed
   four-dimensional Hall-Wightman proof collapses the residual frame to one
   null vector in ranks one and two; the dimension-general Lean route must
   contract a finite totally isotropic frame instead.  The normal-form packet
   must store the dual isotropic frame fields used by the contraction:
   `qDual_pair_zero`, `q_dual`, `qDual_orth`, and the contraction-family
   field `contract_scale_qDual`; otherwise the Lorentz-family construction is
   hidden behind an unexplained existence theorem.  The contraction family is
   split through the standard finite-dimensional Witt lemma
   `BHW.complexMinkowski_wittExtension_subspaceIsometry`: first define the
   partial isometry on
   `span (range ξ) ⊔ span (range q) ⊔ span (range qDual)` fixing `ξ`,
   scaling `q` by `Real.exp (-t)`, and scaling `qDual` by `Real.exp t`; then
   use the dual-pairing equations to prove this partial map preserves the
   complex Minkowski form before extending it to `ComplexLorentzGroup d`.
   The later convergence proof must use the explicit contracted
   configurations and `Real.tendsto_exp_neg_atTop_nhds_zero`, not continuity
   of a noncomputably chosen `t ↦ contract t`.  The contraction data
   consists of two Lorentz-orbit curves, one from each endpoint, converging to
   the same base configuration; it is not a claim that the two approximating
   curve values are pairwise in one orbit.  The proof of those orbit fields
   uses `BHW.complexLorentzAction_mul` for the left curve
   (`N.contract t * N.Λ0`) and the direct `N.contract t` action for the right
   curve.  The analytic value equality is proved only later by Lorentz
   invariance plus continuity.
   `BHW.SourceComplexGramRegularAt` remains reserved for the later local
   source-Gram image theorem; it is not the Hall-Wightman Lemma-2 predicate.
   The high-rank nondegeneracy proof now has an explicit rank bridge:
   `sourceGramMatrixRank_eq_restrictedMinkowskiRank_range` identifies the
   scalar Gram matrix rank with the rank of the complex Minkowski form
   restricted to the span generated by the source vectors, and
   `sourceGramMatrixRank_lt_orbitThreshold_of_range_degenerate` proves that a
   nonzero restricted radical forces scalar rank below `min d n`.  This
   prevents the direct-orbit branch from silently replacing Hall-Wightman's
   scalar-rank condition by a source-map regularity or span-nondegeneracy
   assumption.
   The high-rank branch is equally not allowed to skip directly from equal
   Gram entries to a Lorentz transform: the proof must first identify the
   coefficient kernels of the two source tuples through the common scalar
   Gram kernel, descend the identity map on coefficient space to an isometry
   of the two vector spans, and only then apply
   `BHW.complexMinkowski_wittExtension`.
2. `BHW.sourceExtendedTubeGramDomain_relOpen_connected`: the scalar image
   `BHW.sourceExtendedTubeGramDomain d n` is relatively open in
   `BHW.sourceComplexGramVariety d n` and connected.  Continuity of the Gram
   map is not enough for relative openness; this is the BHW scalar-product
   geometry of `S'_n`.  The connectedness half can use the checked
   `BHW.isConnected_extendedTube` and
   `(BHW.contDiff_sourceMinkowskiGram d n).continuous`; the relative-openness
   half is the Hall-Wightman scalar-neighborhood theorem.
   The local form is
   `BHW.sourceExtendedTubeGramDomain_relOpen_at`; its implementation is the
   Hall-Wightman Lemma-3 realization theorem
   `BHW.hwLemma3_sourceGram_localVectorRealization`: choose an extended-tube
   realization `z0` of the scalar point, choose a small coordinate ball around
   `z0` inside the ordinary extended tube, and use the quantitative
   `BHW.hwLemma3_sourceGram_localVectorRealization_smallPerturbation` theorem
   to realize every nearby scalar point in the source Gram variety by a
   perturbation still inside that ball.  The theorem-2 blueprint now expands
   the quantitative theorem down to Hall-Wightman's actual Lemma-3 algebra:
   `BHW.hwLemma3_selectedBlock_sqrt_near_identity` for the analytic square
   root of the selected principal block near `1`,
   `BHW.hwLemma3_schurComplement_rank_bound` for the lower-right residual
   rank `<= d + 1 - r`,
   `BHW.complexSymmetric_takagi_rankLE` and
   `BHW.complexSymmetric_factorSmall_rankLE` for the finite-dimensional
   Takagi/Bargmann factorization and its small-factor estimate,
   `BHW.complexMinkowskiOrthogonalTailSubspace` and
   `BHW.complexMinkowski_realizeSmallSymmetricRankLE_inOrthogonalTail` for
   realizing the Schur residual in the orthogonal complement of the selected
   normalized block, with the arithmetic and norm-control helpers
   `BHW.exists_finTailEmbedding` and
   `BHW.complexMinkowskiOrthogonalModel_symm_coord_bound`, and
   `BHW.complexMinkowski_realizeSmallSymmetricRankLE` as only the `r = 0`
   corollary of that tail theorem.  The normalized Schur proof must use the
   tail theorem, not the full-space corollary, or the residual vectors could
   disturb the selected block.  The canonical normal-form data are
   `BHW.hwLemma3CanonicalSource`,
   `BHW.hwLemma3CanonicalGram`, and
   `BHW.sourceMinkowskiGram_hwLemma3CanonicalSource`, the normalized
   surjectivity theorem
   `BHW.hwLemma3_normalizedSchurSurjective`, and the transport theorem
   `BHW.hwLemma3_transport_from_normalForm`.  The final conversion from the
   quantitative `ε` theorem to arbitrary `Vsrc` is the finite-product
   open-ball helper `BHW.exists_coord_supnorm_ball_subset_of_isOpen` followed
   by
   `BHW.hwLemma3_smallPerturbation_to_localVectorRealization`; it is not a
   replacement for Lemma 3.  The
   orbit-rank/low-rank split remains internal as
   `BHW.hwLemma3_sourceGram_localVectorRealization_orbitRank` and
   `BHW.hwLemma3_sourceGram_localVectorRealization_lowRank`, but the exported
   relative-open theorem is the direct Lemma-3 neighborhood statement.  The
   global relative-open field is the union of those ambient neighborhoods,
   plus the elementary inclusion
   `BHW.sourceExtendedTubeGramDomain_subset_sourceComplexGramVariety`.
3. `BHW.sourceVarietyGermHolomorphicOn_extendF_descent`: descend
   `BHW.extendF F` through `BHW.sourceMinkowskiGram d n` to a
   `BHW.SourceVarietyGermHolomorphicOn` scalar representative.  The branch law
   gives well-definedness, and the local Hall-Wightman source charts give
   analytic-space variety holomorphicity.  The production API must migrate the
   `SourceScalarRepresentativeData.Phi_holomorphic` field from the old strong
   `BHW.SourceVarietyHolomorphicOn` predicate to
   `BHW.SourceVarietyGermHolomorphicOn`: Hall-Wightman supplies local ambient
   representatives agreeing with the scalar function on
   `U0 ∩ BHW.sourceComplexGramVariety d n`, not one global ambient function
   holomorphic off the variety.  A preimage-choice function on
   `sourceExtendedTubeGramDomain` is still not enough; the chosen scalar value
   function must be represented locally by the Hall-Wightman scalar charts on
   the analytic variety.  The theorem-2 blueprint now names this content as
   the germ-API data `BHW.SourceVarietyGermHolomorphicOn`, the support lemmas
   `continuousOn`, `of_subset_relOpen`, `sub`,
   `precomp_sourcePermuteComplexGram`, `comp_sourceMinkowskiGram`,
   `comp_differentiableOn_chart`, and
   `sourceComplexGramVariety_identity_principle`.
   If an atlas is useful during implementation, `BHW.HallWightmanScalarGermAtlas`,
   `BHW.hallWightman_consistentScalarGermAtlas`, and
   `BHW.hallWightman_scalarGermAtlas_glue` are proof-local organization only:
   they must be private or inlined into
   `BHW.sourceVarietyGermHolomorphicOn_extendF_descent`, not exported as an
   additional source theorem surface.
   The direct descent core is split further into
   `BHW.hallWightman_localScalarChart_at`, with the separate local-chart
   predicates `BHW.HWSourceGramMaxRank` and
   `BHW.HWSourceGramExceptionalRank` and sublemmas
   `BHW.hallWightman_maxRank_localScalarChart_at` and
   `BHW.hallWightman_exceptionalRank_localScalarChart_at`.  This keeps the
   non-exceptional scalar-product chart, exceptional-rank removable-singularity
   step, and chart-overlap gluing explicit.  The theorem-2 blueprint now
   further expands those local-chart lemmas into
	   `BHW.hallWightman_maxRank_powerSeriesChart_at`,
	   `BHW.hallWightman_lorentzInfinitesimalEquations`,
	   with the Lemma-4 exp-curve support
	   `BHW.complexMinkowskiSkewGenerator_isInLieAlgebra`,
	   `BHW.ComplexMinkowskiSkewGenerator.expCurve`,
	   `BHW.complexMinkowskiSkewGenerator_expCurve_val`,
	   `BHW.complexMinkowskiSkewGenerator_expCurve_zero`,
	   `BHW.complexLorentzAction_expCurve_mem_extendedTube`,
	   `BHW.complexLorentz_expCurve_action_hasDerivAt`,
	   `BHW.differentiableAt_extendF_of_mem_extendedTube`, and
	   `BHW.extendF_expCurve_invariant`,
	   `BHW.hallWightman_maxRank_scalarDifferentials_span_PDE`,
	   with the Lemmas-6--7 tangent/dual packet
	   `BHW.sourceGramDifferential`,
	   `BHW.sourceGramDifferential_apply`,
	   `BHW.sourceGramCoordinateDifferential_apply`,
	   `BHW.sourceGramDifferential_lorentzInfinitesimalTangent_zero`,
	   `BHW.complexMinkowski_infinitesimalWittExtension`,
	   `BHW.HWMaxRankSelectedRowsData`,
	   `BHW.hwMaxRank_selectedRowsData`,
	   `BHW.hwMaxRank_kernel_row_relation_transfer`,
	   `BHW.sourceGramDifferential_kernel_eq_lorentzInfinitesimalTangent`,
	   `BHW.continuousLinearFunctional_factor_through_of_vanishes_on_ker`, and
	   `BHW.sourceGramDifferential_dual_coordinate_expansion`,
	   `BHW.HWPowerSeriesCoordinateSplit`,
   `BHW.SelectedScalarCoordinatesBasis`,
   `BHW.HWVectorCoordinateSplitData`,
   `BHW.hallWightman_independentScalarCoordinates`,
   `BHW.hallWightman_sourceVectorCoordinateSplit`,
   `BHW.exists_open_selectedMinor_ne_zero_neighborhood`,
   `BHW.sourceGramDifferential_image_basis_of_selected_minor`,
   `BHW.hallWightman_maxRank_selectedScalarDifferentials_local`,
   `BHW.hallWightman_coordinateSplit_inverseFunction`,
   `BHW.exists_sourceCoord_product_with_connected_aux_subset_open`,
   `BHW.auxiliaryCoordinateTangent`,
   `BHW.auxiliaryCoordinateTangent_selectedScalarDeriv_zero`,
   `BHW.hallWightman_auxiliaryTangent_sourceGramDifferentials_zero`,
   `BHW.fderiv_coord_pullback_extendF`,
   `BHW.hallWightman_powerSeries_coordinateSplit`,
   `BHW.hallWightman_coord_pullback_extendF`,
   `BHW.hallWightman_auxiliaryDerivative_zero`,
   `BHW.eqOn_of_fderiv_eq_zero_of_isConnected_open`,
   `BHW.holomorphic_product_independent_of_auxiliary`,
   `BHW.hallWightman_selectedScalarFunction_to_fullGramChart`,
   `BHW.hallWightman_powerSeries_from_PDE_span`,
   `BHW.hallWightman_powerSeriesChart_branch_eq_of_sameGram`,
   `BHW.hallWightman_scalarGerm_continuous_locallyBounded`,
   `BHW.continuousOn_of_open_nhdsWithin_control`,
   `BHW.continuousOn_openDomain_preimage_nhds`,
   `BHW.hwSourceGramExceptionalRank_isAnalyticSubvariety`,
   `BHW.sourceGramVariety_removableAlongExceptionalRank`, and
   `BHW.hallWightman_removableScalarChart_at`, and
   `BHW.hallWightman_localScalarChart_eq_scalarValue`, so the power-series,
   boundedness/continuity, analytic exceptional-locus, and removability inputs
   are no longer hidden in prose.  The removable theorem is now pinned as a
   consumer of `BHW.sourceGramVariety_normal_riemannExtension`: apply the
   normal analytic-space Riemann theorem to the max-rank chart section using
   `BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_maxRank` for
   the dense complement hypothesis.  The Riemann theorem internally uses the
   relative-open witness for `U` and returns the domain-control field
   `U0 ∩ BHW.sourceComplexGramVariety d n ⊆ U`.  Chart constructors must
   still preserve
   their branch-provenance fields until the descent theorem builds the
   `SourceVarietyGermHolomorphicOn` local representatives.
   The chart overlap compatibility is discharged by
   `BHW.hallWightman_localScalarChart_overlap_eq`: a scalar point in the
   overlap of two chart slices is first realized as an ordinary extended-tube
   Gram point using either chart's `U0_sub` field, and then both chart values
   are rewritten to the same `extendF F w` by their `branch_eq` fields.  No
   equality of arbitrary ambient representatives off the source Gram variety
   is used.
   The descent theorem itself uses
   `BHW.hallWightman_localScalarChart_eq_scalarValue` to convert each local
   branch chart into a `SourceVarietyGermHolomorphicOn` representative for the
   single branch-defined scalar value `Phi`; the exceptional removable chart
   consumes the same `Phi`, together with its continuity and local boundedness,
   so there is no second hidden choice of scalar values.
   The continuity/local-boundedness theorem is deliberately upstream of the
   exceptional chart theorem: it defines the scalar value by an
   extended-tube realization and uses Lemma 3 to realize nearby scalar-variety
   points inside any prescribed extended-tube neighborhood, then applies
   continuity of `extendF` on the ordinary extended tube.  It must not call
   `hallWightman_localScalarChart_at`, which would make the removability
   argument circular.
   The max-rank chart helper
   `BHW.hallWightman_powerSeriesChart_branch_eq_of_sameGram` must carry the
   source-vector inclusion `Uvec ⊆ BHW.ExtendedTube d n`; the branch law cannot
   be applied to the Lemma-3 realization without that hypothesis.  In the
   Lemma-5 power-series proof, the selected-coordinate reinflation theorem
   `BHW.hallWightman_selectedScalarFunction_to_fullGramChart` must consume the
   local selected-coordinate differentiability on the actual product factor
   `Us` returned by `BHW.holomorphic_product_independent_of_auxiliary`; it must
   not silently strengthen this to differentiability on a global
   selected-coordinate image of the source Gram variety.  The product theorem
   must require `C.Ucoord = Us × Ua` with `Ua` connected and nonempty: zero
   derivative in auxiliary directions only proves independence on each
   connected auxiliary component, so the theorem is false without this field.
   The proof defines `Ψs u := g (u, vbase)` for some `vbase ∈ Ua`, proves
   differentiability on `Us`, and uses connectedness of `Ua` to identify
   `g (u,v)` with that base value for every `(u,v) ∈ Us × Ua`.  This
   constancy step is the exact Mathlib theorem
   `IsOpen.is_const_of_fderiv_eq_zero` from
   `Mathlib.Analysis.Calculus.MeanValue`, applied to the fixed-`u`
   auxiliary slice and `hUa_conn.isPreconnected`; before applying it, the
   proof must identify the slice derivative with the auxiliary derivative by
   the chain rule for `v ↦ (u, v)` and `ContinuousLinearMap.inr`.  The product
   chart itself must be obtained by shrinking the inverse-function-theorem
   coordinate target: `isOpen_prod_iff` gives a product neighborhood inside
   the target, then the auxiliary factor is shrunk to a finite-dimensional
   ball using `Metric.mem_nhds_iff`, `Metric.isOpen_ball`, and
   `Metric.isConnected_ball`.  The final coordinate split must restrict the
   local homeomorphism to this product so that
   `C.Ucoord = Set.prod Us Ua` holds by definition; a mere inclusion
   `Us × Ua ⊆ C.Ucoord` is not enough for the auxiliary-independence theorem.
   The full
   scalar chart is obtained by shrinking `C.U0` to
   `C.U0 ∩ {Z | C.scalarCoord Z ∈ Us}` after writing
   `C.Ucoord = Us × Ua`; the selected-coordinate differentiability input is
   exactly on `Us`, not on the larger projection set
   `{u | ∃ v, (u,v) ∈ C.Ucoord}`.  The theorem
   `BHW.hallWightman_powerSeries_from_PDE_span` carries the maximal scalar-rank
   hypothesis `HWSourceGramMaxRankAt d n z0`; this is not redundant with the
   PDE-span hypothesis, because constant-rank shrinking is what makes the
   selected scalar coordinates control the full source-Gram differential image
   throughout the product chart.
   The same Lemma-5 packet must carry the full local differentiable chart
   data, not just a topological coordinate equivalence: `coordMap` and
   `coordSymmMap` are differentiable on the selected opens and inverse there.
   It must also carry local, not merely basepoint, scalar differential data:
   `BHW.HWPowerSeriesCoordinateSplit.sourceGramDifferentials_selected_local`
   says selected scalar differentials span the full source-Gram differential
   image at each chart point, while `BHW.HWPowerSeriesCoordinateSplit.span_local`
   is filled after shrinking to the constant-rank non-exceptional chart.  The
   named source of both fields is
   `BHW.hallWightman_maxRank_selectedScalarDifferentials_local`.  The
   finite-dimensional basis packet must include
   `SelectedScalarCoordinatesBasis.card_eq_expected : e =
   BHW.sourceGramExpectedDim d n`; independence of the selected differentials
   on the shrunken chart is not enough to prove that all source-Gram
	   coordinate differentials lie in their span without this dimension equality.
	   `BHW.hallWightman_auxiliaryDerivative_zero` first differentiates
	   `coordMap (coordSymmMap p) = p` to kill selected scalar derivatives on
	   auxiliary tangents, then uses the selected-span field to kill all source
	   Gram differentials, and finally derives Lemma-4 PDE pointwise from
	   `BHW.hallWightman_lorentzInfinitesimalEquations`.  Lemma 4 itself is now
	   implementation-level: convert the skew matrix to
	   `ComplexLorentzGroup.IsInLieAlgebra`, define
	   `expCurve A t = ComplexLorentzGroup.expLieAlg (t • A.val)`, prove the
	   generated action has derivative
	   `lorentzInfinitesimalTangent d n A z0` at `0`, compose with the
	   differentiability of `extendF F` on the open ordinary extended tube, and
	   identify the derivative with zero because
	   `BHW.extendF_complexLorentzInvariant_of_cinv` makes
	   `extendF F (expCurve A t · z0)` constant in `t`.  This step may not be
	   replaced by an ambient invariant-function theorem.  Lemmas 6--7 are also
	   expanded to implementation level: prove that the kernel of the source Gram
	   differential at a max-rank point is exactly the range of infinitesimal
	   Lorentz tangents, using the infinitesimal Witt-extension theorem, then
	   factor every covector annihilating those tangents through the source Gram
	   differential and expand the resulting finite-product dual functional in
	   coordinate scalar-product differentials.
	   In the
   Lean-shaped proof, destruct
   `hZU : Z ∈ sourceExtendedTubeGramDomain d n` as
   `⟨z0, hz0, rfl⟩`, and when applying the helper to a realized
   extended-tube point `w`, add the variety membership
   `⟨w, rfl⟩` to upgrade `sourceMinkowskiGram d n w ∈ U0 ∩ O` to
   membership in `(U0 ∩ O) ∩ sourceComplexGramVariety d n`.
4. `BHW.sourceScalarRepresentativeData_of_branchLaw`: assemble
   `BHW.SourceScalarRepresentativeData` with
   `U = BHW.sourceExtendedTubeGramDomain d n`, using the relative-open,
   connectedness, descent, and branch-equality fields.
5. `BHW.hallWightman_sourceScalarRepresentativeData` composes the preceding
   four obligations for a general forward-tube function; only then does
   `BHW.sourceScalarRepresentativeData_bvt_F` specialize it using
   `bvt_F_holomorphic` and
   `bvt_F_complexLorentzInvariant_forwardTube`, both transported across
   `BHW_forwardTube_eq` to the `BHW.ForwardTube` API used by the source
   theorem statement.

None of these five surfaces is currently implemented in Lean; the current
production file `BHWPermutation/SourceExtension.lean` intentionally keeps this
Hall-Wightman/BHW branch-law theorem in proof docs until the proof or an
approved source-import boundary is available.

Current readiness verdict: production Lean must still stop before
`BHW.sourceScalarRepresentativeData_bvt_F`.  The germ API and the downstream
source-variety consumers are checked production infrastructure, and the
adjacent path API has now been verified locally, but the upstream
Hall-Wightman scalar representative theorem still depends on either
implementation of the named Lemma-2, Lemma-3, Lemma-5--7, and normal
analytic-space removable packets, or an explicit user-approved source-import
boundary with exactly those theorem statements and no theorem-2/locality
content.  Adding the five theorem names to production without those proofs
would be wrapper churn, not mathematical progress.

Germ-API migration transcript before any Hall-Wightman production theorem:

1. In `BHWPermutation/SourceExtension.lean`, keep the existing
   `SourceVarietyHolomorphicOn` only as a legacy strong sufficient predicate
   and add the active predicate:

   ```lean
   def BHW.SourceVarietyGermHolomorphicOn
       (d n : ℕ)
       (Φ : (Fin n -> Fin n -> ℂ) -> ℂ)
       (U : Set (Fin n -> Fin n -> ℂ)) : Prop :=
     ∀ Z, Z ∈ U ->
       ∃ U0 Ψ,
         IsOpen U0 ∧ Z ∈ U0 ∧
         DifferentiableOn ℂ Ψ U0 ∧
         Set.EqOn Φ Ψ (U0 ∩ BHW.sourceComplexGramVariety d n) ∧
         U0 ∩ BHW.sourceComplexGramVariety d n ⊆ U
   ```

   Also add the elementary support helper
   `BHW.IsRelOpenInSourceComplexGramVariety.subset`:

   ```lean
   theorem BHW.IsRelOpenInSourceComplexGramVariety.subset
       {U : Set (Fin n -> Fin n -> ℂ)}
       (hU : BHW.IsRelOpenInSourceComplexGramVariety d n U) :
       U ⊆ BHW.sourceComplexGramVariety d n := by
     rcases hU with ⟨U0, hU0_open, hU_eq⟩
     intro Z hZU
     rw [hU_eq] at hZU
     exact hZU.2
   ```

   The support lemmas are not wrappers: they expose exactly the analytic-space
   operations needed by downstream theorem 2:
   `SourceVarietyHolomorphicOn.to_germ`,
   `SourceVarietyGermHolomorphicOn.continuousOn` with the subset hypothesis
   `U ⊆ sourceComplexGramVariety d n`,
   `SourceVarietyGermHolomorphicOn.of_subset_relOpen`,
   `SourceVarietyGermHolomorphicOn.sub`, and
   `SourceVarietyGermHolomorphicOn.precomp_sourcePermuteComplexGram`.
   In `precomp_sourcePermuteComplexGram`, the local representative is
   `Ψ ∘ sourcePermuteComplexGram n σ` on the preimage of the old chart; the
   variety-slice equality uses
   `sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff`.

2. Change the two production data/predicate fields in
   `SourceExtension.lean`, not by adding parallel public structures:

   ```lean
   structure BHW.SourceScalarRepresentativeData ... where
     ...
     Phi_holomorphic :
       BHW.SourceVarietyGermHolomorphicOn d n Phi U

   def BHW.sourceDistributionalUniquenessSetOnVariety ... : Prop :=
     E.Nonempty ∧
       ∀ U Φ Ψ,
         BHW.IsRelOpenInSourceComplexGramVariety d n U ->
         IsConnected U ->
         (∀ G ∈ E, BHW.sourceRealGramComplexify n G ∈ U) ->
         BHW.SourceVarietyGermHolomorphicOn d n Φ U ->
         BHW.SourceVarietyGermHolomorphicOn d n Ψ U ->
         (∀ G ∈ E,
           Φ (BHW.sourceRealGramComplexify n G) =
             Ψ (BHW.sourceRealGramComplexify n G)) ->
         Set.EqOn Φ Ψ U
   ```

   Transitional aliases may be private inside one commit if needed for local
   proof organization, but the public theorem-2 surface must not expose both
   a strong and a germ version.  The strong predicate can still map into the
   germ predicate by `SourceVarietyHolomorphicOn.to_germ`.

3. In `BHWPermutation/SourceComplexDensity.lean`, the germ consumers are
   ported under the production theorem names, rather than under parallel
   `_germ` wrappers.  The checked declarations have the following shapes:

   ```lean
   theorem BHW.SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram
       {U : Set (Fin n -> Fin n -> ℂ)}
       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
       {V : Set (Fin n -> Fin (d + 1) -> ℂ)}
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hGramU : BHW.sourceMinkowskiGram d n '' V ⊆ U) :
       DifferentiableOn ℂ
         (fun z => H (BHW.sourceMinkowskiGram d n z)) V

   theorem BHW.sourceComplexGramVariety_identity_principle
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hU_conn : IsConnected U)
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0 U
   ```

   The identity-principle port is not one monolithic rename.  The internal
   germ ladder is present before the public theorem is used downstream:

   ```lean
   theorem BHW.sourceComplexGramVariety_rankExact_local_identity_near_point
       (hD : d + 1 < n)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hZ0U : Z0 ∈ U)
       (hZ0reg :
         Z0 ∈ BHW.sourceSymmetricRankExactStratum n (d + 1))
       (hA_rel :
         ∃ A0, IsOpen A0 ∧
           A = A0 ∩
             (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
       (hZ0_closure : Z0 ∈ closure A)
       (hA_zero : Set.EqOn H 0 A) :
       ∃ V, Z0 ∈ V ∧
         (∃ V0, IsOpen V0 ∧
           V = V0 ∩
             (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))) ∧
         Set.EqOn H 0 V

   theorem BHW.sourceComplexGramVariety_rankExact_identity_principle_of_connected
       (hD : d + 1 < n)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hUreg_conn :
         IsConnected
           (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0
         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))

   theorem BHW.sourceComplexGramVariety_identity_principle_of_connected_rankExact
       (hD : d + 1 < n)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hUreg_conn :
         IsConnected
           (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0 U

   theorem BHW.sourceComplexGramVariety_rankExact_identity_principle
       (hD : d + 1 < n)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hU_conn : IsConnected U)
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0
         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))

   theorem BHW.sourceComplexGramVariety_identity_principle_easy
       (hn : n <= d + 1)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hU_conn : IsConnected U)
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0 U
   ```

   `sourceComplexGramVariety_identity_principle` is then only the final
   arity split:

   ```lean
   by_cases hn : n <= d + 1
   · exact BHW.sourceComplexGramVariety_identity_principle_easy
       hn hU_rel hU_conn hW_rel hW_ne hW_sub hH hW_zero
   · have hD : d + 1 < n := by omega
     exact BHW.sourceComplexGramVariety_identity_principle_of_connected_rankExact
       hD hU_rel
       (BHW.sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
         d n hD hU_rel hU_conn)
       hW_rel hW_ne hW_sub hH hW_zero
   ```

   The final dense-extension line inside
   `sourceComplexGramVariety_identity_principle_of_connected_rankExact`
   must call

   ```lean
   BHW.sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact
     d n (Nat.le_of_lt hD) hU_rel
     (BHW.SourceVarietyGermHolomorphicOn.continuousOn d n hH
       (BHW.IsRelOpenInSourceComplexGramVariety.subset hU_rel))
     hzero_reg
   ```

   `comp_sourceMinkowskiGram` is a local representative proof: at `z ∈ V`,
   choose `U0, Ψ` for `H` at `sourceMinkowskiGram d n z`, shrink the source
   by the open preimage of `U0`, and rewrite to
   `Ψ ∘ sourceMinkowskiGram` because every Gram value lies in
   `sourceComplexGramVariety d n` by definition.  The identity principle uses
   the same rank-exact, connected-regular-locus, and density proof already
   checked before the migration; the only changes are replacing composition by
   the germ local representative and using
   `SourceVarietyGermHolomorphicOn.continuousOn
     (BHW.IsRelOpenInSourceComplexGramVariety.subset hU_rel)`
   in the dense lower-rank extension.

   `BHW.os45AdjacentScalarEq_on_quarterTurnCorridor` has been ported in the
   same file: it proves `hΨ_holo`, `hΦ_holo`, and `hH_holo` with the germ
   `of_subset_relOpen`, `precomp_sourcePermuteComplexGram`, and `sub`, and
   calls `sourceComplexGramVariety_identity_principle`.

4. In `BHWPermutation/SourceComplexLocalChart.lean`, the checked germ chart
   pullback is:

   ```lean
   theorem BHW.SourceVarietyGermHolomorphicOn.comp_differentiableOn_chart
       {D : Set (Fin N -> ℂ)}
       {Γ : (Fin N -> ℂ) -> (Fin n -> Fin n -> ℂ)}
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hΓU : Γ '' D ⊆ U)
       (hΓvar : Γ '' D ⊆ BHW.sourceComplexGramVariety d n)
       (hΓdiff : DifferentiableOn ℂ Γ D) :
       DifferentiableOn ℂ (fun z => H (Γ z)) D
   ```

   and `sourceVariety_localChart_totallyReal_zero` now takes
   `SourceVarietyGermHolomorphicOn`.  The selected-chart theorem already
   exports `hΓvar`; this is exactly the missing equality domain for the germ
   representative.  No new Hall-Wightman theorem is hidden here.

5. In `BHWPermutation/SourceDistributionalUniqueness.lean`,
   `sourceDistributionalUniquenessSetOnVariety_of_realEnvironment` now sets
   `H := Φ - Ψ`, builds `hH` using
   `SourceVarietyGermHolomorphicOn.sub`, calls the germ local-chart theorem,
   then calls `sourceComplexGramVariety_identity_principle`.  The proof
   shape and mathematical content stay the same; only the analytic predicate
   is corrected.

Second, the adjacent `S'_n` seed package must be proved in the order
documented below:
`BHW.os45Figure24_sourceChart_at`,
`BHW.os45SPrime_sourcePullback_pairing_eq_permutedSchwinger`,
`BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`,
`BHW.os45AdjacentSPrimeScalarizationChart_of_figure24`,
`BHW.os45AdjacentSPrimeSourceEq_of_compactWickPairingEq`,
`BHW.os45AdjacentSPrimeScalarSeed_of_compactWickPairingEq`, and
`BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq`.  The
checked `BHW.os45AdjacentQuarterTurnScalarCorridor_of_figure24` may only be
called after that path-and-seed package exists.  None of these inputs may be
replaced by final real-edge equality, `AdjacentOSEOWDifferenceEnvelope`,
global PET branch independence, or a local boundary functional standing in
for `bvt_W`.

The adjacent scalar-trace theorem has one genuine upstream source sublemma:
`BHW.os45SPrime_sourcePullback_pairing_eq_permutedSchwinger`.  It must compare
the permuted Hall-Wightman source pullback with the permuted Schwinger
functional `OS.S n ψZ` in compact pairings on the selected Figure-2-4 chart.
Only after that source-pairing statement is proved may
`BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`
rewrite `OS.S n ψZ` by `bvt_euclidean_restriction` and the finite permutation
change of variables used in
`os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`.  The currently private
helper `integral_perm_npoint_volume` must be exposed or reproved at the first
public call site.

For the path package, the exact Lean topology API is now pinned.  In the
finite-dimensional source space, use
`(IsOpen.isConnected_iff_isPathConnected hUsrc_open).mp hUsrc_conn` to turn
the open connected source chart `Usrc` into `IsPathConnected Usrc`; use
`IsPathConnected.joinedIn` to get a `JoinedIn Usrc zreg zwick0`; extract the
configuration path by `JoinedIn.somePath` and keep membership by
`JoinedIn.somePath_mem`.  Push this path forward with `Path.map` along the
globally continuous `sourceMinkowskiGram` map.  Concatenate the resulting
scalar path to the Figure-2-4 scalar path with `Path.trans` (method form
`γseed.trans γfig`); range control for the concatenated path is exactly
`Path.trans_range`, or equivalently two applications of `JoinedIn.trans` if
the proof is phrased as joined-in data.  Do not cite an unspecified "path
concatenation lemma" here.

Local API audit, 2026-05-01: the names in the preceding paragraph have been
checked against the local Mathlib tree.  The exact files are:
`Mathlib/Topology/Connected/LocPathConnected.lean` for
`IsOpen.isConnected_iff_isPathConnected`,
`Mathlib/Topology/Connected/PathConnected.lean` for
`JoinedIn.somePath`, `JoinedIn.somePath_mem`, and `JoinedIn.trans`, and
`Mathlib/Topology/Path.lean` for `Path.trans` and `Path.trans_range`.  If the
archived overlap-cover connectedness proof is ever revived, the checked
connected-union theorem is
`IsConnected.biUnion_of_reflTransGen` in
`Mathlib/Topology/Connected/Basic.lean`; its Lean signature requires an
explicit nonempty index set `t.Nonempty` and a relation of the form
`ReflTransGen (fun i j => (s i ∩ s j).Nonempty ∧ i ∈ t) i j`.  Therefore the
proof docs must not say merely "the connected union theorem applies": they
must provide the active-label nonemptiness and the exact intersection graph
relation if this package becomes active.

For the adjacent `S'_n` source-equality theorem, the exact analytic API is
also pinned.  Pulling a scalar representative back to `Usrc` uses the germ
signature
`BHW.SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram hPhi hGramU`, where
`hGramU : sourceMinkowskiGram d n '' Usrc ⊆ hRep.U` for the identity branch
and
`hGramU : sourceMinkowskiGram d n '' Usrc ⊆
{Z | sourcePermuteComplexGram n τ Z ∈ hRep.U}` for the adjacent branch.  The
Figure-2-4 source chart must export both the forward Wick membership
`∀ x ∈ V0, (fun k => wickRotatePoint (x k)) ∈ Usrc` and the reverse
real-section equivalence
`∀ x, (fun k => wickRotatePoint (x k)) ∈ Usrc ↔ x ∈ V0`; the latter is what
feeds the last hypothesis of `eqOn_openConnected_of_eqOn_wickRealSection`.
The required continuity of the real Wick section must be exposed as the public
helper `BHW.continuous_wickRotateRealConfig`.  The proof already exists only
as the private helper `continuous_wickRotateRealConfig` in
`OSToWightmanTubeIdentity.lean`; the Lean port must either export that proof
under the `BHW` support namespace or reprove it coordinatewise at the first
call site.

The theorem-2 blueprint now names the two implementation data carriers that
must exist, or be kept as local variables with the same fields:
`BHW.OS45Figure24SourceChartAt`, carrying `V0`, `Usrc`, Wick membership,
Wick real-section equivalence, double-domain membership, and forward-tube
membership of the identity Wick branch; and
`BHW.OS45AdjacentSPrimeScalarSeedWithSourceProvenance`, carrying the scalar
seed together with `Usrc`, `zreg`, `Gseed`, `hwick_mem`, `zreg ∈ Usrc`, and
the source-level double-domain field needed by the path segment.  These are
not substitute theorem routes; they are provenance-preserving forms of the
same OS I §4.5 / BHW seed proof.

The source-chart constructor
`BHW.os45Figure24_sourceChart_at` must consume the actual Figure-2-4
path-stability field from the checked selector, not merely the ordered/Jost
facts for an arbitrary `V`.  Its new `hV_figPath` input gives, for every
`x ∈ V`, paths `Γ, Δ` with `Γ 0 = wick x`, both paths in the ordinary
extended tube, and
`sourceMinkowskiGram (Δ t) =
sourcePermuteComplexGram τ (sourceMinkowskiGram (Γ t))`.  This is what proves
the base Wick source Gram lies in the adjacent double scalar domain before
the connected source neighborhood is chosen.  The topology shrink is then
Lean-ready: use the explicit `BHW.wickRealSectionLeftInverse`,
`BHW.continuous_wickRealSectionLeftInverse`,
`BHW.continuous_wickRotateRealConfig`, and
`BHW.exists_connected_sourceNeighborhood_with_wickPreimage`; set
`V0 := {x | wick x ∈ Usrc}` so the reverse real-section equivalence is
definitionally available.

New route correction for the adjacent scalarization chart: the Figure-2-4
hypothesis
`(fun k => x (τ k)) ∈ EuclideanOrderedPositiveTimeSector τ` does not imply
`(fun k => wickRotatePoint (x (τ k))) ∈ BHW.ForwardTube d n`.  Because
`EuclideanOrderedPositiveTimeSector τ` already applies a further `τ`
relabeling, and an adjacent swap is self-inverse, the standard theorem
`wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector` applied to that
hypothesis returns the identity Wick trace, not the adjacent raw Wick trace.
Therefore `BHW.OS45Figure24SourceChartAt` must not contain a
`wick_tau_forwardTube` field, and
`BHW.os45AdjacentSPrimeScalarizationChart_of_figure24` must not prove its
adjacent Wick identity by `SourceScalarRepresentativeData.branch_eq` followed
by `BHW.extendF_eq_on_forwardTube` at `wick (x ∘ τ)`.

The genuine missing theorem is now named explicitly:
`BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`.  It
must prove, on the Figure-2-4 source chart, equality of compact pairings
between the permuted source pullback
`x ↦ hRep.Phi (sourcePermuteComplexGram n τ
(sourceMinkowskiGram d n (fun k => wickRotatePoint (x k))))`
and the OS-II adjacent Wick trace
`x ↦ bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k)))`.  The pointwise
version is not an input to the seed proof; using it there is circular because
it already asserts the adjacent `S'_n` scalarization on the Wick real section.
Its proof is the local OS I §4.5/BHW scalar-trace comparison: use the OS-II
ACR(1) Euclidean continuation package and compact-test permutation symmetry
to identify pairings on the selected `S'_n` chart.  It must not be replaced by
the global pointwise theorem `bvt_F_perm`, by final `bvt_W` locality, by
`AdjacentOSEOWDifferenceEnvelope`, or by PET branch independence.  Until this
theorem has a complete proof transcript, the adjacent `S'_n` package is not
Lean-ready.

Readiness gate for production Lean: the theorem-2 blueprint must remain the
source of truth for Lean-shaped pseudocode.  The scalar-source theorem is not
implementation-ready until its proof is expanded through the Hall-Wightman
Lemma-2 fiber alternative, the singular null-contraction limit, Lemma-3
relative-openness, and Lemmas-4--7 local scalar-product holomorphicity.  The
branch-law rank split in those sublemmas must be the scalar-product rank split
`min d n <= sourceGramMatrixRank` versus `sourceGramMatrixRank < min d n`,
not `SourceComplexGramRegularAt`; the local holomorphic-chart split is the
different maximum-rank threshold `min (d+1) n`.  After the latest doc pass
those are named as the specific sublemmas above, including the power-series
and removable-singularity packet; the
remaining review question before Lean on the scalar-representative theorem is
whether each named Hall-Wightman
sublemma has a fully audited source proof or approved source-import boundary,
not whether theorem-2 may bypass them.  The
adjacent `S'_n` package is not implementation-ready unless the proof keeps the
source-chart provenance needed by the path theorem: `V0`, `Usrc`, `zreg`,
`Gseed`, the Wick real-section equivalence for `Usrc`, the specialized proof
`zwick0 ∈ Usrc` or its source `hwick_mem`, and the Figure-2-4 realization path
must all survive as explicit fields until
`BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq` is proved.
Discarding this provenance and recreating it later would be a documentation
gap, not a Lean convenience.

The current proof-document pass now separates upstream and downstream source
content:

1. `hUfig_source` is explicitly only domain geometry.  It supplies Jost
   membership, identity/adjacent extended-tube membership, and the two OS45
   pulled-domain memberships; it does not compare branch values.
2. `BHW.os45BranchHorizontalSourceGermAt_of_figure24_id` and
   `BHW.os45BranchHorizontalSourceGermAt_of_figure24_adjacent` are upstream
   one-branch OS I §4.5/BHW source suppliers.  They must also consume the
   closure-level ordered-sector fields from the selected `V`: the identity
   supplier uses `hV_ordered_closure`, and the adjacent supplier uses both
   `hV_ordered_closure` and `hV_swap_ordered_closure` after relabelling.  These
   ordered fields are not optional, because they are what make
   `BHW.os45CommonEdge_mem_acrBranchDomain_of_ordered` available at the
   horizontal base point.  The adjacent scalar packet is produced in the
   original identity coordinates at
   `y0 = BHW.os45CommonEdgeRealPoint 1 x`; the one-branch source-patch assembly
   is then applied on the relabelled ordered branch `x ∘ τ` after rewriting the
   packet basepoint by `BHW.os45CommonEdgeRealPoint_adjacent_swap_eq`, and the
   packaged source-germ predicate is rewritten back to `y0` by the same checked
   equality.  This is only basepoint transport for one branch.  It must not use
   an
   `AdjacentOSEOWDifferenceEnvelope`, real-edge adjacent equality, final
   `bvt_W` locality, or global PET branch independence.
3. Both suppliers factor through the exact one-branch theorem
   `BHW.os45BranchHorizontalSourceGermAt_of_oneBranch_sourcePatch`.  Its
   genuine content is the BHW source/edge statement that, on one selected
   Figure-2-4 source patch and for one fixed branch label `β`, the OS-II ACR
   representative `bvt_F (permAct β.symm (Q.symm z))` and the pulled BHW
   representative `extendF (bvt_F) (permAct β.symm (Q.symm z))` are two
   continuations of the same local germ.  This former proof-doc target has now
   been expanded as a one-branch BHW theorem, not as adjacent equality.  The
   theorem is split in the blueprint into a pure source-neighborhood
   geometry part and the genuine value-agreement theorem
   `BHW.os45OneBranchACRBHWAgreement_of_sourcePatch`.  The geometry fields
   choose the neighborhood, use ordered-sector membership for the ACR side,
   and ensure the pulled BHW argument lies in the extended tube; they do
   **not** prove the ACR/BHW equality.  Jost and ordinary extended-tube fields
   remain upstream in the scalar-packet suppliers; the generic source-patch
   assembly no longer carries them after `hScalar` is supplied.  The agreement
   theorem is now further
   split around the explicit scalar packet
   `BHW.OS45OneBranchScalarGramEqPacket`: the public identity and adjacent
   source suppliers produce this packet, while
   `BHW.os45OneBranchACRBHWAgreement_sourceInput` only consumes it and converts
   it into a neighborhood contained in both branch domains plus the required
   `Set.EqOn` equality.  The packaging theorem
   `BHW.os45OneBranchACRBHWAgreement_of_sourcePatch` also consumes the same
   packet together with the source-patch geometry.  The algebraic reduction from
   local Gram equality to ACR/BHW equality is now named
   `BHW.os45OneBranchACRBHWAgreement_of_scalarGramEq`: after a
   `SourceScalarRepresentativeData` packet supplies equality of the two
   scalar-product Gram arguments, the proof is just the checked orientation of
   `SourceScalarRepresentativeData.branch_eq`, `sourceMinkowskiGram_perm`,
   `bvt_F_perm`, and
   `BHW.extendF_eq_on_forwardTube`.  The scalar packet must be produced from
   the explicit local `S'_n` source suppliers
   `BHW.os45OneBranchScalarGramEq_sourceInput_id` and
   `BHW.os45OneBranchScalarGramEq_sourceInput_adjacent`; there is no public
   arbitrary-`β` theorem manufacturing it from source-domain geometry alone.
   These suppliers obtain the ordinary `SourceScalarRepresentativeData`,
   construct a relatively open scalar neighbourhood inside the relevant double
   scalar domain, prove equality of `Phi` and its permuted pullback from the
   identity simplification or the OS-II symmetric `S'_n` seed, and then pull
   the result back through
   `sourceMinkowskiGram (Q.symm z)`.  This is the local Hall-Wightman/BHW
   source theorem layer that the first theorem-2 Lean pass must implement
   before touching the downstream EOW envelope.

   The latest blueprint correction rejects the earlier real-environment seed
   formulation.  At the OS45 horizontal edge the point
   `sourceMinkowskiGram d n (Q.symm (realEmbed (os45CommonEdgeRealPoint β x)))`
   is generally a complex quarter-turn scalar point, not
   `sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)`.  Therefore
   the seed cannot be stated as direct equality on a real Minkowski Gram
   environment.  The proof must instead use the OS §4.5 order:
   `BHW.os45AdjacentSPrimeScalarSeed_of_compactWickPairingEq` obtains a
   connected nonempty relatively open scalar seed in `S'_n` in two explicit
   steps.  First
   `BHW.os45AdjacentSPrimeSourceEq_of_compactWickPairingEq` proves equality
   on a connected complex source-neighborhood `Usrc`, using the checked
   compact Wick equality
   `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`, the
   Wick-section identity principle, and the explicit OS-I §4.5 adjacent
   source-chart scalarization theorem
   `BHW.os45AdjacentSPrimeScalarizationChart_of_figure24`, which puts
   `sourceMinkowskiGram '' Usrc` inside the adjacent double scalar domain,
   identifies the identity `hRep.Phi` pullback pointwise with the identity
   OS-II Wick branch, identifies the adjacent `hRep.Phi` pullback with the
   adjacent OS-II Wick branch only in compact pairings, and shrinks around the
   selected base point `x0` so `x0 ∈ V0`.  Its identity branch reduction is the ordinary
   forward-tube `branch_eq`/`extendF_eq_on_forwardTube` argument; its adjacent
   branch reduction is exactly
   `BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`,
   not an adjacent raw-Wick forward-tube argument.  In the
   compact-Wick-to-pointwise step, continuity is needed only for the two
   scalarized source pullbacks.  Obtain it by composing the differentiable
   scalar pullbacks with
   `BHW.continuous_wickRotateRealConfig` using Mathlib
   `ContinuousOn.comp'` and the explicit `MapsTo` proof
   `fun x hx => hwick_mem x hx`.  The integral equality for those scalar
   pullbacks is the chain: adjacent source-pairing theorem, checked compact
   Wick equality, and the identity pointwise scalarization rewritten under the
   integral.  The proof must not silently use continuity of unrelated total
   `bvt_F` values off the Wick section, and must not use
   `ContinuousOn.comp_continuous` unless the
   chart has been changed to a global Wick-image statement.  The checked
   compact Wick equality is called with
   `ρ = 1`, so its swapped-order hypothesis is labelled by
   `(Equiv.swap i ⟨i.val + 1, hi⟩).symm * 1`; normalize this to the local
   adjacent transposition `τ` with `Equiv.swap_inv` and `mul_one` before
   passing `hV_swap_ordered`.  Then a complex regular point is chosen near the Wick
   source point for `x0` by `BHW.dense_sourceComplexGramRegularAt`, and scalar coordinates are
   extracted with the all-arity connected local-image packet
   `BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular_allArity`;
   in the hard range this is the checked
   `BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`,
   while in the easy range it uses the checked full symmetric-coordinate
   identification of the source variety.  The path provenance needed by the
   corridor is packaged in
   `BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq`, whose
   extra output is anchored at the same selected base point `x0`: the scalar
   seed theorem records a distinguished `Gseed ∈ Wseed`, the source chart
   supplies a path from `Gseed` to
   `sourceMinkowskiGram d n (fun k => wickRotatePoint (x0 k))`, and
   the selected Figure-2-4 source patch supplies the path-stability field
   `hV_figPath_closure`, recorded on `closure V` because the branch source germ is
   required at every point of the compact edge closure.  That field is the
   actual Streater-Wightman Figure-2-4
   configuration-level path from the Wick configuration to the OS45
   quarter-turn configuration, together with a second continuous
   ordinary-extended-tube realization of the adjacent permuted Gram point.
   The provenance form must keep
   `Gseed_def : Gseed = sourceMinkowskiGram d n zreg`; the path proof should
   either `subst Gseed` and then define
   `γseed : Path (sourceMinkowskiGram d n zreg)
   (sourceMinkowskiGram d n zwick0)`, or keep `Gseed` and cast the mapped
   source path along `Gseed_def`.  Defining `γseed : Path Gseed ...` after
   `subst Gseed` is not Lean-shaped.  Without this field the scalar-only seed
   has lost the endpoint needed by `Path.trans`.
   Its adjacent branch is the Figure-2-4 two-plane rotated realization from
   the checked `AdjacentOverlapWitness.lean` model, made uniform around the
   same equal-time Figure-2-4 anchor by a compact-open shrink over
   `unitInterval`; it is not the bare relabelled path `Γ t ∘ τ`.  The ordered
   seed is chosen only afterward inside `Ufig ∩ Upath`, and the final
   precompact `V` is then shrunk inside the ordered-sector preimages.  The
   blueprint now pins the support names:
   `BHW.os45Figure24IdentityPath`,
   `BHW.figure24RotateAdjacentConfig`,
   `BHW.figure24RotateAdjacentConfig_lorentz_inverse`, and
   `BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability`, whose
   projections include `BHW.swFigure24_adjacentHorizontalRealEnvironment` and
   `BHW.swFigure24_adjacentPathStableNeighborhood_exists`.  The support
   theorem feeding the path-stability neighborhood must also export
   `realEmbed xrot = figure24RotateAdjacentConfig hd
     (realEmbed (fun k => xfig (τ k)))`; otherwise the compact-open
   path-stability proof has no identified base point.  Its proof transcript
   now fixes the actual arithmetic: the identity path uses
   `0 < 1 - (t : ℝ) / 2` for `t : unitInterval`, while the rotated adjacent
   witness has first-axis consecutive differences `2 / 5` at `i`, `1 / 5` at
   `i + 1`, and `(3 / 5) * Δe1` on all other gaps.  Thus the adjacent path
   support is anchored in the checked `(3,4,5)` rotation calculation, not in a
   vague strict-inequality claim.  The only new generic helper on this
   subroute is the finite-subcover tube lemma
   `BHW.exists_open_nhds_forall_mem_of_compact_parameter`, and the Gram
   calculation uses the genuine scalar-product theorem
   `BHW.sourceMinkowskiGram_complexLorentzAction` plus
   `BHW.sourceMinkowskiGram_perm`, with `Equiv.swap_inv` normalizing the
   adjacent transposition inverse from `τ.symm` to `τ`.  The optional theorem
   `BHW.swFigure24_wickToQuarterTurn_doubleETRealizationPath` is only a
   projection from `hV_figPath_closure`, not an independent broad theorem about an
   arbitrary real-open `V`.  The scalar theorem
   `BHW.swFigure24_wickToQuarterTurn_scalarPath` is then only the mechanical
   corollary `γ t = sourceMinkowskiGram d n (Γ t)`, with double-domain
   membership proved by
   `BHW.mem_sourceDoublePermutationGramDomain_iff_exists_realizations`.
   This correction is mandatory: do not assert the scalar path directly, and
   do not claim that the adjacent relabelling of `Γ t` itself lies in the
   ordinary forward tube.  Its paper source is the local OCR of
   `references/pct-spin-and-statistics-and-all-that-9781400884230_compress.pdf`
   around printed page 73: the adjacent transposition `P(j,j+1)` and Figure
   2-4 give a common real Jost environment for the ordinary and adjacent
   permuted extended tubes;
   `BHW.os45AdjacentQuarterTurnScalarCorridor_of_figure24` supplies the
   Hall-Wightman/BHW connected scalar corridor from that seed to the selected
   OS45 quarter-turn scalar neighbourhood by the Figure-2-4 scalar path and
   the finite-dimensional topology theorems
   `BHW.sourceComplexGramVariety_local_connectedRelOpen_basis` and
   `BHW.sourceComplexGramVariety_connectedRelOpenTube_around_compactPath`.
   The corridor assembly is now checked in
   `OSToWightmanLocalityOS45TraceMembership.lean`: after the path `γ` is
   supplied, it thickens `γ` by the connected source component, rewrites the
   adjacent ACR edge through
   `BHW.os45CommonEdgeRealPoint_adjacent_swap_eq`, and pulls the final scalar
   tube back through `z ↦ sourceMinkowskiGram d n (Q.symm z)` while intersecting
   the checked OS45 ACR and pulled BHW branch domains.
   Equality propagation along that corridor is now checked in the generic
   source theorem `BHW.os45AdjacentScalarEq_on_quarterTurnCorridor` in
   `BHWPermutation/SourceComplexDensity.lean`; it is deliberately generic in
   the represented function `F`, so the local theorem depends only on
   `SourceScalarRepresentativeData` and the source-variety identity principle,
   not on unrelated upstream `bvt_F` proof obligations.
   The singular Schur branch of the local-basis theorem uses the explicit
   rank-`<=` cone package
   `BHW.matrixSymmetricRankLECone_small_connected`,
   `BHW.isConnected_sourcePrincipalSchurGraph_rankLE_image`, and
   `BHW.sourcePrincipalSchurGraph_rankLE_image_eq_openCoordinatePatch`; it is
   not allowed to reuse the checked rank-exact cone theorem as if the
   lower-rank source variety were rank-exact;
   and
   `BHW.os45AdjacentScalarEq_on_quarterTurnCorridor` propagates equality by
   the source-variety identity theorem.  No real-edge `extendF` equality,
   `AdjacentOSEOWDifferenceEnvelope`, final `bvt_W` locality, or global PET
   branch-independence is allowed in these upstream source suppliers.

   The generic arbitrary-`β` theorem is not licensed as a standalone
   production source theorem until the same `S'_n` seed and BHW corridor are
   proved for arbitrary `β`; on the active theorem-2 path it should be
   implemented only as an assembly lemma consuming
   `BHW.OS45OneBranchScalarGramEqPacket`.  The
   public scalar suppliers are
   `BHW.os45OneBranchScalarGramEq_sourceInput_id` for `β = 1` and
   `BHW.os45OneBranchScalarGramEq_sourceInput_adjacent` for the adjacent
   swap; any generic helper is private assembly from an already constructed
   scalar corridor.  The identity supplier must reduce
   `sourceDoublePermutationGramDomain d n 1` by the explicit helper
   `BHW.sourceDoublePermutationGramDomain_one_eq`, proved by unfolding
   `sourceDoublePermutationGramDomain` and using
   `BHW.sourcePermuteComplexGram_one`; do not rely on an unstated
   "definitional" simplification of the double-domain field.  The adjacent
   supplier must carry the selected
   pointwise Figure-2-4 path field on its theorem surface.  The higher
   `BHW.os45BranchHorizontalSourceGermAt_of_figure24_adjacent` supplier
   therefore carries `hV_figPath_closure`; for each `x ∈ closure V` it passes
   the corresponding path as `hfig_x0`.  Without that input, the OS45
   quarter-turn scalar point has not been connected to the `S'_n` seed inside
   the adjacent double scalar domain, and the theorem would again be trying to
   infer scalar branch agreement from domain membership.  The closure-point
   suppliers must also choose a fresh local open patch around each
   `x ∈ closure V`; they must not pass the original open `V` to a scalar input
   theorem when only `x ∈ closure V` is known.  The local patch is the finite
   intersection of `Ufig`, the identity and swapped ordered-sector preimages,
   and the relevant horizontal pulled-domain preimage.  In the adjacent case,
   this local original-coordinate patch supplies the scalar packet at `y0`; the
   source-germ assembly step separately transports to the relabelled patch
   `Uτ := {u | (fun k => u (τ k)) ∈ Ux}` and rewrites the scalar packet along
   `BHW.os45CommonEdgeRealPoint_adjacent_swap_eq` before calling
   `BHW.os45BranchHorizontalSourceGermAt_of_oneBranch_sourcePatch`.  This
   preimage definition is equivalent to `{u | ∃ v ∈ Ux, u = fun k => v (τ k)}`
   for an adjacent swap, but it makes openness and basepoint membership
   Lean-direct.  The proof must explicitly transport all five one-branch
   source-patch fields across this finite permutation: openness, Jost membership,
   branch-`τ` ordered membership, ordinary extended-tube membership of the
   relabelled configuration, and horizontal pulled-BHW membership after the
   common-edge rewrite.  The basepoint proof is
   `change (fun k => xτ (τ k)) ∈ Ux; simpa [xτ, τ] using hxUx`; it is not
   automatic from the original `Ux` membership unless this relabelling step is
   performed.  The theorem-2 blueprint now records the checked tactic-shaped
   transport: `hUτ_open` is `hUx_open.preimage` along the continuous finite
   permutation map; `hUτ_jost` applies `BHW.jostSet_permutation_invariant` to
   `v := u ∘ τ`; `hUτ_ordered` consumes the swapped ordered field of `Ux`;
   `hUτ_ET` consumes the adjacent ordinary-ET field; and `hUτ_horiz` rewrites
   `os45CommonEdgeRealPoint τ u` to `os45CommonEdgeRealPoint 1 v` by
   `BHW.os45CommonEdgeRealPoint_adjacent_swap_eq`.
   The selector construction must choose the ordered seed inside
   `Ufig ∩ Upath`, where `Upath` is the Figure-2-4 compact-open
   path-stability neighborhood around the same equal-time witness returned
   with `Ufig`; this shared anchor is what makes the closure-level
   `hV_figPath_closure` field legitimate.  The `Upath` path field is
   conditional on the identity ordered-sector hypothesis: `Upath` itself is an
   open neighborhood of an equal-time anchor, while the final selector obtains
   the full `Γ, Δ` field on `closure V` by combining `closure V ⊆ Upath` with
   `hV_ordered_closure`.  The implementation must not call two independent
   existential theorems for `Ufig` and `Upath` and then assume the witnesses
   agree.
4. The compact common-germ theorem `BHW.os45BranchHorizontalCommonGerm` then
   glues these branch-specific germs over `closure E`; the identity and
   adjacent germs remain different branch packets.
5. The branchwise BV construction gives `Tid` and `Tτ`; only after subtracting
   those packets may `SCV.chartDistributionalEOW_local_envelope` be invoked.
   The subsequent side-component gluing is fixed in those same one-chart
   coordinates: choose `ys` with `∑ j, ys j = η₁`, shrink the selected patch
   so `(SCV.localEOWRealLinearCLE ys hli).symm (η(x))` is coordinatewise
   positive, and define the side components from
   `Ωplus ∩ SCV.ChartPositiveOrthant m` and
   `Ωminus ∩ SCV.ChartNegativeOrthant m`.  Then the local ball overlaps are
   exactly `SCV.StrictPositiveImagBall R` and
   `SCV.StrictNegativeImagBall R`, so the side identities returned by the
   checked one-chart theorem are already the full overlap equalities needed
   for holomorphic gluing; the exact rewrites are the pure topology lemmas
   `SCV.ball_inter_positiveOrthantComponent_eq_strictPositiveImagBall` and
   `SCV.ball_inter_negativeOrthantComponent_eq_strictNegativeImagBall`.
   The finite Wick/real trace membership in those components is reduced to
   the generic helper `SCV.path_endpoint_mem_connectedComponentIn` plus the
   explicit OS45 positive/negative path membership calculations.
   Openness and connectedness of the side components are supplied by
   `SCV.isOpen_connectedComponentIn_complexChart_of_isOpen` and
   `SCV.isConnected_connectedComponentIn_of_mem` from finite-dimensional
   local connectedness and the standard connected-component-in API.
   Disjointness of the positive/negative side components uses the nonzero
   chart dimension through
   `SCV.disjoint_chartPositiveOrthant_chartNegativeOrthant`; do not omit
   `hm : 0 < m`, since the zero-dimensional orthant predicates are vacuous.
   The final holomorphic gluing theorem is
   `SCV.glue_localEnvelope_to_disjoint_sideComponents`, and its output domain
   is part of the contract: it returns `U = U0 ∪ Uplus ∪ Uminus`, not an
   unnamed larger set.  Its proof uses the pure topology helper
   `SCV.isConnected_threeUnion_of_connected_core_meets`, then proves the
   three local `EqOn` facts for the nested-if glued function and combines
   local holomorphy by `DifferentiableOn.congr` plus two applications of
   `DifferentiableOn.union_of_isOpen`.
   Do not replace this by a broad
   original-coordinate linear sign condition; that would reintroduce an
   unproved identity-theorem obligation on arbitrary overlap components.
6. The scalar theorem `BHW.os45AdjacentScalarGerm_of_OSII_Figure24` is
   downstream only.  It may be proved after
   `BHW.os45_adjacent_commonBoundaryEnvelope` and
   `bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`
   have produced real-edge equality.  It is an audit/export of the EOW result,
   not an input to the source suppliers.

The theorem-2 local source route is now a Lean-facing implementation contract
for the named support theorems above.  The previous circular dependence on
the downstream scalar germ has been retired; implementation must still proceed
in the documented order and may not skip ahead to local EOW, global PET branch
independence, or final `bvt_W` locality.

The Figure-2-4 source-selector support packet is now checked; it was the first
allowed Lean pass after the earlier source-route correction.  Its file/order
contract remains fixed for audit purposes: publicize only the
concrete Figure-2-4 witness export
`BHW.figure24_adjacentTwoPlaneRotationSupport` from
`ComplexLieGroups/AdjacentOverlapWitness.lean`; the public axes
`BHW.figure24Axis1`, `BHW.figure24Axis2`, and the finite formula
`BHW.figure24RotateAdjacentConfig` also live there, as does
`BHW.figure24RotateAdjacentConfig_lorentz_inverse`, so the witness export and
the scalar path proof do not depend on the OS45 companion's path topology.
This algebraic export is now checked.  The generic compact parameter tube
lemma, the OS45 identity path, the zero-time identity-path lemma, joint
identity-path continuity, rotation continuity, composed rotated-path
continuity, Lorentz-invariance scalar identity, and
`BHW.swFigure24_adjacentPathStableNeighborhood_exists` are also checked in the
small OS45 Figure-2-4 companion file.  The checkpoint also checked
`BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability` and
`BHW.os45_adjacent_identity_horizontalEdge_sourcePatch`.  The next live work is
therefore the proof-doc-only scalar-source route above, not another
Figure-2-4 selector theorem.  Any theorem that
claims the bare adjacent relabelling of the identity path is forward-tube
valued is off route; the adjacent certificate is the rotated Figure-2-4
extended-tube realization.

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
   checked and consumed by the open-Jost-patch uniqueness theorem under the
   legacy strong API.  The analytic bookkeeping lemma
   `SourceVarietyHolomorphicOn.sub` is checked in `SourceExtension.lean`; the
   corrected scalar-source route now also has the parallel checked germ lemma
   `SourceVarietyGermHolomorphicOn.sub`.  The complex selected-coordinate
   local-IFT substrate
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
   `SourceVarietyGermHolomorphicOn.comp_differentiableOn_chart`,
   and `sourceVariety_localChart_totallyReal_zero` with the germ hypothesis,
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
	   `U`.  The production `SourceVarietyGermHolomorphicOn` hypothesis exposes
	   `ContinuousOn` through the checked
	   `SourceVarietyGermHolomorphicOn.continuousOn` plus the relative-open
	   subset helper, so the continuity-extension lemma applies directly to
	   theorem-2 representatives.
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
	   needed for the local identity-propagation theorem.  On the corrected
	   route the pullback helper is
	   `SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram`; it uses a
	   germ local representative on the source-variety slice.  The local
	   propagation theorem
	   `sourceComplexGramVariety_rankExact_local_identity_near_point` is now
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
	   regular local-image strengthening, and the connected cone lemmas
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
	   variety.  Two checked local-basis surfaces are now distinguished:
	   `sourceComplexGramVariety_local_rankExact_connected_basis` supplies the
	   connected rank-exact regular-locus input used by the identity-principle
	   layer, while `sourceComplexGramVariety_local_connectedRelOpen_basis`
	   supplies the actual connected rank-bounded source-variety tube.  The
	   lower-rank tube is checked by genuine Schur product charts plus the
	   connected rank-`<=` cone lemma, with no zero-Schur wrapper hiding the
	   lower-rank singular case.  The cone lemmas are proved through real
	   finite-dimensional content: nonzero scalar rank invariance, cone
	   invariance of `sourceSymmetricRankExactStratum` and
	   `sourceSymmetricRankLEVariety`, dot-Gram scaling,
	   path-connectedness of the full-rank complex source-configuration
	   Stiefel space using `MatrixLieGroup.GL_isPathConnected`, and the
	   small-ball radial contraction arguments.  The implementation should not
	   cite "rank-exact cone connectedness" as an opaque geometric black box for
	   rank-bounded topology.
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
	   `sourceSymmetricRankExactCone_small_connected`.  It also now checks
	   scalar rank non-increase, rank-`<=` cone invariance, path-connectedness of
	   `Metric.ball 0 ε ∩ sourceSymmetricRankLEVariety m r`, and
	   `sourceSymmetricRankLECone_small_connected`.  The cone blocker is
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
	   graph-image connectedness theorems
	   `isConnected_sourcePrincipalSchurGraph_rankExact_image` and
	   `isConnected_sourcePrincipalSchurGraph_rankLE_image`, together with the
	   rank-exact/rank-`<=` image-subset theorems
	   `sourcePrincipalSchurGraph_rankExact_image_subset` and
	   `sourcePrincipalSchurGraph_rankLE_image_subset`, are now checked too.
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
	   The rank-bounded analogues
	   `sourcePrincipalSchurGraph_rankLE_image_eq_coordinatePatch` and
	   `sourcePrincipalSchurGraph_rankLE_image_eq_openCoordinatePatch` are also
	   checked, so the lower-rank connected source-variety tube is identified
	   with the continuous image of the connected rank-`<=` Schur product.
	   The singular topology target is now checked as
	   `sourceComplexGramVariety_local_rankExact_connected_basis_singular`: it
	   constructs the actual `Aset`, `Bset`, and `Sset` around a lower-rank
	   point and proves the final radius-shrinking and assembly for the singular
	   rank-exact local-basis theorem.  The rank-bounded singular tube is now
	   separately checked as
	   `sourceComplexGramVariety_local_connectedRelOpen_basis_singular`; the
	   strict and all-arity connected local-basis theorems are checked as
	   `sourceComplexGramVariety_local_connectedRelOpen_basis_strict` and
	   `sourceComplexGramVariety_local_connectedRelOpen_basis`.  The easy-arity
	   branch uses connected balls in the full symmetric affine space, while the
	   strict lower-rank branch uses the rank-`<=` Schur tube.  The regular rank
	   The compact-path source tube is now checked by a connected-component
	   argument.  For a relatively open source-variety domain `D` and a point
	   `Z0 ∈ D`, the component `connectedComponentIn D Z0` is relatively open:
	   around each point of the component, the checked local connected basis
	   supplies a connected relatively open neighborhood inside `D`, and
	   `IsPreconnected.subset_connectedComponentIn` plus
	   `connectedComponentIn_eq` places that neighborhood back inside the same
	   component; the component is the union of these local neighborhoods.  The
	   corresponding checked theorem chooses
	   `Wtube = connectedComponentIn D (γ 0)`.  Connectedness and containment are
	   the standard `connectedComponentIn` facts, the starting connected set
	   `W0` lies in the component by
	   `hW0_conn.isPreconnected.subset_connectedComponentIn`, and the path lies
	   in the same component because `Set.range γ` is preconnected.  Thus no
	   finite-subdivision or hidden path-chain lemma remains in this step.
	   The checked declarations are
	   `IsRelOpenInSourceComplexGramVariety.iUnion`,
	   `sourceComplexGramVariety_connectedComponentIn_relOpen`, and
	   `sourceComplexGramVariety_connectedRelOpenTube_around_compactPath`.
	   The regular rank
	   branch of the rank-exact local-basis
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
	   legacy strong-API `sourceComplexGramVariety_identity_principle` in
	   `BHWPermutation/SourceComplexDensity.lean`; the corrected route now
	   exposes the germ analogue under the same name,
	   `sourceComplexGramVariety_identity_principle`, using the same
	   rank-exact/continuity proof and
	   `SourceVarietyGermHolomorphicOn.continuousOn` at the dense-extension
	   step.
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
   packaging: it constructs the common chart, instantiates the checked
   one-chart theorem `SCV.chartDistributionalEOW_local_envelope` at an ordered
   identity-sector horizontal edge, glues the local seed to the OS45 side
   components, and exports a holomorphic branch-difference function with the
   Wick/real trace identities.  The older global
   `SCV.local_distributional_edge_of_the_wedge_envelope` surface is retained as
   a future SCV packaging target, not as the active Slot 1 input.  The
   finite-order primitive shortcut is rejected because the
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
   regularity package.  The later ordered-edge correction changes the immediate
   OS45 boundary-value step: Slot 1 now uses continuous horizontal-edge
   boundary values on a compact local edge window, so the compact-subcone
   strengthening of `bvt_boundary_values` is no longer the local seed blocker.
   Historical note: the next proof-doc frontier at this point was
   `SCV.distributionalHolomorphic_regular`.  That frontier is no longer the
   theorem-2 Slot 1 blocker after the later checked SCV recovery and one-chart
   EOW passes.  The active theorem-2 proof-doc frontier is now the
   identity-order OS45 instantiation of
   `SCV.chartDistributionalEOW_local_envelope`: choose an ordered perturbation,
   use the checked identity selector, reformulate the false horizontal-edge
   common-boundary shortcut, call the one-chart theorem only after the corrected
   boundary-value hypotheses are available, then glue to the finite Wick/real
   traces through side components.  The equal-time local-wedge audit remains as
   the reason the old post-radius plan is retired, not as the next theorem to
   prove.  The blueprint
   still records the Lean
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
		   `SCV.localEOWChart_twoSided_polywedge_mem`.  The remaining
		   theorem-2 supplier blocker is no longer an SCV splice.  It is the OS45
		   identity-order instantiation layer: the ordered seed is checked, but
		   the common-boundary theorem surface must be corrected before the
		   ordered horizontal-edge local wedge, compact-cutoff boundary CLM,
		   one-chart call, and side-component gluing can be implemented.  This is
		   not another distributional EOW theorem and not a wrapper.
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
	   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII`.  The old
	   target `SCV.local_distributional_edge_of_the_wedge_envelope` remains a
	   future global packaging theorem only; the current OS45 supplier consumes
	   the checked `SCV.chartDistributionalEOW_local_envelope` directly.  The
	   identity-order seed selection is now checked in
	   `BHW.choose_os45_identity_real_open_edge_for_adjacent_swap`, and the
	   same-patch domain/trace/geometry package is checked in
	   `BHW.os45_adjacent_identity_localEOWGeometry`.
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

1. the active route is uniquely the OS II / OS I §4.5 branch-difference path:
   selected Figure-2-4 source patch, branchwise horizontal source germs,
   branch BV packets, local EOW envelope, BHW/Jost source continuation, and
   final OS-II boundary transfer to `bvt_W`;
2. the source layer is fixed at the scalar-packet surfaces
   `BHW.OS45OneBranchScalarGramEqPacket`,
   `BHW.os45OneBranchScalarGramEq_sourceInput_id`, and
   `BHW.os45OneBranchScalarGramEq_sourceInput_adjacent`, with no public
   arbitrary-`β` geometry-only source theorem;
3. the Figure-2-4 selector is closure-ready: `Ufig` and `Upath` share one
   anchor, the ordered seed is chosen inside `Ufig ∩ Upath`, and the exported
   path field is `hV_figPath_closure`;
4. the branch-BV and local EOW theorem surfaces name the exact CLMs, side
   wedges, chart-linear kernel pushforwards, and gluing consumers, without
   treating the local boundary functional as `bvt_W`;
5. the downstream Hall-Wightman/Jost and final boundary-transfer slots identify
   which theorem packages consume the local EOW output and where the physical
   `bvt_W` distribution re-enters;
6. every historical shortcut is fenced off: pointwise horizontal equality,
   quarter-turn bypass, boundary-functional demotion, generic PET branch
   independence, and the archived adjacent-word source cover are not active
   implementation options.

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
