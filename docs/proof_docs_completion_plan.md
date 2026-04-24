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
   that distinct permuted forward-tube sectors are disjoint. The active
   replacement is the generic direct BHW source branch-law theorem
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`,
   whose proved PET-algebra assembly theorem is
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry`, and whose
   branch-equality corollary is
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` on permuted
   extended-tube sectors, specialized to the OS witness as
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.  Its generic
   source contract uses restricted real Lorentz invariance plus permutation
   symmetry on the tube family; complex-Lorentz single-valuedness on `S''_n`
   is the Hall-Wightman output, not an input.  The Lean implementation locus is
   the new small file
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
   exactly Hall-Wightman single-valued continuation for the symmetric
   permuted-tube datum.
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
