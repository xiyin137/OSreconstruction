# Mathlib Gap Analysis For OS Reconstruction

Purpose: this note records the external infrastructure gaps that still matter
for `OSReconstruction`, and separates them from gaps that should simply be
proved locally in this repo.

This note should be read together with:
- `docs/general_k_continuation_blueprint.md`
- `docs/scv_infrastructure_blueprint.md`
- `docs/nuclear_spaces_blueprint.md`
- `docs/gns_pipeline_blueprint.md`
- `docs/unbounded_spectral_project.md`
- `docs/mathlib_issue_draft.md`

It is not a summary of all Mathlib limitations. It is a route-facing guide to
the exact missing infrastructure that still matters for later Lean work here.

## 1. Decision rule

For every missing ingredient, the docs should now decide one of:

1. **prove locally now**: the theorem is specialized to the repo and should not
   wait on upstream,
2. **prove locally but keep upstream-compatible shape**: theorem is general but
   current progress benefits from a local proof first,
3. **prepare an upstream issue / import route**: the best long-term home is
   Mathlib or another Lean library, but work here can still proceed in a local
   staging file,
4. **do not block on upstream**: the user-facing route should continue without
   waiting for ecosystem work.

The default for the OS-route frontiers should be (1) or (2), not (3).

## 2. Confirmed current Mathlib regression

The only concrete current upstream issue already isolated in local docs is the
instance-synthesis regression recorded in:

- `docs/mathlib_issue_draft.md`

The exact issue is:

1. `NormSMulClass ℝ ℂ` does not synthesize automatically in Mathlib `v4.29.0`
   in some downstream contexts,
2. this breaks `fun_prop` chains involving `Continuous.smul`,
3. the local workaround is to install the explicit instances:
   `NormedSpace.toNormSMulClass` and `NormSMulClass.toIsBoundedSMul`.

This is a genuine upstream regression report candidate. It is not a reason to
delay proof work in this repo.

## 3. Functional-analysis gaps

### 3.1. Separate continuity on Frechet/Schwartz products

Current repo surface:

1. `exists_continuousMultilinear_ofSeparatelyContinuous`
   is still an axiom in `Wightman/WightmanAxioms.lean`.

Current local documentation:

1. `docs/nuclear_spaces_blueprint.md`
2. `docs/gns_pipeline_blueprint.md`

Mathlib status:

1. multilinear continuity in Banach settings is well supported,
2. the exact Frechet/Schwartz separate-to-joint theorem is not packaged in the
   form needed here.

Decision:

1. prove locally but keep the theorem statement generic,
2. do not wait for Mathlib,
3. later upstreaming is plausible once the proof is isolated from QFT.

Exact implementation consequence:

1. **Primary route**: import/wrap the theorem from the local
   `gaussian-field` dependency if the exact statement matches;
2. **Fallback route**: prove the Frechet-space Banach-Steinhaus package locally
   under the theorem slots listed in
   [nuclear_spaces_blueprint.md](/Users/xiyin/OSReconstruction/docs/nuclear_spaces_blueprint.md);
3. do not block GNS/kernel-theorem work on opening a Mathlib issue first.

### 3.2. Schwartz nuclear / kernel theorem

Current repo surface:

1. `schwartz_nuclear_extension`
   is still an axiom in `Wightman/WightmanAxioms.lean`.

Mathlib status:

1. no turnkey Schwartz kernel theorem in core Mathlib,
2. local docs note relevant infrastructure in the `gaussian-field` library.

Decision:

1. prove locally with import-compatible interfaces if possible,
2. treat `gaussian-field` as the first place to look for reusable lemmas,
3. do not make GNS cyclicity depend on waiting for a future upstream package.

Exact implementation consequence:

1. **Primary route**: import the local `gaussian-field` nuclear/Schwartz facts
   and derive the repo-facing theorem
   `schwartz_nuclear_extension`;
2. **Fallback route**: prove the tensor-extension package locally via the
   intermediate theorem slots listed in
   [nuclear_spaces_blueprint.md](/Users/xiyin/OSReconstruction/docs/nuclear_spaces_blueprint.md);
3. the consumer-facing GNS/Wightman files should only see the repo theorem
   surface, never the import-path details.

### 3.3. Bochner-Minlos

Current repo surface:

1. `Wightman/NuclearSpaces/BochnerMinlos.lean` still has five direct sorries.

Mathlib status:

1. finite-dimensional measure theory is strong,
2. projective/tightness/Minlos packaging is not available as a ready-made
   theorem family.

Decision:

1. prove locally in repo-specific files,
2. keep statements generic enough for later extraction,
3. do not confuse this with the critical theorem-2/3/4 route.

## 4. Several-complex-variables gaps

### 4.1. Tube boundary values from polynomial growth

Current repo surface:

1. `tube_boundaryValueData_of_polyGrowth` is still axiomatic in
   `SCV/TubeBoundaryValues.lean`.

Mathlib status:

1. SCV holomorphy, connectedness, and identity theorems exist locally here,
2. the exact Vladimirov/Streater-Wightman tube-boundary theorem is not in
   Mathlib.

Decision:

1. prove locally in `OSReconstruction/SCV`,
2. keep it QFT-free,
3. do not wait for upstream.

### 4.2. Malgrange-Zerner gluing

Current repo surface:

1. needed by `docs/general_k_continuation_blueprint.md`,
2. not implemented in current repo or Mathlib.

Mathlib status:

1. the ingredients around open/connected sets and holomorphy exist,
2. the exact MZ theorem is not present.

Decision:

1. implement locally in a dedicated SCV file,
2. document every domain/gluing theorem slot first,
3. consider upstreaming only after the local proof stabilizes.

### 4.3. Envelope-of-holomorphy continuation on the mixed OS II domains

Current repo surface:

1. needed for `(P_N) -> (A_{N+1})` in the general-`k` blueprint,
2. not implemented anywhere current.

Mathlib status:

1. no general envelope-of-holomorphy package.

Decision:

1. treat this as local SCV infrastructure,
2. keep the theorem split into generating-union and envelope-identification
   theorems,
3. do not let later docs write "by envelope" without exact theorem names.

### 4.4. Bochner tube theorem

Current repo surface:

1. `bochner_local_extension`
2. `bochner_tube_extension`

Mathlib status:

1. no ready-made Bochner tube theorem.

Decision:

1. prove locally in `SCV/BochnerTubeTheorem.lean`,
2. do not block theorem-2/3/4 work on it unless a later route truly consumes
   it directly.

## 5. Forward-tube / boundary-value constructor gaps

The theorem-2 blueprint now depends on one important missing constructor:

```lean
flatRegular_of_boundary_distribution_and_polyGrowth
```

This is **not** a Mathlib gap. It is a missing local theorem package in the
repo’s own flattened forward-tube language.

Decision:

1. prove locally in the SCV/forward-tube files,
2. document it as a repo theorem, not as a missing upstream theorem,
3. do not open a Mathlib issue for this until the local formulation has
   stabilized.

Exact implementation consequence:

1. theorem 2 and the GNS matrix-coefficient bridge should both consume the same
   one-point package documented in
   [scv_infrastructure_blueprint.md](/Users/xiyin/OSReconstruction/docs/scv_infrastructure_blueprint.md),
2. the constructor
   `flatRegular_of_boundary_distribution_and_polyGrowth`
   should be treated as a repo-local flattening/adapter theorem above that
   one-point SCV package,
3. neither theorem 2 nor GNS should invent its own custom boundary-value
   constructor route.

## 5b. Theorem-3 raw `BorchersSequence` surface is a repo representation gap, not a Mathlib gap

Current repo surface:

1. [`BorchersSequence`](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/Core.lean)
   is a bounded-record encoding of finitely supported Borchers data;
2. the file provides raw pointwise operations (`Zero`, `Add`, `Neg`, `SMul`, `Sub`);
3. it does **not** currently provide the full `AddCommMonoid` / `Module ℂ` /
   topological structure that a literal
   `Submodule ℂ (BorchersSequence d)` implementation would need.

This is not a missing theorem from Mathlib. It is a local representation issue
in how the repo currently packages Borchers data.

Decision:

1. treat this as a theorem-3 implementation/documentation issue inside the repo,
2. do not open an upstream Mathlib issue for it,
3. prefer the Section 4.3 transport-map / norm-square implementation route
   recorded in
   [theorem3_os_route_blueprint.md](/Users/xiyin/OSReconstruction/docs/theorem3_os_route_blueprint.md)
   before attempting to force a raw `Submodule` / topology layer onto
   `BorchersSequence d`.
4. if a local continuity helper is wanted for legacy consumer theorems, keep it
   explicitly subordinate to those fixed-bound finite-sum consumers, not as a
   new global topological structure on raw `BorchersSequence d`.

Important current-status clarification:

1. this representation issue is **not** the active theorem-3 blocker any more;
2. the active theorem-3 blocker is the repo-local Package-C positive-real
   pairing theorem recorded in
   [theorem3_os_route_blueprint.md](/Users/xiyin/OSReconstruction/docs/theorem3_os_route_blueprint.md);
3. the main missing content there is the OS I Section 4.3 Fourier-Laplace /
   spectral-integral proof strategy for the current `hschw` theorem surface;
4. the later `z -> 0+` transport is already formal once that Package-C theorem
   is available;
5. the old public density layer F/G/H is now withdrawn rather than repaired,
   because ordered-positive-time support is not dense in the full Schwartz
   space;
6. the final public closure route is Package I in its corrected Section 4.3
   form: transformed positive-time Euclidean data -> positive-energy Schwartz
   transformed-image core -> quadratic identity there -> public
   density/continuity closure;
7. so theorem-3 work should not drift back to either
   a raw density theorem or “add a `Submodule`/topology layer first” as if
   either were the main obstruction.

## 6. Operator-theory gaps

### 6.1. Unbounded spectral theorem / Stone package

Current repo surfaces:

1. `vNA/Unbounded/StoneTheorem.lean`
2. `docs/unbounded_spectral_project.md`

Mathlib status:

1. no unbounded spectral theorem / PVM package,
2. bounded functional calculus exists, but not the needed unbounded theorem.

Decision:

1. this is a serious ecosystem gap,
2. but it is not on the current theorem-2/3/4 OS route,
3. so it should remain a dedicated side project rather than absorbing frontier
   proof time now.

### 6.2. Predual / sigma-weak topology / KMS

Current repo surfaces:

1. `vNA/Predual.lean`
2. `vNA/KMS.lean`
3. `vNA/ModularTheory.lean`
4. `vNA/ModularAutomorphism.lean`

Mathlib status:

1. partial operator-topology infrastructure exists,
2. the full Tomita-Takesaki / KMS / predual packages do not.

Decision:

1. prove locally if and when the project prioritizes operator-algebra work,
2. keep them separate from the OS-route documentation and execution order.

## 7. What should definitely be solved locally first

The following are local project gaps, not reasons to wait for Mathlib:

1. theorem-2 regular-input constructor from boundary data and growth,
2. theorem-3 corrected Section 4.3 transformed-image / quadratic-identity /
   density-closure layer,
3. theorem-4 one-factor extraction bookkeeping,
4. SCV tube boundary-value constructor from polynomial growth,
5. general-`k` Malgrange-Zerner / envelope packages,
6. GNS matrix-coefficient holomorphic bridge in the one-variable forward-tube
   language.

## 8. What is plausible to upstream later

The following later packages could plausibly be generalized and upstreamed:

1. separate continuity on Frechet products,
2. Schwartz kernel/nuclear theorem packaging,
3. some SCV gluing lemmas around tube domains,
4. possibly the bounded parts of the spectral/integral story.

But none of those should be prerequisites for current documentation-guided
progress in this repo.

## 9. Route consequences for later Lean work

When Lean proof work resumes, the first question should not be:

> "does Mathlib already have this?"

It should be:

> "is this theorem already explicitly documented as a local package we need?"

If yes, implement it locally first and upstream later only if that becomes the
best cleanup path.

## 10. Quick-reference table

| Gap | Current status | Action |
|---|---|---|
| `NormSMulClass ℝ ℂ` regression | confirmed | upstream issue + local shim |
| Frechet separate-to-joint continuity | missing | local proof |
| Schwartz kernel theorem | missing | local proof/import package |
| tube BV from polynomial growth | axiomatic | local SCV proof |
| Malgrange-Zerner | missing | local SCV proof |
| envelope theorem on mixed domains | missing | local SCV proof |
| theorem-2 regular constructor | missing local theorem | local proof |
| unbounded spectral theorem | ecosystem gap | side project / defer |
| full predual/KMS package | ecosystem gap | side project / defer |

This file should evolve whenever a gap moves from "external blocker" to
"explicit local theorem package."
