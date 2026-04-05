# Theorem 3 OS-Route Blueprint

Purpose: this note is a theorem-specific implementation blueprint for the live
`E -> R` frontier theorem

- `OSToWightmanBoundaryValues.lean`, private theorem `bvt_W_positive`.

It is not a general paper summary. It is a bridge document between:
- the OS I / OS II proofs,
- the current production reduction chain,
- the currently trusted scratch facts,
- and the eventual Lean implementation.

This note assumes familiarity with:
- `docs/os1_detailed_proof_audit.md`
- `docs/os2_detailed_proof_audit.md`
- `docs/os_reconstruction_reading_notes.md`

For the rest of this note, the two domain names that matter are:

- `positiveTimeRegion := {ξ : SpacetimeDim d | 0 < ξ 0}`,
- `fixedStrip s := {ξ : SpacetimeDim d | -(s + s) < ξ 0}`.

The first is the support surface used by the trusted current pairing theorems.
The second is the larger open strip on which the current common-kernel
continuity theorems are naturally stated.

## 1. The live production theorem and its reduction chain

The live frontier statement is:

- `bvt_W_positive` in `OSToWightmanBoundaryValues.lean`.

At the current production state, theorem 3 has already been reduced through the
following chain:

1. `bvt_W_positive`
2. `bvt_wightmanInner_self_nonneg_of_boundary_ray_eq_xiShift_of_hermitian`
3. `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_boundary_ray_eq_xiShift_of_hermitian`
4. `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`
5. `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian`

The important interpretation is:
- all of these are reductions of the same positivity theorem,
- none of them is itself the OS II positivity theorem,
- the real remaining content is the explicit shell comparison sitting behind the
  compact-approximation reduction.

So the implementation task is not "invent another reduction theorem." It is:
- fill the current shell-comparison bridge honestly.

### 1.1. Exact existing theorem hooks by file

To keep later implementation from rediscovering the file graph, the most
relevant currently existing theorem surfaces are listed here explicitly.

In `OSToWightmanBoundaryValueLimits.lean`:
- `schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_boundary_ray_eq_xiShift`
  is the current shell-comparison bridge from a boundary-ray identity to the
  positive-real Schwinger-vs-Wightman equality needed downstream.

In `OSToWightmanBoundaryValuesCompactApprox.lean`:
- `bvt_wightmanInner_compactApprox_timeShift_eq_osInner_of_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`
  converts the shell equality into compact-approximation OS/Wightman isometry;
- `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`
  packages that isometry into the compact-approximation positivity step.

In `K2VI1/InputAStripUniqueness.lean`:
- `continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local`
  is the existing continuity theorem for the common zero-center section;
- `zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local`
  and
  `compactSupport_pairing_eq_comparison_of_fixedCenter_pairing_eq_of_diffBlockDependence_local`
  are the existing uniqueness-upgrade surfaces on a fixed strip;
- `exists_commonZeroCenterShiftSection_bound_of_compactSupport_pairing_eq_comparison_local`
  and related strip-bound theorems package boundedness once compact-support
  pairing equality is known.

In `K2VI1/InputAHeadBlockTransport.lean`:
- `ae_eq_on_positiveStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local`
  is the existing almost-everywhere uniqueness theorem on the positive strip;
- `integral_centerDiffShell_eq_of_compactSupport_schwartz_pairing_eq_continuousOn_positiveStrip_local`
  upgrades compact-support pairing equality to the shell identities used later;
- `integral_centerDiffShell_eq_via_shifted_realDifference_representative_local`
  and
  `integral_reflected_productShell_eq_fixed_center_difference_via_shifted_realDifference_representative_local`
  are the pre-existing transport theorems that make the shifted real-difference
  representative route viable.

In `K2VI1/InputAKernelReduction.lean`:
- `exists_common_difference_kernel_of_common_productShell_pairing_local`
  is the common-kernel existence surface from product-shell pairings;
- `exists_common_difference_kernel_of_common_productShell_pairing_headBlockInvariant_local`
  is the head-block-invariant refinement.

These are the main production hooks the theorem-3 documentation should keep in
view. If a future proof step does not clearly sit on top of one of them, then
either it is inventing a new route or this document is still missing a theorem
slot that must be written down before coding starts.

## 2. What OS I / OS II say the missing theorem should look like

From OS I:
- positivity comes from identifying the reconstructed Wightman pairing with a
  common Hilbert-space / semigroup object.

From OS II:
- one-variable continuation comes first,
- parameters are packaged,
- bounds or boundary values come only after the correct one-variable object is
  in place.

Therefore the missing theorem shape for theorem 3 must be:

1. identify the correct one-variable scalar continuation object;
2. show that the OS-side kernel and the explicit boundary-value-side kernel
   represent the same scalar functional on the correct positive-time domain;
3. only then feed that equality into the existing compact-approximation
   positivity reduction.

What the papers do *not* support:
- direct same-formula equality of Euclidean and Minkowski pairings,
- same-test-function contour shifts,
- operator shortcuts such as pretending `e^{-tH}` and the Wightman boundary
  value are literally the same object before the analytic bridge is proved.

### 2.1. Paper-to-repo symbol dictionary for the theorem-3 lane

To make later implementation more mechanical, the main objects on this route
should be read with the following dictionary in mind.

OS paper side:
- the Euclidean Schwinger function with one distinguished time gap,
- the packaged one-variable continuation object,
- the positive-real fixed-time evaluation,
- the boundary-value / Wightman identification of that same common object.

Current repo side:
- `OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
    (((F.funcs n).osConjTensorProduct
      (timeShiftSchwartzNPoint (d := d) t (F.funcs m)))))`
  is the Schwinger-side scalar pairing on the shifted shell;
- `bvt_W OS lgc (n + m)
    (((F.funcs n).conjTensorProduct
      (timeShiftSchwartzNPoint (d := d) t (F.funcs m))))`
  is the reconstructed Wightman-side pairing on the same split shell;
- `bvt_F OS lgc (n+m)` is the common boundary-value-side holomorphic object
  evaluated at interior or boundary-shifted points;
- `singleSplit_xiShiftHolomorphicValue` and its compact-approximation wrappers
  are the current one-variable positivity packaging on the production side;
- `twoPointFixedTimeCenterDiffKernel_local`, `commonLiftedDifferenceSliceKernel_local`,
  and `commonZeroCenterShiftSection_local` are the current `K2VI1` common-kernel
  incarnations of the one-variable packaged object.

The practical rule is:
- whenever the papers say "same one-variable continuation object viewed in two
  ways", the repo currently expresses that through one of the `common*` kernels
  on the K2 side and one of the descended `bvt_F` / `singleSplit_xiShift*`
  objects on the boundary-value side.

That is the semantic comparison to preserve in Lean. Do not flatten it into a
same-formula equality of Euclidean and Minkowski test shells.

## 3. Current trusted scratch state

At the time of writing, the trusted scratch file is:

- `test/proofideas_bvt_route1_semigroup_strip.lean`.

What is actually proved there:

1. `bvt_descendedAbsoluteInput_twoPoint_eq_semigroupShell_on_positiveStrip`
   identifies the explicit descended `bvt_F` reduced input with the theorem-3
   semigroup shell on the positive strip.

2. `integral_descendedAbsoluteInput_twoPoint_eq_semigroupShell_of_positiveSupport`
   lifts that identification to integral pairings against positive-support
   tests.

3. `commonFixedTimeCenterDiffKernel_eq_descendedAbsoluteInput_pairing_of_positiveSupport`
   aligns the strengthened common fixed-time kernel with the explicit descended
   kernel on positive-support pairings.

4. `commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport`
   descends that alignment to the actual one-variable common zero-center
   section used by the theorem-3 route.

What is *not* currently trusted:
- a pointwise equality theorem on the whole positive-time strip.

That stronger claim appeared briefly in coordination discussion but is not part
of the current trusted scratch file, because the attempted proof overreached the
natural domain of the descended absolute forward-tube input.

So the trusted state is:
- functional-level agreement on positive-support test pairings,
- not yet full pointwise equality.

### 3.1. Exact current K2 theorems already available

The later implementation should not rediscover the following existing K2
surfaces.

From `InputAStripUniqueness.lean`:
- `continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local`
- `zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local`
- `compactSupport_pairing_eq_comparison_of_fixedCenter_pairing_eq_of_diffBlockDependence_local`
- `exists_commonZeroCenterShiftSection_bound_of_compactSupport_pairing_eq_comparison_local`

From `InputAHeadBlockTransport.lean`:
- `ae_eq_on_positiveStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local`
- `integral_centerDiffShell_eq_of_compactSupport_schwartz_pairing_eq_continuousOn_positiveStrip_local`
- `integral_centerDiffShell_eq_via_shifted_realDifference_representative_local`
- `integral_reflected_productShell_eq_fixed_center_difference_via_shifted_realDifference_representative_local`

From `InputAKernelReduction.lean`:
- `exists_common_difference_kernel_of_common_productShell_pairing_local`
- `exists_common_difference_kernel_of_common_productShell_pairing_headBlockInvariant_local`

These should be treated as the default adapter layer before inventing any new
support theorems.

## 4. The exact remaining mathematical gap

The most precise current reading is:

Input A:
- a common one-variable kernel
  `ξ ↦ commonZeroCenterShiftSection_local G s ξ`.

Input B:
- an explicit one-variable boundary-value-side kernel
  `ξ ↦
    (descendAbsoluteForwardTubeInput (d := d)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc 1)).toFun
      (fun _ => wickRotatePoint (ξ + timeShiftVec d (s+s)))`.

Known:
- for every positive-support Schwartz test `h`, their pairings against `h`
  agree.

Still needed:
- either a theorem upgrading this pairing agreement to equality on the exact
  local positive-time domain,
- or an alternative direct route that feeds the pairing equality into the
  production reduction chain without first asserting full pointwise equality.

This is the correct place to work. Anything that avoids confronting this gap is
drifting off the OS route.

### 4.1. The semantic content of the two kernels

To avoid future category confusion, the two kernels should be read as follows.

`commonZeroCenterShiftSection_local G s ξ`
means:
- take the strengthened `InputA` common continuation object `G`,
- collapse to the one-variable zero-center section,
- evaluate it at positive-time parameter `s`,
- then test it at the spacetime difference variable `ξ`.

`(descendAbsoluteForwardTubeInput (d := d)
    (bvt_absoluteForwardTubeInput (d := d) OS lgc 1)).toFun
    (fun _ => wickRotatePoint (ξ + timeShiftVec d (s + s)))`
means:
- start from the explicit boundary-value-side holomorphic object `bvt_F`,
- descend it to the reduced one-gap variable,
- then evaluate it at the Wick-rotated shifted real spacetime point
  `ξ + 2s e_0`.

So the intended equality is not "OS = Wightman" in some raw sense. It is:
- the common one-variable continuation object from the K2/Input-A side
  equals
- the explicit one-variable reduced boundary-value representative from the
  route-1 / `bvt_F` side
on the common positive-time domain.

That is the precise theorem-3 bridge.

### 4.2. Why pairing equality is not yet enough

The currently trusted scratch theorem gives:

`∀ h with positive support, ∫ commonKernel * h = ∫ explicitKernel * h`.

This is already substantial, but it is still weaker than what production needs.

The missing upgrade is not formal for two reasons:

1. One needs both kernels to be defined on the same open set.
2. One needs the uniqueness theorem to apply on exactly that open set with the
   right continuity hypotheses.

The failed earlier scratch step overreached in a more specific way than "the
domain was wrong".

What is genuinely known from the current trusted scratch state:

1. the comparison pairing theorem
   `commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport`
   quantifies over tests `h` with support in `positiveTimeRegion`;
2. the current common-kernel continuity theorem is naturally stated on the
   larger strip `fixedStrip s`;
3. the fixed-strip uniqueness theorem
   `zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local`
   requires pairing equality for *all* compactly supported tests supported in
   `fixedStrip s`, not merely those supported in `positiveTimeRegion`.

So the earlier jump to pointwise equality on the whole strip was unjustified
because a theorem requiring strip-supported test equality was fed only
positive-time-supported test equality. That is a theorem-hypothesis mismatch.

The documentation must therefore distinguish two separate questions:

1. is the explicit descended kernel mathematically defined and continuous on
   `fixedStrip s`?
2. even if yes, do we currently have the stronger strip-wide pairing theorem
   needed to invoke fixed-strip uniqueness?

At present the answer to (2) is "no". The honest current route is therefore to
work first on `positiveTimeRegion`, where the pairing theorem already lives,
and only later widen to `fixedStrip s` if a stronger pairing theorem is
actually proved.

## 5. Preferred proof shapes

There are only three honest proof shapes still on the table.

### 5.1. Positive-time uniqueness on the correct domain

The positive-time uniqueness route has the following exact input shape:

- both kernels are
- honestly defined on `positiveTimeRegion`,
- continuous there,
- and equal on all compactly supported positive-time Schwartz test pairings,

so one may apply the repo's existing distributional uniqueness theorem.

This route is currently the cleanest one because the trusted pairing theorem is
already stated on `positiveTimeRegion`.

Detailed subclaims needed before uniqueness:

1. `explicitKernel` is defined on `fixedStrip s`, hence also on
   `positiveTimeRegion`;
2. `commonKernel` is defined on `fixedStrip s`, hence also on
   `positiveTimeRegion`;
3. both kernels are continuous on `positiveTimeRegion` by restriction from the
   fixed strip;
4. the existing positive-support pairing theorem really quantifies over all
   compactly supported Schwartz tests supported in `positiveTimeRegion`;
5. the theorem
   `eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local`
   can therefore be applied directly.

Only after all five are written down explicitly should a uniqueness theorem be
applied.

Subclaim 4 hides a standard but real separation statement that should also be
spelled out:

1. `positiveTimeRegion = {ξ | 0 < ξ 0}` is an open subset of Euclidean space;
2. compactly supported Schwartz tests with support inside that open set
   separate continuous kernels on the set;
3. the uniqueness theorem is exactly the packaged repo form of that separation
   principle.

So the later Lean proof should not treat "pairings against Schwartz tests are
enough" as a slogan. It should remember that openness plus Schwartz separation
is the mathematical reason the uniqueness step works.

### 5.2. Partial-boundary-value transport through existing `K2VI1` machinery

The more paper-shaped route is to instantiate the existing `InputA*` /
head-block transport infrastructure so that the common kernel and the explicit
descended kernel are seen to arise as two faces of the same one-variable
continuation object.

This route is closest to OS II:
- it treats the common kernel as the packaged one-variable continuation object;
- it treats the explicit descended `bvt_F` side as the corresponding
  boundary-value-side representative.

This route decomposes further into:

1. use `InputAKernelReduction` to locate the common kernel at the fixed-time
   shell level;
2. use `InputAHeadBlockTransport` to move between product-shell and
   difference-shell representations;
3. use the trusted route-1 scratch theorems to identify the explicit
   difference-shell representative with the descended `bvt_F` object;
4. only then compare the one-variable zero-center sections.

So the K2 route is not an alternative to the current scratch mathematics; it is
the production infrastructure through which that mathematics must eventually be
ported.

### 5.3. A direct fixed-time boundary-value theorem

A third route is to prove a dedicated theorem:
- fixed-time interior evaluation of the common/descended kernel equals the
  positive-time boundary-value pairing for the explicit descended `bvt_F`
  object.

This route is admissible only under the following exact constraints:

1. the theorem remains strictly one-variable,
2. all other parameters stay fixed throughout,
3. the domain is the actual theorem-3 positive-time / fixed-strip domain,
4. the conclusion is used only as a local `k = 2` bridge and is not recast as
   a general several-variable continuation theorem.

Such a theorem would have to identify, step by step:

1. the interior fixed-time common kernel,
2. the shifted real-difference representative,
3. the descended `bvt_F` representative,
4. the boundary-value-side shell pairing.

If any one of those identifications is skipped, the theorem is too vague to be
trusted.

## 6. Mathematical decomposition into implementation tasks

The later Lean work should be decomposed into the following explicit tasks.

### 6.0. Full rewrite chain before any proof attempt

Before proving anything new, the later implementation should write down the
following semantic chain explicitly for the fixed-time parameter `s`:

1. `commonZeroCenterShiftSection_local G s`
2. `commonLiftedDifferenceSliceKernel_local G s`
3. `twoPointFixedTimeCenterDiffKernel_local G ((2s : ℂ) * I)`
4. shifted real-difference representative
5. explicit descended absolute forward-tube input
6. semigroup shell built from `bvt_F`
7. positive-real Schwinger shell
8. positive-real Wightman shell

The point of this list is that each arrow should later be implemented by a
named theorem, not by intuition or a long `simpa`.

If any arrow does not already have an obvious existing theorem candidate, that
absence should be recorded in the docs before coding starts.

Important route clarification:

- the intended proof path is the Task 3 uniqueness route on
  `positiveTimeRegion`;
- Section 6.0 is not a competing proof path;
- it is the semantic rewrite inventory needed before and after uniqueness so
  the later production proof can move from kernel equality to the shell
  equality actually consumed by theorem 3.

So Section 6.0 answers "what must eventually be rewritten by named theorems?",
while Task 3 answers "what is the central analytic proof step?".

### Task 1. Nail the domain of the explicit descended kernel

Goal:
- state precisely on which subset of spacetime the explicit descended kernel is
  already known to be defined and continuous.

At the documentation level, this task must distinguish:

1. the larger strip `fixedStrip s = {ξ | -(s+s) < ξ 0}`,
2. the smaller positive-time region `positiveTimeRegion = {ξ | 0 < ξ 0}`.

The honest later implementation will need two theorems:

1. a strip-domain theorem on `fixedStrip s`,
2. a restriction corollary on `positiveTimeRegion`.

Desired theorem shape:

```lean
/-- The fixed strip used by the theorem-3 one-variable comparison. -/
def fixedStrip (s : ℝ) : Set (SpacetimeDim d) := {ξ : SpacetimeDim d | -(s + s) < ξ 0}

/-- Domain statement for the explicit descended theorem-3 kernel. -/
theorem explicit_descended_kernel_continuous_on_fixedStrip
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s) :
    ContinuousOn
      (fun ξ : SpacetimeDim d =>
        (descendAbsoluteForwardTubeInput (d := d)
            (bvt_absoluteForwardTubeInput (d := d) OS lgc 1)).toFun
          (fun _ => wickRotatePoint (ξ + timeShiftVec d (s + s))))
      (fixedStrip s) := by
  -- prove the translated Wick-rotated point lands in the reduced forward-tube
  -- domain for every `ξ` with `-(s+s) < ξ 0`
```

The main thing this theorem must *not* do is silently enlarge the domain beyond
what the reduced forward-tube factorization actually gives.

Micro-lemma checklist:
1. identify the exact reduced forward-tube image of
   `ξ ↦ wickRotatePoint (ξ + timeShiftVec d (s+s))`;
2. prove the image lies in the domain of
   `descendAbsoluteForwardTubeInput`;
3. record the continuity theorem available on that domain;
4. prove `positiveTimeRegion ⊆ fixedStrip s` when `0 < s`;
5. obtain the restriction corollary on `positiveTimeRegion`.

Lean pseudocode with the expected shape:

```lean
lemma explicit_descended_kernel_mem_reduced_forward_tube
    (hs : 0 < s) (hξ : ξ ∈ fixedStrip s) :
    (fun _ => wickRotatePoint (ξ + timeShiftVec d (s + s)))
      ∈ reducedForwardTubeDomain := by
  -- this is the theorem-specific content behind the route-1 safe-basepoint
  -- factorization argument

lemma explicit_descended_kernel_continuousOn_reduced_domain
    :
    ContinuousOn explicitKernel reducedForwardTubeDomain := by
  -- use the continuity packaged with `descendAbsoluteForwardTubeInput`

lemma positiveTimeRegion_subset_fixedStrip
    (hs : 0 < s) :
    positiveTimeRegion ⊆ fixedStrip s := by
  intro ξ hξ
  linarith

theorem explicit_descended_kernel_continuous_on_positiveTime
    (hs : 0 < s) :
    ContinuousOn explicitKernel positiveTimeRegion := by
  intro ξ hξ
  exact explicit_descended_kernel_continuous_on_fixedStrip (OS := OS) (lgc := lgc) s hs
    (positiveTimeRegion_subset_fixedStrip (d := d) hs hξ)
```

The later implementation should not leave those as generic placeholders. The
natural theorem-slot inventory is:

```lean
lemma continuous_eta_s
    (s : ℝ) :
    Continuous (fun ξ : SpacetimeDim d =>
      (fun _ : Fin 1 => wickRotatePoint (ξ + timeShiftVec d (s + s)))) := by
  -- `continuous_const.add continuous_id`,
  -- then the existing `wickRotatePoint` continuity proof pattern,
  -- then `continuous_pi`

lemma eta_s_mem_reducedForwardTubeN_of_mem_fixedStrip
    (hs : 0 < s) {ξ : SpacetimeDim d}
    (hξ : ξ ∈ fixedStrip s) :
    (fun _ : Fin 1 => wickRotatePoint (ξ + timeShiftVec d (s + s)))
      ∈ ReducedForwardTubeN d 1 := by
  -- unfold `ReducedForwardTubeN d 1`,
  -- reduce to the single forward-cone condition on the imaginary part,
  -- compute that imaginary part explicitly,
  -- use `inOpenForwardCone_add_time`

lemma explicit_descended_kernel_continuous_on_fixedStrip
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s) :
    ContinuousOn explicitKernel (fixedStrip s) := by
  let hdesc :=
    (descendAbsoluteForwardTubeInput (d := d)
      (bvt_absoluteForwardTubeInput (d := d) OS lgc 1)).holomorphic
  have houter : ContinuousOn
      (descendAbsoluteForwardTubeInput (d := d)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc 1)).toFun
      (ReducedForwardTubeN d 1) :=
    hdesc.continuousOn
  exact houter.comp (continuous_eta_s (d := d) s).continuousOn
    (eta_s_mem_reducedForwardTubeN_of_mem_fixedStrip (d := d) hs)
```

Those three theorem slots are the exact local implementation targets for Task 1.

### Task 1a. Exact proof transcript for the fixed-strip continuity theorem

The fixed-strip continuity theorem is now specific enough to be written as a
line-by-line proof plan.

Let

`explicitKernel_s ξ :=
  (descendAbsoluteForwardTubeInput (d := d)
    (bvt_absoluteForwardTubeInput (d := d) OS lgc 1)).toFun
    (fun _ => wickRotatePoint (ξ + timeShiftVec d (s + s)))`.

The proof of

`ContinuousOn explicitKernel_s (fixedStrip s)`

should proceed exactly as follows.

1. The object
   `descendAbsoluteForwardTubeInput (bvt_absoluteForwardTubeInput ...)`
   is a `ReducedForwardTubePreInput d 1`.
2. By the structure field `holomorphic`, its `.toFun` is
   `DifferentiableOn ℂ` on `ReducedForwardTubeN d 1`.
3. Therefore its `.toFun` is `ContinuousOn` on `ReducedForwardTubeN d 1`.
4. Define the one-variable map
   `η_s : SpacetimeDim d -> ReducedNPointConfig d 1` by
   `η_s ξ := fun _ => wickRotatePoint (ξ + timeShiftVec d (s + s))`.
5. Prove `Continuous η_s` by continuity of `ξ ↦ ξ + timeShiftVec d (s+s)` and
   of `wickRotatePoint`.
6. Prove `MapsTo η_s (fixedStrip s) (ReducedForwardTubeN d 1)`.
7. The only nontrivial part of step 6 is the forward-cone condition:
   for `ξ ∈ fixedStrip s`, the imaginary part of
   `wickRotatePoint (ξ + timeShiftVec d (s+s))` is the vector
   `(ξ 0 + (s+s), 0, ..., 0)`,
   which lies in the open forward cone because `-(s+s) < ξ 0`.
8. Apply `ContinuousOn.comp` to the continuous-on-reduced-forward-tube outer
   map and the continuous inner map `η_s`.

Exact local theorem hooks already present in the repo:

1. outer differentiability:
   the field
   `ReducedForwardTubePreInput.holomorphic` in
   `BHWReducedExtension.lean`;
2. `wickRotatePoint` continuity pattern:
   the local proof
   `continuous_wickRotatePoint_local` in
   `K2VI1/InputCSwapSymmetry.lean`
   and the identical proof pattern `hwickpt_cont` in
   `SchwingerTemperedness.lean`;
3. forward-cone inflation:
   `inOpenForwardCone_add_time` in
   `BaseFiberInflation.lean`.

So Task 1 is not blocked by an unknown analytic theorem. It is a concrete
composition proof whose remaining work is:

1. write the `MapsTo` lemma into the exact reduced-forward-tube coordinates
   used by `ReducedForwardTubeN d 1`,
2. package the `η_s` continuity proof as a local theorem instead of repeating
   the `continuous_pi` proof pattern inline,
3. invoke the already existing `holomorphic` field of the reduced preinput.

### Task 1b. Exact reduced-forward-tube membership computation

The `MapsTo` lemma in Task 1 is simple enough that its proof should already be
written in mathematical detail here.

Take `ξ ∈ fixedStrip s`, so `-(s+s) < ξ 0`. Define

`η_s ξ : ReducedNPointConfig d 1 := fun _ => wickRotatePoint (ξ + timeShiftVec d (s+s))`.

To show `η_s ξ ∈ ReducedForwardTubeN d 1`, unfold:

1. `ReducedForwardTubeN d 1 = ReducedForwardTube d 2`;
2. a point of `ReducedForwardTube d 2` is exactly one reduced difference whose
   imaginary part lies in `V_+`;
3. `timeShiftVec d (s+s)` is the real vector `(2s, 0, ..., 0)`;
4. `wickRotatePoint` turns a real spacetime point `x` into the complex point
   whose imaginary part is `(x 0, 0, ..., 0)`.

So

`Im (η_s ξ 0) = (ξ 0 + (s+s), 0, ..., 0)`.

Now:

1. the base vector `(0, ..., 0)` is the zero vector in `R^(d+1)`;
2. `safeBasepointVec d = (1, 0, ..., 0)` lies in `V_+`;
3. scaling by the positive number `ξ 0 + (s+s)` gives the vector above;
4. equivalently, one may start from `safeBasepointVec d` and use
   `inOpenForwardCone_add_time` to add the extra positive amount.

Thus the forward-cone condition reduces to the single scalar inequality

`0 < ξ 0 + (s+s)`,

which is exactly `hξ`.

This is the full mathematical content of the domain proof. There is no contour
argument or hidden SCV lemma here.

### Task 1c. Exact `Fin 1` / reduced-domain unfolding chain

Because the theorem-3 route specializes to a single reduced variable, the
domain proof should record the exact type-unfolding chain rather than relying
on informal "there is only one point" language.

Start from the target statement

`η_s ξ ∈ ReducedForwardTubeN d 1`.

Unfolding proceeds as follows.

1. `ReducedForwardTubeN d 1 = ReducedForwardTube d (1 + 1)`, by definition of
   `ReducedForwardTubeN`.
2. `ReducedForwardTube d 2` is the reduced one-difference tube for two points.
3. A point of `ReducedForwardTube d 2` is equivalently a function
   `η : Fin 1 → Fin (d + 1) → ℂ` satisfying the reduced forward-cone condition
   on its unique reduced coordinate.
4. Since `Fin 1` has only the index `0`, the universal reduced-cone condition
   collapses to the single statement that the imaginary part of `η 0` lies in
   the open forward cone.

So the later Lean proof should not expect a nontrivial block-difference
recurrence here. After unfolding all abbreviations, the proof target is simply

`InOpenForwardCone (fun μ => Complex.im ((η_s ξ) 0 μ))`.

The exact proof transcript is then:

1. extensionality in the unique `Fin 1` coordinate reduces the membership check
   to `0`;
2. compute the imaginary part coordinatewise using the definition of
   `wickRotatePoint`;
3. identify that imaginary part with the positive time vector
   `(ξ 0 + (s+s), 0, ..., 0)`;
4. conclude by the scalar inequality `0 < ξ 0 + (s+s)`.

This is intentionally over-explicit because otherwise the eventual Lean port is
likely to waste time fighting `Fin 1` definitional equalities that are already
mathematically trivial.

### Task 2. Nail the domain and continuity of the common kernel

Goal:
- show the common zero-center section is continuous on the same domain.

Unlike Task 1, most of this is already present in the repo: the strip
continuity theorem exists, so the main later implementation step is a careful
restriction to `positiveTimeRegion`.

Desired theorem shape:

```lean
theorem common_zero_center_section_continuous_on_fixedStrip
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s) :
    let G :=
      Classical.choose
        (schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
          (d := d) OS lgc)
    ContinuousOn
      (commonZeroCenterShiftSection_local G s)
      (fixedStrip s) := by
  -- this is exactly
  -- `continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local`
  -- instantiated with the holomorphicity and diff-block-dependence data coming
  -- from the chosen Input-A witness
```

This is where the `InputA*` / fixed-time extension machinery enters. The proof
plan is:

1. instantiate the existing fixed-strip continuity theorem on the chosen
   `InputA` witness `G`;
2. restrict from `fixedStrip s` to `positiveTimeRegion`;
3. record the restricted theorem under the local name that Task 3 will call.

Existing hooks to inspect first:
- `continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local`
- `continuousOn_translatedProbeSection_on_fixedStrip_local`
- the boundedness package in `InputAStripUniqueness.lean`

So the first documentation question is not "can we prove continuity somehow?"
It is "which existing fixed-strip continuity theorem already matches the exact
common-kernel surface we need?"

Lean pseudocode with the expected shape:

```lean
theorem common_zero_center_section_continuous_on_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
          v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v) :
    ContinuousOn (commonZeroCenterShiftSection_local G s) positiveTimeRegion := by
  intro ξ hξ
  exact
    (continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local
      (d := d) G hG_holo hG_diff s)
      (positiveTimeRegion_subset_fixedStrip (d := d) hs hξ)
```

Detailed implementation checklist:

1. identify the exact strip domain used by
   `continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local`;
2. prove `positiveTimeRegion ⊆ fixedStrip s`;
3. use the existing `ContinuousOn` theorem on the strip;
4. transport it by restriction to `positiveTimeRegion`;
5. record the resulting theorem name that the later uniqueness proof will use.

### Task 3. Upgrade pairing equality to equality on the common domain

Once Tasks 1 and 2 are done, the mathematically clean route is:

```lean
theorem common_eq_explicit_descended_on_positive_domain
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s) :
    let G :=
      Classical.choose
        (schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
          (d := d) OS lgc)
    EqOn
      (commonZeroCenterShiftSection_local G s)
      (fun ξ =>
        (descendAbsoluteForwardTubeInput (d := d)
            (bvt_absoluteForwardTubeInput (d := d) OS lgc 1)).toFun
          (fun _ => wickRotatePoint (ξ + timeShiftVec d (s + s))))
      positiveTimeRegion := by
  -- 1. continuity of both sides on the common domain
  -- 2. pairing equality on compactly supported positive-support tests
  -- 3. invoke the repo's uniqueness theorem
```

This theorem is exactly where a later port should either succeed honestly or
fail honestly. It is the natural pressure test for the current theorem-3 route.

Existing hooks to inspect first:
- `zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local`
- `eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local`
- `ae_eq_on_positiveStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local`
- `integral_centerDiffShell_eq_of_compactSupport_schwartz_pairing_eq_continuousOn_positiveStrip_local`

There are two admissible implementation branches:

1. the positive-time uniqueness theorem
   `eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local`
   applies directly after the domain/continuity audit, in which case no new
   theorem is needed at this stage;
2. one hypothesis still mismatches, in which case the only allowed new theorem
   is a local adapter whose statement consists solely of translating that
   mismatched hypothesis into the exact input format of the existing uniqueness
   theorem.

Any theorem stronger than that local adapter would be route drift.

Lean pseudocode with exact current theorem names:

```lean
theorem common_eq_explicit_descended_on_positive_domain
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    : EqOn commonKernel explicitKernel positiveTimeRegion := by
  apply eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local
  · exact common_zero_center_section_continuous_on_positiveTime
      (d := d) (OS := OS) (lgc := lgc) s hs G hG_holo hG_diff
  · exact explicit_descended_kernel_continuous_on_positiveTime
      (d := d) (OS := OS) (lgc := lgc) s hs
  · intro h hh_compact hh_support
    -- reduce to the already proved positive-support pairing theorem
    simpa [commonKernel, explicitKernel] using
      commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport
        (d := d) OS lgc χc h hχc hh_support s hs
```

The extra cutoff parameter `χc` should not be treated as an afterthought. The
current pairing theorem is not literally quantified over arbitrary auxiliary
cutoffs. It is proved for a chosen normalized center cutoff satisfying

`∫ u, χc u = 1`.

So Task 3 must keep the following bookkeeping explicit:

1. fix one canonical normalized cutoff `χc` once and for all,
   for example the repo's standard normalized bump/cutoff object;
2. prove the pairing theorem with that fixed `χc`;
3. feed that theorem into uniqueness;
4. only if later proof work needs a cutoff-independent theorem should a new
   lemma be stated and proved.

At the current theorem-3 stage, cutoff-independence is not required. A fixed
choice of `χc` is enough because the uniqueness theorem quantifies over the test
function `h`, not over the center cutoff. So the later Lean proof should bind
`χc` near the top of the argument and never silently drop it.

Only after a stronger strip-wide pairing theorem has been proved should the
fixed-strip uniqueness theorem
`zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local`
be brought back into the route. Using it earlier would repeat the same
overreach that already failed once.

If the positive-time route first produces only
`ae_eq_on_positiveStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local`,
that is still acceptable provided the documentation records the final upgrade:

1. both kernels are continuous on the open set `positiveTimeRegion`,
2. they agree almost everywhere there,
3. the set where two continuous functions differ is open,
4. an open set of measure zero must be empty,
5. therefore the equality is pointwise on `positiveTimeRegion`.

So "a.e. versus pointwise" is not a mystery once continuity has been proved; it
is a short explicit topological lemma that must simply be named in the final
implementation notes.

The theorem-slot form of that upgrade should be:

```lean
lemma eqOn_of_aeEq_of_continuousOn_open
    {U : Set (SpacetimeDim d)} (hU : IsOpen U)
    {K K' : SpacetimeDim d → ℂ}
    (hK : ContinuousOn K U)
    (hK' : ContinuousOn K' U)
    (hae : ∀ᵐ x ∂volume, x ∈ U → K x = K' x) :
    Set.EqOn K K' U := by
  intro x hx
  by_contra hneq
  have hopen_diff :
      IsOpen {y : SpacetimeDim d | y ∈ U ∧ K y ≠ K' y} := by
    -- continuity of `K - K'` and openness of `{z : ℂ | z ≠ 0}`
  have hx_diff : x ∈ {y : SpacetimeDim d | y ∈ U ∧ K y ≠ K' y} := by
    exact ⟨hx, hneq⟩
  have hpos_meas :
      0 < volume {y : SpacetimeDim d | y ∈ U ∧ K y ≠ K' y} := by
    -- nonempty open subset of Euclidean space has positive Lebesgue measure
  have hzero_meas :
      volume {y : SpacetimeDim d | y ∈ U ∧ K y ≠ K' y} = 0 := by
    -- from `hae`
  exact (lt_irrefl (0 : ℝ)) (hzero_meas ▸ hpos_meas)
```

If later implementation uses the a.e. uniqueness theorem first, this lemma is
the exact missing bridge from a.e. equality to pointwise equality.

### Task 3a. Minimal proof transcript for the uniqueness route

If the uniqueness route succeeds, the proof should look like this and not be
left implicit:

1. define `K_cmp` to be the explicit descended kernel on the target domain;
2. set `U := positiveTimeRegion`;
3. prove `ContinuousOn K_cmp U`;
4. prove `ContinuousOn (commonZeroCenterShiftSection_local G s) U`;
5. let `h` be a compactly supported Schwartz test supported in `U`;
6. note that this support condition is *exactly* the hypothesis required by
   `commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport`;
7. rewrite the pairing equality using that theorem;
8. invoke
   `eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local`;
9. only then rewrite the conclusion into the shell form needed downstream.

If a later production proof instead tries to use the fixed-strip theorem at
this stage, it must first add a new documented theorem upgrading the pairing
equality from `positiveTimeRegion` to `fixedStrip s`.

### Task 3c. Exact support logic in the uniqueness step

The support bookkeeping in Task 3 is simple but should be explicit:

1. the uniqueness theorem on `positiveTimeRegion` asks for
   `HasCompactSupport h` and
   `tsupport h ⊆ positiveTimeRegion`;
2. the trusted pairing theorem
   `commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport`
   asks only for the positive-support hypothesis
   `tsupport h ⊆ positiveTimeRegion`;
3. therefore no extra support-reduction lemma is needed at this stage;
4. the compact-support hypothesis is consumed only by the uniqueness theorem,
   not by the pairing theorem.

So the later Lean proof should not waste effort proving a support-conversion
lemma here. The two theorems already line up exactly on the support side.

The only additional bookkeeping item is the fixed normalized cutoff `χc`
mentioned above:

1. `χc` is a global auxiliary parameter chosen once for the pairing theorem;
2. the uniqueness theorem itself does not mention `χc`;
3. therefore the later port should first instantiate the pairing theorem with
   the chosen `χc`, then pass the resulting equality of pairings to uniqueness.

### Task 3b. Why the fixed-strip theorem is not yet available

The theorem
`zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local`
would give a stronger conclusion on `fixedStrip s`, but it expects:

```lean
∀ h,
  HasCompactSupport h ->
  tsupport h ⊆ fixedStrip s ->
  ∫ commonKernel * h = ∫ explicitKernel * h
```

The trusted current scratch theorem gives only:

```lean
∀ h,
  tsupport h ⊆ positiveTimeRegion ->
  ∫ commonKernel * h = ∫ explicitKernel * h
```

Since `positiveTimeRegion ⊊ fixedStrip s` for `s > 0`, the second theorem does
not imply the first. This is the exact logical reason the earlier strip-wide
pointwise equality claim was not yet justified.

### Task 4. Convert the common/exact equality into the `hschw` hypothesis

After Task 3, production wiring should become straightforward:

```lean
theorem compact_approx_componentwise_schwinger_eq_bvtW_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) :
    ∀ N n m (hm : 0 < m) (t : ℝ), 0 < t →
      let F_N := compactApproxPositiveTimeBorchers F N
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((((F_N : BorchersSequence d).funcs n).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t
            ((F_N : BorchersSequence d).funcs m))))) =
        bvt_W OS lgc (n + m)
          ((((F_N : BorchersSequence d).funcs n).conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t
              ((F_N : BorchersSequence d).funcs m)))) := by
  -- instantiate `common_eq_explicit_descended_on_positive_domain` at the
  -- one-variable time-shift parameter,
  -- rewrite the common-kernel side back to the K2 fixed-time shell,
  -- rewrite the explicit side to the `bvt_F` semigroup shell,
  -- then apply the existing production theorem
  -- `schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_boundary_ray_eq_xiShift`
```

This is the first place where production reduction theorems should be revisited.
Before this point, the work should remain theorem-specific and domain-specific.

Micro-lemma checklist:
1. instantiate the common-kernel equality on the fixed shell parameter;
2. rewrite the common-kernel side to the Schwinger-side shell using the current
   `InputA*` witness package;
3. rewrite the explicit descended side to the `bvt_F` / `bvt_W` shell using the
   proven route-1 scratch identifications;
4. only then package the exact `hschw` hypothesis expected by
   `OSToWightmanBoundaryValuesCompactApprox.lean`.

Concrete rewrite inventory:

- common-kernel side:
  - `twoPointFixedTimeCenterDiffKernel_local`
  - `commonLiftedDifferenceSliceKernel_local`
  - `commonZeroCenterShiftSection_local`
- explicit side:
  - `integral_centerDiffShell_eq_via_shifted_realDifference_representative_local`
  - `integral_reflected_productShell_eq_fixed_center_difference_via_shifted_realDifference_representative_local`
  - `bvt_descendedAbsoluteInput_twoPoint_eq_semigroupShell_on_positiveStrip`
  - `integral_descendedAbsoluteInput_twoPoint_eq_semigroupShell_of_positiveSupport`
  - `commonFixedTimeCenterDiffKernel_eq_descendedAbsoluteInput_pairing_of_positiveSupport`
  - `commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport`
- production packaging target:
  - `schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_boundary_ray_eq_xiShift`
  - `bvt_wightmanInner_compactApprox_timeShift_eq_osInner_of_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`

The documentation-level test for this task is:
- after all rewrites, no unnamed semantic jump should remain between the
  common-kernel side and the production `hschw` hypothesis.

Clarification on the previously unnamed step
"shifted real-difference representative -> explicit descended absolute
forward-tube input":

- this is not expected to be a pointwise theorem at the one-variable kernel
  level;
- the natural theorem candidates already in the repo are the shell-level
  transport theorems
  `integral_centerDiffShell_eq_via_shifted_realDifference_representative_local`
  and
  `integral_reflected_productShell_eq_fixed_center_difference_via_shifted_realDifference_representative_local`;
- if those two shell-level transport theorems already match the descended-input
  shell expression exactly, use them directly;
- if one hypothesis or shell normal form still mismatches, the only admissible
  extra theorem is a local shell-normalization adapter whose conclusion is
  literally the input form of
  `bvt_descendedAbsoluteInput_twoPoint_eq_semigroupShell_on_positiveStrip`;
- no stronger comparison theorem belongs here.

### Task 4b. Explicit theorem-by-theorem rewrite candidates

The current best candidate rewrite path is:

1. `commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport`
   gives equality at the one-variable pairing level.
2. use
   `eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local`
   as the default uniqueness theorem on the common positive-time domain;
   only if the implementation first obtains almost-everywhere equality should
   `ae_eq_on_positiveStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local`
   plus `eqOn_of_aeEq_of_continuousOn_open` replace this step.
3. `commonLiftedDifferenceSliceKernel_eq_k2TimeParametricKernel_on_zeroCenterShift_of_diffBlockDependence_local`
   and
   `twoPointFixedTimeCenterDiffKernel_eq_commonLiftedDifferenceSlice_of_diffBlockDependence_local`
   should move from the zero-center section back to the fixed-time center/diff
   kernel.
4. `commonFixedTimeCenterDiffKernel_eq_descendedAbsoluteInput_pairing_of_positiveSupport`
   identifies the fixed-time common kernel with the explicit descended one at
   the shell-pairing level.
5. `bvt_descendedAbsoluteInput_twoPoint_eq_semigroupShell_on_positiveStrip`
   and
   `integral_descendedAbsoluteInput_twoPoint_eq_semigroupShell_of_positiveSupport`
   rewrite the explicit descended side to the semigroup shell.
6. The production theorem
   `schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_boundary_ray_eq_xiShift`
   is the final bridge from shell identity to `hschw`.

This list is intentionally redundant. Later implementation should collapse it
only after every semantic step has been checked.

The rewrite directions should also be fixed in advance. The intended default
orientation is:

1. `commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport`
   :
   `commonZeroCenterShiftSection_local ...` `→`
   descended-absolute-input pairing.
2. `commonFixedTimeCenterDiffKernel_eq_descendedAbsoluteInput_pairing_of_positiveSupport`
   :
   common fixed-time kernel pairing `→`
   descended-absolute-input pairing.
3. `commonLiftedDifferenceSliceKernel_eq_k2TimeParametricKernel_on_zeroCenterShift_of_diffBlockDependence_local`
   and
   `twoPointFixedTimeCenterDiffKernel_eq_commonLiftedDifferenceSlice_of_diffBlockDependence_local`
   :
   outer common-kernel incarnations `→`
   the simpler zero-center / lifted-slice incarnations.
4. `integral_centerDiffShell_eq_via_shifted_realDifference_representative_local`
   :
   center-difference shell integral `→`
   shifted-real-difference representative.
5. `integral_reflected_productShell_eq_fixed_center_difference_via_shifted_realDifference_representative_local`
   :
   reflected product shell `→`
   fixed-center-difference shell.
6. `bvt_descendedAbsoluteInput_twoPoint_eq_semigroupShell_on_positiveStrip`
   :
   descended absolute input `→`
   the explicit semigroup shell.
7. `integral_descendedAbsoluteInput_twoPoint_eq_semigroupShell_of_positiveSupport`
   :
   descended-absolute-input pairing `→`
   semigroup-shell pairing.
8. `schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_boundary_ray_eq_xiShift`
   :
   boundary-ray equality `→`
   the positive-real Schwinger/Wightman shell equality expected by production.

If one of those theorem statements in the actual Lean files is oriented the
opposite way, the implementation script should record that immediately using
`rw [← theoremName]` rather than silently relying on trial and error.

### Task 4c. Where the boundary-value limit is handled

The theorem-3 blueprint should say explicitly that the `ε -> 0` boundary-value
limit is *not* a new theorem to be proved after Task 4. It is already consumed
by the existing production reduction chain in
`OSToWightmanBoundaryValueLimits.lean`.

The intended order is:

1. Task 4 proves the positive-real shell equality
   `OS.S(...) = bvt_W(... timeShift ...)`;
2. the existing theorem
   `schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_boundary_ray_eq_xiShift`
   turns the shell equality into the boundary-ray identification expected by
   the limit package;
3. the existing theorem
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
   discharges the `nhdsWithin 0` limit obligation;
4. the compact-approximation positivity theorems in
   `OSToWightmanBoundaryValuesCompactApprox.lean` and
   `OSToWightmanBoundaryValues.lean` consume that limit theorem and close
   theorem 3.

So no extra "take ε -> 0" step should be inserted after Task 4. The only new
mathematical work before the limit package is the shell equality itself.

### Task 4a. Exact production target after rewriting

The final output of Task 4 should be a theorem with the following semantic
content:

- for each compact approximant `F_N`,
- for each split `n + m` with `m > 0`,
- for each positive time `t`,
- the Schwinger pairing on the OS side of the shifted shell equals the
  reconstructed Wightman pairing on the Lorentzian side of the shifted shell.

In other words, by the time Task 4 is finished, no mention of the common
kernel, descended kernel, or K2 transport machinery should remain in the final
statement. All of that should already have been discharged as internal bridge
work.

### Task 5. Close theorem 3 with no new reductions

Once Task 4 is in place:

```lean
private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  intro F
  -- use the existing compact approximation + hermitian reduction chain
  -- feed in Task 4
```

At this stage, any temptation to add a new `h*` reduction theorem should be
treated as a route error unless it closes something immediately.

There is, however, one remaining theorem-shape issue that should now be stated
explicitly: the live frontier `bvt_W_positive` quantifies over
`F : BorchersSequence d`, whereas the whole compact-approximation route in
Tasks 1-4 works with `PositiveTimeBorchersSequence d`.

So Task 5 actually splits into two closure obligations:

1. close the positive-time positivity theorem using Tasks 1-4;
2. identify the precise production bridge from a general Borchers sequence to
   the positive-time class, or document that this bridge is still part of the
   frontier if no such theorem already exists.

At the current repo state, the positive-time compact-approximation theorems are
already present and proved, but the final general-to-positive-time reduction is
still hidden inside the frontier theorem itself. Therefore the documentation
must *not* pretend that Tasks 1-4 alone mechanically finish `bvt_W_positive`.
They finish only the positive-time analytic core.

The nearest already-existing positive-time closure hooks are:

1. in `OSToWightmanBoundaryValuesBase.lean`,
   `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`,
   which upgrades componentwise shell comparison to full OS/Wightman equality
   for positive-time sequences once the degree-zero bookkeeping is handled;
2. in the same file,
   `bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero`,
   which already closes the self-pair positivity theorem for positive-time
   sequences whose degree-zero component vanishes;
3. in `OSToWightmanBoundaryValues.lean`,
   the public wrappers
   `bvt_positiveTime_self_nonneg_of_componentwise_*`
   and
   `bvt_positiveTime_self_nonneg_of_compactApprox_*`,
   which are the exact positive-time consumers of the theorem-3 analytic work.

More explicitly, the positive-time closure chain already present in
`OSToWightmanBoundaryValuesBase.lean` is:

1. `bvt_wightmanInner_right_single_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   :
   componentwise shell comparison against one positive-degree right singleton
   implies equality of the full right-single pairing.
2. `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   :
   summing the right-single theorem over all right degrees reduces the full
   positive-time comparison to the single remaining `m = 0` term.
3. `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero_right`
   :
   if the right degree-zero component vanishes, that remaining `m = 0` term is
   discharged automatically.
4. `bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero`
   :
   in the self-pair case, the previous equality theorem immediately yields
   positivity.

So the production theorem-3 route should be read as:

1. prove the shell comparison at the component level;
2. feed it into the right-single theorem;
3. sum over right degrees;
4. discharge or package the degree-zero term;
5. only then invoke the compact-approximation wrappers in
   `OSToWightmanBoundaryValuesCompactApprox.lean` /
   `OSToWightmanBoundaryValues.lean`.

The exact compact-approximation closure package already present in
`OSToWightmanBoundaryValuesCompactApprox.lean` is:

1. `tendsto_wightmanInner_right_timeShift_nhdsWithin_zero_of_isCompactSupport`
   :
   for compactly supported right data, the reconstructed Wightman inner product
   against `timeShiftBorchers t` tends to the unshifted Wightman inner product
   as `t → 0+`.
2. `tendsto_osInner_right_timeShift_nhdsWithin_zero_of_isCompactSupport`
   :
   the honest OS Hilbert-space inner product satisfies the same `t → 0+`
   continuity for compactly supported positive-time data.
3. `bvt_wightmanInner_self_nonneg_of_compactApprox_timeShift_eq_osInner`
   :
   if the time-shifted Wightman and OS matrix elements agree for every compact
   approximant `F_N` and every positive real `t`, positivity follows after
   taking `t → 0+` and then `N → ∞`.
4. `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_ofReal_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`
   :
   replaces the abstract matrix-element equality by the scalar holomorphic
   boundary-value equality on each component.
5. `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`
   :
   replaces that scalar equality by the positive-real Schwinger-vs-Wightman
   shell equality.
6. `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_boundary_ray_eq_xiShift_of_hermitian`
   :
   replaces the positive-real shell equality by the current live `hpath`
   boundary-ray equality.

So once the direct `hpath` theorem is proved for a positive-time sequence,
positivity is already formal inside the compact-approximation package. The
remaining work is not "find yet another reduction theorem," but:

1. prove the direct `hpath` componentwise shell equality,
2. instantiate the already existing compact-approximation closure theorem,
3. then deal honestly with the final general-sequence reduction if the public
   frontier still quantifies over arbitrary `BorchersSequence d`.

So the documentation should treat the final theorem-3 closure as:

1. finish the positive-time analytic core,
2. land it in the existing positive-time closure theorems,
3. only then address the remaining general Borchers-sequence reduction.

The later Lean port should therefore begin Task 5 by checking which of the
following is actually available in production:

1. a reduction theorem from arbitrary `BorchersSequence d` to
   `PositiveTimeBorchersSequence d`,
2. a density/approximation theorem that reduces positivity to positive-time
   test sequences,
3. or no such theorem yet, in which case this reduction must be written as an
   explicit final subtask rather than buried inside the closing proof.

In other words, the docs now distinguish three separate closure layers:

1. analytic shell comparison,
2. positive-time algebraic/Borchers summation closure,
3. general-sequence reduction.

The third layer is now documented at theorem-slot granularity below, but it is
still not tied to concrete production theorem names or implementations.

### Task 5a. Exact theorem-slot inventory for the final general-sequence layer

The paper-faithful final layer should **not** be described as "approximate an
arbitrary Minkowski Borchers sequence by positive-time-supported Minkowski
cutoffs" unless that approximation theorem is itself proved and identified with
OS I Section 4.3. The paper route is more specific:

1. construct the OS/Hilbert vector attached to a general Minkowski test
   sequence;
2. prove the Wightman quadratic form equals the Hilbert norm square on the
   initial core where the boundary-value/continuation theorem is available;
3. extend that identity by continuity and density;
4. conclude positivity from Hilbert-space positivity.

So if the public frontier remains

`∀ F : BorchersSequence d, 0 ≤ Re WightmanInnerProduct(F,F)`,

then the final theorem-slot inventory should be recorded as:

```lean
lemma bvt_minkowski_to_os_vector
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    BorchersSequence d → OSHilbertSpace OS := by
  -- the Section 4.3 transport map `u`, specialized to the reconstructed BV data

lemma bvt_minkowski_to_os_vector_continuous
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    Continuous (bvt_minkowski_to_os_vector (d := d) OS lgc) := by
  -- OS I Lemma 4.2 type continuity package

lemma bvt_minkowski_to_os_vector_dense
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    DenseRange (bvt_minkowski_to_os_vector (d := d) OS lgc) := by
  -- OS I Lemma 4.1 / Section 4.3 density package

lemma bvt_wightman_quadratic_form_eq_vector_norm_sq_on_core
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F ∈ bvtInitialCore,
      WightmanInnerProduct d (bvt_W OS lgc) F F =
        inner
          (bvt_minkowski_to_os_vector (d := d) OS lgc F)
          (bvt_minkowski_to_os_vector (d := d) OS lgc F) := by
  -- this is where the already-proved positive-time theorem is consumed

lemma bvt_wightman_quadratic_form_eq_vector_norm_sq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      WightmanInnerProduct d (bvt_W OS lgc) F F =
        inner
          (bvt_minkowski_to_os_vector (d := d) OS lgc F)
          (bvt_minkowski_to_os_vector (d := d) OS lgc F) := by
  -- extend the core theorem by continuity/density

lemma bvt_wightman_sesquilinear_form_eq_osHilbert_inner
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F G : BorchersSequence d,
      WightmanInnerProduct d (bvt_W OS lgc) F G =
        inner
          (bvt_minkowski_to_os_vector (d := d) OS lgc F)
          (bvt_minkowski_to_os_vector (d := d) OS lgc G) := by
  -- optional but paper-faithful: polarization plus continuity/density

lemma bvt_W_positive_from_transport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  intro F
  rw [bvt_wightman_quadratic_form_eq_vector_norm_sq (d := d) OS lgc F]
  exact positivity_of_vector_norm_sq _
```

### Task 5b. What the "initial core" must mean

The placeholder `bvtInitialCore` above should not be left semantically vague.
For the OS I Section 4.3 route, it must mean:

1. an algebraic subspace of `BorchersSequence d` on which the transport map to
   OS/Hilbert vectors is already concretely defined from the continuation data;
2. a subspace dense enough that continuity extends the quadratic-form identity
   from that core to all Borchers sequences;
3. a subspace on which the positive-time theorem from Tasks 1-4 can actually be
   applied after the required rewrites.

So the documentation-standard theorem slots should also record:

```lean
def bvtInitialCore
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    Submodule ℂ (BorchersSequence d) := by
  -- the algebraic image of the Section 4.3 transport construction,
  -- before completion and before continuity extension

lemma bvtInitialCore_dense
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    Dense (bvtInitialCore (d := d) OS lgc : Set (BorchersSequence d)) := by
  -- this is the concrete dense-core theorem that replaces vague "density of u"

lemma bvt_positiveTime_theorem_applies_on_initialCore
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F ∈ bvtInitialCore (d := d) OS lgc,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  -- unwind membership in the core until the positive-time theorem from Tasks 1-4
  -- applies literally
```

This is the right level of precision for the final theorem-3 layer. If a later
implementation cannot define such a core cleanly, that should be treated as a
signal that the route has drifted away from the OS I positivity proof.

This is the exact point where the theorem-3 blueprint meets the OS I Section
4.3 audit in `docs/os1_detailed_proof_audit.md`. If the repo later chooses a
different final theorem surface, it should be justified by an explicit theorem
showing that the new surface is equivalent to this transport/density route.

Equally important: the compact-approximation convergence theorem

`tendsto_compactApproxPositiveTimeBorchers_diff_osInner`

from `OSToWightmanSpatialMomentum.lean` belongs to closure layer 2, not layer 3.
It says compactly supported approximants are dense **inside the positive-time
OS Hilbert sector**. It does *not* by itself reduce an arbitrary
`BorchersSequence d` to the positive-time route. The docs should keep that
distinction explicit.

The same applies to hermiticity bookkeeping: the theorem
`bvt_hermitian` is already proved in `OSToWightmanBoundaryValues.lean` and is
consumed automatically by the positive-time reduction theorems. So theorem 3
no longer carries an open hermiticity hypothesis. The blueprint should always
refer to hermiticity as a solved prerequisite, not as an additional frontier.

## 7. "Do not do this" list

The current theorem-3 notes should explicitly ban the following moves:

1. Do not claim pointwise equality from the current scratch file without
   re-proving the domain and continuity hypotheses.
2. Do not add another wrapper reduction theorem for `bvt_W_positive`.
3. Do not use a same-test-function contour-shift slogan.
4. Do not recast the problem as an operator identity in GNS/Hilbert-space
   language unless the relevant analytic bridge has already been established.
5. Do not port stale `agents_chat` optimism into production without rechecking
   the actual current file contents.

## 7.1. Exact theorem-name dictionary for the current scratch facts

To avoid confusion when later porting from scratch to production, the trusted
scratch theorems should be referred to by their exact names:

1. `bvt_descendedAbsoluteInput_twoPoint_eq_semigroupShell_on_positiveStrip`
2. `integral_descendedAbsoluteInput_twoPoint_eq_semigroupShell_of_positiveSupport`
3. `commonFixedTimeCenterDiffKernel_eq_descendedAbsoluteInput_pairing_of_positiveSupport`
4. `commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport`

Anything stronger than those four should currently be treated as untrusted until
re-proved in the actual current file.

## 7.2. Trusted-vs-untrusted checklist for future porting

Before porting anything from scratch to production, check it against this list.

Trusted right now:
- positive-strip identity of the explicit descended kernel with the semigroup
  shell,
- positive-support integral equality for that explicit kernel,
- positive-support pairing equality between the common fixed-time kernel and the
  explicit descended kernel,
- positive-support pairing equality between the common zero-center section and
  the explicit descended kernel.

Not trusted right now:
- pointwise equality on the whole positive-time strip,
- any continuity theorem for the explicit descended kernel on a domain larger
  than what the reduced forward-tube factorization directly justifies,
- any claim that theorem 3 is now only a "mechanical extraction" problem.

This checklist should be re-read immediately before the later production port.

## 7.3. Exact "nothing left implicit" checklist for future Lean work

When theorem 3 proof work resumes, each of the following should have an
explicit theorem or lemma name written next to it in the local docs before any
large production edit proceeds:

1. common-kernel domain theorem
2. explicit-kernel domain theorem
3. common-kernel continuity theorem
4. explicit-kernel continuity theorem
5. support-to-positive-support reduction lemma for the uniqueness test
6. pairing equality theorem on compactly supported tests
7. uniqueness theorem application
8. rewrite from kernel equality to shell equality
9. rewrite from shell equality to `hschw`
10. rewrite from `hschw` to positive-time theorem-3 closure through the
    existing compact approximation chain
11. general-to-positive-time reduction closing the actual public frontier

If any one of these eleven slots is still blank, the documentation should say so
explicitly and the proof should not be described as "essentially done".

As of the current documentation state, all eleven slots now have an explicit
semantic description, and slot 11 also has a paper-faithful theorem-slot
inventory. The remaining incompleteness is no longer "what must be proved" but
"which exact local lemmas in the repo should carry each slot name when the Lean
port begins."

## 7.4. What counts as a complete theorem-3 documentation state

The theorem-3 docs should only be considered complete enough for Lean work when
all of the following are written down explicitly:

1. exact domains for both kernels,
2. exact continuity theorem names for both kernels,
3. exact support-reduction lemma from compact support to positive support,
4. exact uniqueness theorem name and its hypotheses,
5. exact rewrite theorem names for each semantic arrow in Section 6.0,
6. exact production theorem that consumes the final shell equality,
7. an explicit statement saying whether the route proves pointwise equality or
   only almost-everywhere equality and why that is sufficient,
8. an explicit note identifying whether the final frontier step is still the
   general-to-positive-time reduction or whether that bridge has already been
   isolated elsewhere in production.

Until then, the theorem-3 note should be treated as still under construction.

## 8. Minimal Lean pseudocode for the whole closure

If the documentation is doing its job, the later implementation should have the
following semantic shape.

```lean
/- Step A: common and explicit kernels live on the same positive-time domain. -/
theorem explicit_descended_kernel_continuous_on_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s) :
    ContinuousOn explicitKernel positiveTimeRegion := by
  -- restrict the fixed-strip continuity theorem to `{ξ | 0 < ξ 0}`

theorem common_zero_center_section_continuous_on_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s) :
    ContinuousOn commonKernel positiveTimeRegion := by
  -- restrict `continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local`
  -- to the positive-time region

/- Step B: their pairings agree on all positive-support test functions. -/
theorem common_pairing_eq_explicit_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc h : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ positiveTimeRegion)
    (s : ℝ) (hs : 0 < s) :
    ∫ ξ, commonKernel ξ * h ξ = ∫ ξ, explicitKernel ξ * h ξ := by
  simpa using
    commonZeroCenterShiftSection_pairing_eq_descendedAbsoluteInput_of_positiveSupport
      (d := d) OS lgc χc h hχc hh_pos s hs

/- Step C: uniqueness on the common domain. -/
theorem common_eq_explicit_descended_on_positive_domain
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s) :
    EqOn commonKernel explicitKernel positiveTimeRegion := by
  apply eqOn_positiveTime_of_compactSupport_schwartz_integral_eq_continuousOn_local
  · exact common_zero_center_section_continuous_on_positiveTime (d := d) OS lgc s hs
  · exact explicit_descended_kernel_continuous_on_positiveTime (d := d) OS lgc s hs
  · intro h hh_compact hh_support
    exact common_pairing_eq_explicit_pairing (d := d) OS lgc χc h hχc hh_support s hs

/- Step D: convert to the shell equality needed by theorem 3. -/
theorem compact_approx_componentwise_schwinger_eq_bvtW_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) :
    ∀ N n m (hm : 0 < m) (t : ℝ), 0 < t →
      let F_N := compactApproxPositiveTimeBorchers F N
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((((F_N : BorchersSequence d).funcs n).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t
            ((F_N : BorchersSequence d).funcs m))))) =
        bvt_W OS lgc (n + m)
          ((((F_N : BorchersSequence d).funcs n).conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t
              ((F_N : BorchersSequence d).funcs m)))) := by
  -- rewrite the common zero-center section to the fixed-time common kernel,
  -- rewrite the explicit kernel to the semigroup shell,
  -- invoke the existing production bridge theorem

/- Step E1: close the positive-time theorem through the existing wrappers. -/
theorem bvt_positiveTime_self_nonneg_from_hpath
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hpath :
      ∀ N n m (hm : 0 < m) (t ε : ℝ), 0 < t → 0 < ε →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N;
          ∫ x : NPointDomain d (n + m),
            bvt_F OS lgc (n + m) (fun k μ =>
              ↑(x k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
              ((((F_N : BorchersSequence d).funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((F_N : BorchersSequence d).funcs m))) x)
            =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((((F_N : BorchersSequence d).funcs n).osConjTensorProduct
                ((F_N : BorchersSequence d).funcs m)) y)) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  exact
    bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_boundary_ray_eq_xiShift
      (d := d) (OS := OS) (lgc := lgc) F hpath

/- Step E2: only after Step E1 should the public frontier be closed. -/
private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  intro F
  -- This step is *not* supplied by the compact-approximation package itself.
  -- It must be the exact final theorem reducing arbitrary Borchers sequences
  -- to the positive-time route, or else the frontier theorem should be
  -- restated honestly on `PositiveTimeBorchersSequence d`.
  exact
    general_borchers_to_positiveTime_reduction
      (d := d) (OS := OS) (lgc := lgc) F
      bvt_positiveTime_self_nonneg_from_hpath
```

That pseudocode should be treated as a goal, not as a statement that the
continuity hypotheses or the final
`BorchersSequence -> PositiveTimeBorchersSequence` reduction are already
available under those exact names.

## 9. Bottom line

The current theorem-3 frontier is much narrower than it used to be.

The honest remaining issue is not "positivity in general." It is:
- match the common one-variable kernel and the explicit descended boundary-value
  kernel on the correct positive-time domain,
- then hand that equality to the reduction chain already in production.

That is the only theorem-3 route this note endorses.
