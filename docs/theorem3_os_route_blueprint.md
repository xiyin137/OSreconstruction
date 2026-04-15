# Theorem 3 OS-Route Blueprint

Purpose: this note is the implementation blueprint for the live `E -> R`
frontier theorem

- `OSToWightmanBoundaryValues.lean`, private theorem `bvt_W_positive`.

This document is not a historical summary. It is the route specification to be
followed during Lean work. If the code seems to suggest a different route, the
docs must be repaired first and Lean work must pause.

This note should be read together with:

- `docs/os1_detailed_proof_audit.md`
- `docs/os2_detailed_proof_audit.md`
- `docs/mathlib_gap_analysis.md`
- `docs/sorry_triage.md`

## 1. The live theorem and the current production situation

The live theorem is:

```lean
private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re
```

The current production files still expose an older reduction chain through
boundary-ray / Schwinger / compact-approximation consumer interfaces. Those
surfaces are part of the current code graph, but they are **not** the theorem-3
blueprint any more. They are legacy consumers.

The theorem-3 blueprint now has exactly one endorsed route:

1. keep Packages A-B as valid one-variable support infrastructure;
2. do **not** use Package C / `hschw`, because that theorem surface is false;
3. build the OS I Section 4.3 transformed-image package:
   positive-time Euclidean data -> dense half-space transformed image ->
   OS Hilbert vector;
4. prove the quadratic identity on that transformed-image core, not on the same
   raw `BorchersSequence d` viewed on both sides;
5. extend positivity to arbitrary `BorchersSequence d` only afterwards, by the
   density/continuity closure supplied by the Section 4.3 image theorem.

That is the route Claude directed in `agents_chat.md`, and it is now the only
route this document endorses.

Implementation discipline:

1. the legacy `hschw` consumer interface may remain in production as deprecated
   dead-end infrastructure, but it is not an endorsed target theorem surface;
2. Package I is now the only endorsed theorem-3 closure route;
3. the old raw same-input theorem slogan for Package I is withdrawn;
4. if future work wants a different production endpoint than Package I, this
   blueprint must be rewritten first.

### 1.0. Mandatory documentation readiness gate

For this frontier, inability to close the live `bvt_W_positive` `sorry` is not
an invitation to add more production Lean scaffolding. It means this blueprint
is still missing mathematical proof detail.

Before any further blocker-facing Lean edit, the relevant subsection below must
state:

1. the exact theorem statement to implement;
2. the exact already-proved dependency names and files;
3. every hidden domain, support, compactness, integrability, Fourier-transform,
   and coercion obligation;
4. a proof transcript detailed enough that the Lean work is execution rather
   than route discovery;
5. the exact verification command for the touched file/module.

If any of those items is missing, pause production Lean and repair this
blueprint or the proof-audit docs first. Wrapper lemmas, conditional reducers,
residual limit algebra, and theorem-surface shuffling are forbidden in that
state unless the subsection explicitly identifies the lemma as a required
proof slot that directly discharges a named subgap.

### 1.1. Exact current local status on that route

The theorem-3 docs must distinguish three things:

1. what the route is in principle,
2. what is already implemented locally in production,
3. what exact theorem is still missing.

As of the current local branch state:

1. Package A is already implemented in
   `OSToWightmanPositivity.lean` as
   `identity_theorem_right_halfplane`;
2. Package B is already implemented there as
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`;
3. Package C / `hschw` has now been settled as false at the exact theorem
   surface; see `agents_chat.md` Entries `#283`, `#285`, `#286`;
4. the later positive-time / compact-approximation consumers still exist in
   `OSToWightmanBoundaryValuesBase.lean`,
   `OSToWightmanBoundaryValuesCompactApprox.lean`, and
   `OSToWightmanBoundaryValues.lean`, but they are legacy consumers rather than
   endorsed theorem-3 route definitions;
5. the live theorem-3 frontier is now the corrected Package-I theorem surface;
6. the older raw theorem slogan
   `WightmanInnerProduct(bvt_W)(F,F).re = ‖u(F)‖^2` for the same raw
   `BorchersSequence d` on both sides is not endorsed and is under
   correction.

So the current frontier is not “find a theorem-3 route.” The route is fixed.
The current frontier is:

1. keep Packages A-B as valid support infrastructure,
2. stop treating Package C as a live theorem to prove,
3. repair Package I to the actual Section 4.3 transformed-image theorem
   surface,
4. only then implement the resulting transport / density / closure package.

### 1.2. Iteration B retraction (2026-04-07)

Between April 6 and April 7, 2026, branch `3b` briefly adopted "Option alpha"
(full Schwartz codomain via an internal Seeley extension) as the working
codomain choice for `os1TransportComponent`. A direct re-reading of the OS I
PDF on April 7, 2026, showed this is off-paper: OS I p. 95 Lemma 4.1 writes
the codomain as `L(R_+^{4n})`, i.e. the half-space Schwartz target, not the
full ambient Schwartz space.

Iteration B's Option alpha is therefore retracted, and the chosen codomain
reverts to **Option beta (quotient model of the half-space target)**.

This retraction implies:

1. the production docstring on `os1TransportComponent` should no longer claim
   the full-Schwartz / Seeley-extension route;
2. branch `3b` sub-CLM work should not spend time on a Seeley-extension stage;
3. the real branch-`3b` challenge remains the concrete partial-spatial-Fourier
   infrastructure, but now with the correct half-space codomain.

## 2. Exact existing theorem hooks already available

The current code already provides the main ingredients for the endorsed route.
The later Lean port should consume these exact theorem surfaces instead of
inventing new theorem shapes.

### 2.1. Holomorphic / boundary-value package

In `OSToWightmanBoundaryValueLimits.lean`:

- `bvt_singleSplit_xiShiftHolomorphicValue`
- `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
- `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
- `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
- `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`

These theorems already package the one-variable holomorphic object attached to a
single/split pair and the relevant `z -> 0+` limit statements.

In `OSToWightmanPositivity.lean`:

- `identity_theorem_right_halfplane`
- `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`

These are the current local production implementations of Packages A and B.
Note that the implemented Package-B theorem currently uses the simpler surface
`OSInnerProductTimeShiftHolomorphicValue` specialized to positive-time singles,
not the broader `...ExpandBoth` wrapper. That is fine and should be treated as
the canonical current production start point.

### 2.2. OS inner-product package

In `SchwingerOS.lean`:

- `PositiveTimeBorchersSequence`
- `PositiveTimeBorchersSequence.single`
- `PositiveTimeBorchersSequence.osInner`
- `PositiveTimeBorchersSequence.osInner_nonneg_self`
- `PositiveTimeBorchersSequence.osInner_eq_sum_right_singles`
- `OSInnerProduct_single_single`
- `OSInnerProduct_right_single`
- `OSInnerProduct_eq_sum_right_singles`
- `OSInnerProduct_zero_right`
- `OSInnerProduct_hermitian`

This is the OS-side algebraic package the theorem-3 proof should use.

### 2.3. Semigroup / time-shift package

In `OSToWightmanSemigroup.lean` and `OSToWightman.lean`:

- `OSInnerProductTimeShiftHolomorphicValue`
- `OSInnerProductTimeShiftHolomorphicValue_differentiableOn`
- `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single`
- `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `continuousOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_piecewise_xiShift`

This is the OS-side holomorphic family to compare against
`bvt_singleSplit_xiShiftHolomorphicValue`.

### 2.4. Compact-approximation package

In `OSToWightmanBoundaryValuesCompactApprox.lean`:

- `compactApproxPositiveTimeBorchers`
- `compactApproxPositiveTimeBorchers_component_compact`
- `tendsto_compactApproxPositiveTimeBorchers_term`
- `tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_timeShift_eq_osInner`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_ofReal_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`

These theorems can still be used as **consumer interfaces** once the direct
positive-time semigroup bridge has been proved. They are not the route
definition.

### 2.5. Continuity package

In `OSToWightmanBoundaryValuesBase.lean` and nearby files:

- `bvt_W_continuous`
- `wightmanInner_eq_osInner_of_orderedPositive_termwise`
- `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
- `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero_right`
- `bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero`
- finite-sum expansions of `WightmanInnerProduct`
- right-single and zero-right reduction lemmas

This is the continuity package already used by the legacy positive-time
consumer chain. It is no longer the endorsed final theorem-3 closure route.

## 3. What the OS papers require here

OS I and OS II both point to the same theorem shape:

1. identify the correct one-variable scalar holomorphic object;
2. prove equality of the Minkowski-side and OS-side scalar functions on the
   right half-plane from equality on positive reals;
3. take the `z -> 0+` limit to recover the boundary pairing identity;
4. use that scalar/boundary-value identity only inside the corrected Section
   4.3 transformed-image package, not as a same-input quadratic-form identity
   on `PositiveTimeBorchersSequence d`;
5. extend positivity to the full Borchers space by the Section 4.3 transport
   map and Hilbert-norm identity.

So the actual theorem-3 content is **not**:

- a contour-deformation theorem,
- a `K2VI1` comparison theorem,
- a new shell wrapper,
- or a raw algebraic-core theorem on `Submodule ℂ (BorchersSequence d)`.

The actual theorem-3 content is:

- positive-time semigroup identity,
- Section 4.3 transformed-image map to `OSHilbertSpace OS`,
- Hilbert-norm realization of the Wightman quadratic form on that transformed
  image, followed by density/continuity closure.

## 4. Route that is explicitly forbidden

The later Lean implementation must not drift back to any of the following:

1. `hpath` / contour-deformation / boundary-ray route.
2. `hschw` as the **target theorem shape**.
3. k=2-specific common-kernel transport as theorem-3 infrastructure.
4. defining `bvtInitialCore : Submodule ℂ (BorchersSequence d)`.
5. adding ad hoc `AddCommGroup`, `Module ℂ`, or topology instances to raw
   `BorchersSequence d` just to mimic paper notation.
6. inventing any new reduction theorem whose only purpose is to repackage the
   same positivity seam.

Historical note:

- the current production consumer theorem
  `bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
  may still be used after the positive-time semigroup bridge is proved;
- but the proof should **arrive** at that theorem from the positive-time
  semigroup route, not target `hschw` as the mathematical endpoint.

## 5. Corrected theorem package

The theorem-3 proof package should now be implemented in the following order.
This order is mathematical, not merely organizational.

### 5.1. Package A: one-variable identity theorem

The first theorem slot is:

```lean
theorem identity_theorem_right_halfplane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hagree : ∀ t : ℝ, 0 < t → f (t : ℂ) = g (t : ℂ)) :
    ∀ z : ℂ, 0 < z.re → f z = g z
```

This theorem is local complex analysis only. It should be proved once and then
reused.

Primary use in theorem 3:

- `f z = bvt_singleSplit_xiShiftHolomorphicValue ... z`
- `g z = OSInnerProductTimeShiftHolomorphicValue ... z`

### 5.2. Package B: compact positive-time single/split bridge

For compactly supported positive-time components, prove the direct one-variable
identity:

```lean
theorem bvt_singleSplit_eq_osTimeShift_on_rightHalfPlane
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hm : 0 < m) :
    ∀ z : ℂ, 0 < z.re →
      bvt_singleSplit_xiShiftHolomorphicValue (d := d) OS lgc hm
        f hf_ord hf_compact g hg_ord hg_compact z
        =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) z
```

Proof transcript:

1. use
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
   and
   `OSInnerProductTimeShiftHolomorphicValue_differentiableOn`;
2. use
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
   for the Wightman-side real-axis formula;
3. use
   `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single`
   specialized to a positive-time single left factor, or equivalently
   the already implemented production theorem
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`;
4. check that both real-axis formulas equal the same positive-real Schwinger
   time-shift expression;
5. apply `identity_theorem_right_halfplane`.

This is the core analytic theorem. Everything after this is algebra and
continuity.

Exact current implementation note:

1. the current local production theorem for Package B is already
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` in
   `OSToWightmanPositivity.lean`;
2. later work should build on that theorem, not reprove Package B under a
   slightly different wrapper unless there is a compelling API reason.

### 5.3. Package C: false legacy theorem surface

Package C is **not** a live frontier any more. It is the old positive-real
same-shell theorem surface externalized as `hschw`, and it is mathematically
false.

The legacy theorem surface was:

```lean
theorem schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift_of_compact_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hm : 0 < m) :
    ∀ t : ℝ, 0 < t →
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
        =
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
```

This is the exact theorem externalized today as the hypothesis `hschw` in
`OSToWightmanBoundaryValueLimits.lean` and
`OSToWightmanBoundaryValuesCompactApprox.lean`.

Exact reason it is false:

1. for the free scalar field, the left-hand side evaluates to a Euclidean/OS
   Laplace-type quantity with factor `e^{-ω_p t}`;
2. the right-hand side evaluates to the reconstructed Wightman boundary-value
   pairing against a real Minkowski time translation, with oscillatory factor
   `e^{-i ω_p t}`;
3. the test functions also appear through different transforms on the two
   sides: Laplace on the OS side, Fourier on the Wightman side;
4. so the two sides do not agree on the exact intended theorem surface.

See `agents_chat.md` Entry `#283` for the exact free-field counterexample and
Entries `#285`-`#286` for the exact-surface verification against the repo
definitions.

Operational consequence:

1. the legacy `hschw` theorems may remain in production as logically valid
   implications from a false premise;
2. they should be marked deprecated/dead-end and not used to guide theorem-3
   proof work;
3. Package I is now the only endorsed theorem-3 route.

### 5.3.1. Existing theorem inventory still relevant after the correction

Existing production infrastructure already supporting this route:

1. `identity_theorem_right_halfplane` in `OSToWightmanPositivity.lean`;
2. `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` in
   `OSToWightmanPositivity.lean`;
3. `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` in
   `OSToWightmanBoundaryValueLimits.lean`;
4. `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
   in `OSToWightmanSemigroup.lean`;
5. `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   and
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
   in `OSToWightmanBoundaryValueLimits.lean`.

Core Wightman-side boundary-value infrastructure already present:

1. `full_analytic_continuation_boundaryValueData`;
2. `boundary_values_tempered`;
3. `bvt_W`;
4. `bvt_F`;
5. `bvt_W_continuous`;
6. `bvt_W_linear`;
7. `bvt_F_holomorphic`;
8. `bvt_boundary_values`.

These are important because the Package-C spectral/Laplace strategy does not
only need the OS-side semigroup object; it also needs the exact theorem surfaces
that realize the reconstructed Wightman pairing as the boundary value of the
forward-tube witness `bvt_F`.

Particularly relevant BV-side spectral/Laplace bridge theorems already in
`OSToWightmanBoundaryValuesBase.lean`:

1. `bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift`;
2. `bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift_translate_spatial_right`;
3. `bvt_OSInnerProductTimeShiftHolomorphicValue_onePoint_pair_eq_xiShift_centerShear_local`;
4. `bvt_OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial_right`.

These remain useful as support infrastructure for the corrected Section 4.3
transport-map route, but they should no longer be read as evidence that the old
same-shell Package-C theorem is true.

Useful transcript guides from older support files:

1. `schwinger_simpleTensor_timeShift_eq_xiShift`;
2. `OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift`;
3. `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_piecewise_xiShift`.

These older theorems are valuable because they already write out the OS-side
positive-real / Euclidean-`xiShift` conversion in detail. They should be used
as proof transcripts, not as reasons to revert to an off-blueprint theorem
surface.

Zero-right and helper transport facts:

1. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero_zeroRight_of_hermitian`
   still handles the `m = 0` repair only;
2. `boundary_ray_hermitian_pairing_of_F_negCanonical`,
   `bv_hermiticity_transfer_of_F_reflect`,
   `bv_timeReversal_transfer`,
   `boundary_ray_timeReversal_pairing_of_F_timeReversalCanonical`,
   and `tendsto_boundary_negReverse_pairing`
   remain helper transport theorems only.

They may assist a future proof, but they are not themselves the OS I Section 4.3
Fourier-Laplace mechanism.

### 5.3.2. What this correction means for the codebase

1. do not spend any further theorem-3 effort trying to prove the old
   `schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift` surface;
2. do not revive a same-shell bridge
   `bvt_W (f.conjTensorProduct g) = OS.S (f.osConjTensorProduct g)`;
3. keep Packages A-B as valid support lemmas;
4. treat the current `hschw` consumer theorems as deprecated legacy
   infrastructure only;
5. move directly to Package I.

Exact current handoff theorems after the correction:

1. the `hschw`-consuming compact-approximation theorems remain compiled legacy
   infrastructure but are no longer part of the endorsed route;
2. the live theorem-3 implementation target remains Package I, with the
   current sub-blocker being the canonical shell-to-Laplace identification in
   §5.9.4a.1.ε before the separate Section-4.3 `hH_imag_os` identification;
3. the older theorems
   `bvt_wightmanInner_single_single_eq_osInner_of_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   and
   `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   remain legacy consumers only and should not drive new theorem-3 production.

### 5.4. Package D: withdrawn raw positive-time sesquilinear route

The theorem surface

```lean
WightmanInnerProduct d (bvt_W OS lgc)
  (F : BorchersSequence d) (G : BorchersSequence d)
  =
OSInnerProduct d OS.S
  (F : BorchersSequence d) (G : BorchersSequence d)
```

for raw `F G : PositiveTimeBorchersSequence d` is **false** and must not be
implemented.

Reason:

1. the Wightman side uses the Borchers/Fourier involution through
   `conjTensorProduct`;
2. the OS side uses the Euclidean/Laplace involution through
   `osConjTensorProduct`;
3. these are not the same quantity even at `t = 0`;
4. therefore summing the single/split bridge theorems does **not** produce a
   same-input sesquilinear identity on the positive-time class.

Consequences:

1. `bvt_wightmanInner_eq_osInner_of_positiveTime` is withdrawn as a theorem
   target;
2. the legacy consumer theorems that look like positive-time `osInner`
   comparisons remain compiled only as historical infrastructure and should not
   drive any new theorem-3 production;
3. the corrected route moves directly from the single/split bridge to the
   Section 4.3 transformed-image / transport package.

### 5.5. Package E: withdrawn raw positive-time positivity route

The theorem surface

```lean
0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
  (F : BorchersSequence d) (F : BorchersSequence d)).re
```

for raw `F : PositiveTimeBorchersSequence d` should **not** be pursued by
rewriting to `OSInnerProduct` on the same literal input. That route depends on
the false Package-D identity and is therefore quarantined together with it.

What remains true is only:

1. some existing compiled theorems still consume old Package-D-style inputs;
2. they may remain in the codebase as deprecated legacy consumers;
3. they are not part of the endorsed theorem-3 proof route.

The analytic core now passes straight from the single/split bridge to Package I.

### 5.6. Package F: ordered-positive-time density in each degree

Important route correction:

The naive raw-density slogan

```lean
Dense {f : SchwartzNPoint d n |
  tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}
```

is not mathematically correct on the full Schwartz space. If
`x ∉ OrderedPositiveTimeRegion d n`, then point evaluation `f ↦ f x` is a
continuous linear functional and it vanishes on every function whose support is
contained in `OrderedPositiveTimeRegion d n`. So that set cannot be dense in
all of `SchwartzNPoint d n`.

Therefore the raw theorem surface originally written in this section is
quarantined and must not be implemented as stated.

This means the older density route is withdrawn, not merely awaiting repair.
The later Lean implementation should not start from a global topology on raw
`BorchersSequence d`, and it should not attempt to resurrect Package F as a
real theorem on full Schwartz space.

Quarantined theorem slots (recorded here only so later work does not
accidentally reintroduce them as if they were valid):

```lean
theorem orderedPositiveTime_dense_schwartzNPoint
    (n : ℕ) :
    Dense
      {f : SchwartzNPoint d n |
        tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

theorem exists_orderedPositiveTime_seq_tendsto
    (n : ℕ) (f : SchwartzNPoint d n) :
    ∃ g : ℕ → SchwartzNPoint d n,
      (∀ k, tsupport (g k : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
        ∧ Tendsto g atTop (𝓝 f)
```

Exact current implementation status:

1. there is **no** current production theorem implementing Package F yet;
2. the existing family `compactApproxPositiveTimeBorchers` in
   `OSToWightmanSpatialMomentum.lean` is **not** Package F:
   it approximates an already positive-time Borchers sequence by compactly
   supported positive-time Borchers sequences, but it does not approximate an
   arbitrary Schwartz component by ordered-positive-time data;
3. this section is retained only as a warning / historical quarantine, not as
   endorsed implementation guidance.

### 5.7. Package G: componentwise positive-time approximation of Borchers sequences

The original Package-G statement depended on the quarantined raw Package-F
statement above. So this section is also historical only, not a currently
endorsed theorem surface.

Recommended theorem slot:

```lean
theorem exists_positiveTime_componentwise_approximation
    (F : BorchersSequence d) :
    ∃ G : ℕ → PositiveTimeBorchersSequence d,
      (∀ n, Tendsto (fun k => ((G k : BorchersSequence d).funcs n)) atTop (𝓝 (F.funcs n)))
        ∧ (∀ k, (G k : BorchersSequence d).bound = F.bound)
```

What remains fixed is only the negative guidance:

1. do not force a raw topological structure on `BorchersSequence d`;
2. do not reintroduce raw support-density claims on full Schwartz space;
3. use Package I instead of trying to revive this approximation route.

Exact current implementation status:

1. there is **no** current production theorem implementing Package G, and none
   is currently endorsed;
2. `compactApproxPositiveTimeBorchers` should be treated only as an internal
   compact-support approximation inside the positive-time class;
3. it is not the final arbitrary-`BorchersSequence` approximation theorem and
   should not be documented or used as if it were.

### 5.8. Package H: withdrawn continuity-after-density route

This section records the old continuity-after-density plan only so it is not
accidentally revived as current blueprint guidance.

Recommended theorem slots:

```lean
theorem WightmanInnerProduct_tendsto_of_componentwise_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d)
    (G : ℕ → BorchersSequence d)
    (hbound : ∀ k, (G k).bound = F.bound)
    (hcomp : ∀ n, Tendsto (fun k => (G k).funcs n) atTop (𝓝 (F.funcs n))) :
    Tendsto
      (fun k => WightmanInnerProduct d (bvt_W OS lgc) (G k) (G k))
      atTop
      (𝓝 (WightmanInnerProduct d (bvt_W OS lgc) F F))

theorem re_WightmanInnerProduct_tendsto_of_componentwise_tendsto
    ...
```

Proof transcript:

1. expand `WightmanInnerProduct` as a finite double sum up to `F.bound`;
2. for each fixed pair `(n,m)`, use `bvt_W_continuous` and the product
   convergence of the component approximants;
3. move the limit through the finite sum.

This is where the route uses the finite-support nature of `BorchersSequence d`
instead of forcing a global topological structure.

Acceptable implementation helper:

1. if the eventual Lean code wants a helper theorem phrased as continuity of
   the real quadratic form on a **fixed-bound product space**
   `(n : Fin (B + 1)) → SchwartzNPoint d n`, that is acceptable;
2. such a theorem is still only a repackaging of the finite-sum argument above,
   because the bound `B` is fixed and the quadratic form expands to a finite
   double sum of already-continuous pairings;
3. what should still be avoided is restarting theorem 3 from a new global
   topological structure on raw `BorchersSequence d` itself.

Exact current implementation status:

1. the repo already contains a concrete model of this continuity argument for
   one specific approximation family:
   `tendsto_compactApproxPositiveTimeBorchers_term` and
   `tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self` in
   `OSToWightmanBoundaryValuesCompactApprox.lean`;
2. these theorems show that the finite-sum continuity route is formally viable
   on the current encoding of `BorchersSequence d`;
3. however, they are still only special-case continuity theorems for the
   compact-support truncation family, not the final general Package-H theorem.

### 5.9. Package I: final public closure via the OS I Section 4.3 transformed-image package

After the density-route correction, the final theorem-3 closure package is no
longer the withdrawn raw positive-time approximation theorem. But it is also
not the naive raw theorem

`(WightmanInnerProduct d (bvt_W OS lgc) F F).re = ‖u(F)‖ ^ 2`

for the same raw `BorchersSequence d` on both sides.

OS I Section 4.3 itself first constructs a dense transformed image `L` of
positive-time Euclidean test functions inside the half-space Schwartz target
`L(R_+^{4n})` on the Minkowski side (Lemma 4.1), then defines `u` on that
image (Eq. (4.27)), and then proves the quadratic identity there
(Eq. (4.28)). Only afterwards does one recover the full public positivity
statement by density/continuity.

Just as importantly, the naive same-test-function identity is false even at
`t = 0`: one must transport Euclidean test functions on the Laplace side to the
positive-energy Minkowski test-function side before the Wightman quadratic form
matches the OS Hilbert norm.

So the old raw theorem slots are withdrawn. The corrected theorem slots are:

```lean
/-- The degree-`n` positive-time Euclidean domain used in OS I Section 4.3.

This is the paper's `S_+(ℝ^{4n})`: Schwartz `n`-point test functions whose
topological support lies in the ordered positive-time region. If the eventual
Lean implementation prefers an equivalent `Submodule ℂ (SchwartzNPoint d n)`
presentation rather than a subtype, that is acceptable, but it must represent
the same paper domain. -/
def EuclideanPositiveTimeComponent (d n : ℕ) [NeZero d] :=
  {f : SchwartzNPoint d n //
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

/-- The degree-`n` Section 4.3 positive-energy codomain.

This is **not** the support-restricted subtype
`{f : SchwartzNPoint d n // tsupport f ⊆ PositiveEnergyRegion}`.
It is also **not** the full ambient `SchwartzNPoint d n` equipped with a
false `DenseRange` claim.

The correct theorem surface is the paper's half-space Schwartz target
`L(R_+^{4n})`, implemented in production by the quotient model
`SchwartzNPoint d n ⧸ {f | f = 0 on section43PositiveEnergyRegion}`. The
current blueprint no longer endorses either:
- the false support-restricted subtype
  `{f : SchwartzNPoint d n // tsupport f ⊆ PositiveEnergyRegion}`, or
- a fixed global Seeley-extension choice landing in full ambient
  `SchwartzNPoint d n`.
-/
def Section43PositiveEnergyComponent (d n : ℕ) [NeZero d] := ...

/-- The degree-`n` Section 4.3 Fourier-Laplace transport
(OS I (4.19)-(4.20)) landing in the corrected half-space codomain. -/
noncomputable def os1TransportComponent
    (d n : ℕ) [NeZero d] :
    EuclideanPositiveTimeComponent d n →L[ℂ] Section43PositiveEnergyComponent d n

/-- The degree-`n` Section 4.3 transformed image. -/
def bvtTransportImage (d n : ℕ) [NeZero d] :
    Set (Section43PositiveEnergyComponent d n) :=
  Set.range (os1TransportComponent d n)

-- Convention: time components are cumulative energy variables; spatial
-- components are cumulative `-momentum / (2 * Real.pi)` variables, matching
-- Mathlib's spatial Fourier kernel `𝐞 (-(inner ℝ _ _))`.

/- Point reversal used to turn existing prefix sums into tail sums.
Inside `namespace OSReconstruction`, the flat equivalence from
`ForwardTubeDistributions.lean` must be referenced as
`_root_.flattenCLEquivReal`. -/
noncomputable def section43PointReverseCLE
    (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃L[ℝ] NPointDomain d n :=
  (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) Fin.revPerm).toContinuousLinearEquiv

@[simp] theorem section43PointReverseCLE_apply
    (d n : ℕ) [NeZero d]
    (x : NPointDomain d n) (k : Fin n) :
    section43PointReverseCLE d n x k = x (Fin.rev k)

private theorem section43_fin_rev_prefix_sum_eq_tail_sum
    {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → A) (j : Fin n) :
    (∑ l : Fin ((Fin.rev j).val + 1),
        f (Fin.rev ⟨l.val, by omega⟩)) =
      ∑ k : Fin n, if j.val ≤ k.val then f k else 0

/- Concrete construction: build the unscaled tail-sum equivalence by flattening,
reversing points, applying the existing partial-sum inverse
`section43DiffCoordRealCLE.symm`, and reversing back. -/
noncomputable def section43RawCumulativeTailMomentumCLE
    (d n : ℕ) [NeZero d] :
    (Fin (n * (d + 1)) → ℝ) ≃L[ℝ] NPointDomain d n :=
  (((_root_.flattenCLEquivReal n (d + 1)).symm).trans
    (section43PointReverseCLE d n)).trans
    (((section43DiffCoordRealCLE d n).symm).trans
      (section43PointReverseCLE d n))

@[simp] theorem section43RawCumulativeTailMomentumCLE_apply
    (d n : ℕ) [NeZero d]
    (ξ : Fin (n * (d + 1)) → ℝ) (j : Fin n) (μ : Fin (d + 1)) :
    section43RawCumulativeTailMomentumCLE d n ξ j μ =
      ∑ k : Fin n,
        if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0

@[simp] theorem section43RawCumulativeTailMomentumCLE_symm_apply
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    (section43RawCumulativeTailMomentumCLE d n).symm q
        (finProdFinEquiv (k, μ)) =
      q k μ - if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0

noncomputable def section43SpatialFourierScaleLinearEquiv
    (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃ₗ[ℝ] NPointDomain d n where
  toFun := fun q j μ =>
    if μ = 0 then q j μ else -(1 / (2 * Real.pi)) * q j μ
  invFun := fun q j μ =>
    if μ = 0 then q j μ else -(2 * Real.pi) * q j μ
  map_add' := by
    intro q r
    ext j μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hμ]
      ring
  map_smul' := by
    intro a q
    ext j μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hμ]
      ring
  left_inv := by
    intro q
    ext j μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hμ]
      field_simp [Real.pi_ne_zero]
  right_inv := by
    intro q
    ext j μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hμ]
      field_simp [Real.pi_ne_zero]

noncomputable def section43SpatialFourierScaleCLE
    (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃L[ℝ] NPointDomain d n :=
  (section43SpatialFourierScaleLinearEquiv d n).toContinuousLinearEquiv

@[simp] theorem section43SpatialFourierScaleCLE_apply
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (j : Fin n) (μ : Fin (d + 1)) :
    section43SpatialFourierScaleCLE d n q j μ =
      if μ = 0 then q j μ else -(1 / (2 * Real.pi)) * q j μ

@[simp] theorem section43SpatialFourierScaleCLE_symm_apply
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (j : Fin n) (μ : Fin (d + 1)) :
    (section43SpatialFourierScaleCLE d n).symm q j μ =
      if μ = 0 then q j μ else -(2 * Real.pi) * q j μ

noncomputable def section43CumulativeTailMomentumCLE
    (d n : ℕ) [NeZero d] :
    (Fin (n * (d + 1)) → ℝ) ≃L[ℝ] NPointDomain d n :=
  (section43RawCumulativeTailMomentumCLE d n).trans
    (section43SpatialFourierScaleCLE d n)

@[simp] theorem section43CumulativeTailMomentumCLE_apply
    (d n : ℕ) [NeZero d]
    (ξ : Fin (n * (d + 1)) → ℝ) (j : Fin n) (μ : Fin (d + 1)) :
    section43CumulativeTailMomentumCLE d n ξ j μ =
      if μ = 0 then
        ∑ k : Fin n,
          if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0
      else
        -(1 / (2 * Real.pi)) *
          ∑ k : Fin n,
            if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0

@[simp] theorem section43CumulativeTailMomentumCLE_symm_apply
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    (section43CumulativeTailMomentumCLE d n).symm q
        (finProdFinEquiv (k, μ)) =
      if μ = 0 then
        q k μ - if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0
      else
        -(2 * Real.pi) *
          (q k μ - if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0)

/- Proof transcript for the cumulative-tail simp lemmas:
1. `section43RawCumulativeTailMomentumCLE_apply`: unfold the `trans`
   construction and simplify with `_root_.flattenCLEquivReal_symm_apply`,
   `section43PointReverseCLE_apply`, and
   `section43DiffCoordRealCLE_symm_apply`.  The remaining finite-sum rewrite is
   exactly `section43_fin_rev_prefix_sum_eq_tail_sum` with
   `f := fun k => ξ (finProdFinEquiv (k, μ))`.
2. `section43RawCumulativeTailMomentumCLE_symm_apply`: unfold the symm of the
   same `trans` construction and simplify with
   `section43DiffCoordRealCLE_apply`.  The `if h : k.val + 1 < n` branch is
   the predecessor/successor case produced after reversing indices.
3. `section43_fin_rev_prefix_sum_eq_tail_sum`: rewrite the right side as the
   sum over `Finset.univ.filter (fun k => j.val ≤ k.val)`, then apply
   `Finset.sum_bij` with forward map
   `l ↦ Fin.rev ⟨l.val, by omega⟩` and inverse map
   `k ↦ ⟨(Fin.rev k).val, by omega⟩`.  The range proofs are pure `omega`
   after `simp [Fin.rev]`; injectivity follows from `Fin.rev` injectivity and
   `Fin.ext`.
4. `section43SpatialFourierScaleLinearEquiv`: the additive and scalar proofs
   close by splitting on `μ = 0`, `simp`, and `ring`; the inverse proofs close
   by the same split and `field_simp [Real.pi_ne_zero]`.
5. The final apply/symm lemmas for `section43CumulativeTailMomentumCLE` are
   just the raw apply/symm lemmas followed by the scale apply/symm lemmas. -/

noncomputable def section43FrequencyRepresentative
    (d n : ℕ) [NeZero d] :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43CumulativeTailMomentumCLE d n).symm).comp
    ((physicsFourierFlatCLM : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ).comp
      (flattenSchwartzNPoint (d := d)))

noncomputable def section43FrequencyProjection
    (d n : ℕ) [NeZero d] :
    SchwartzNPoint d n →L[ℂ] Section43PositiveEnergyComponent d n :=
  (section43PositiveEnergyQuotientMap (d := d) n).comp
    (section43FrequencyRepresentative (d := d) n)

/-- Additive closure of the Section 4.3 image. -/
theorem bvtTransportImage_add
    {n : ℕ} {f g : Section43PositiveEnergyComponent d n} :
    f ∈ bvtTransportImage (d := d) n →
    g ∈ bvtTransportImage (d := d) n →
    f + g ∈ bvtTransportImage (d := d) n

/-- Scalar closure of the Section 4.3 image. -/
theorem bvtTransportImage_smul
    {n : ℕ} {c : ℂ} {f : Section43PositiveEnergyComponent d n} :
    f ∈ bvtTransportImage (d := d) n →
    c • f ∈ bvtTransportImage (d := d) n

/-- For positive degree, the current support-restricted Section 4.3 source is
not dense in the half-space quotient codomain. Degree `0` is exceptional: the
source already is the full ambient Schwartz space there. The honest
quotient-side dense map is the ambient Schwartz quotient map, not
`os1TransportComponent` itself. -/
theorem not_denseRange_os1TransportComponent_succ
    (n : ℕ) :
    ¬ DenseRange (os1TransportComponent d (n + 1))

/-- Finite Borchers data whose every component lies in the Section 4.3 image. -/
structure BvtTransportImageSequence (d : ℕ) [NeZero d] where
  toBorchers : BorchersSequence d
  image_mem : ∀ n,
    section43FrequencyProjection (d := d) n (toBorchers.funcs n) ∈
      bvtTransportImage (d := d) n

/-- The OS I Section 4.3 transport map on the transformed-image core. -/
noncomputable def bvt_transport_to_osHilbert_onImage
    (OS : OsterwalderSchraderAxioms d) :
    BvtTransportImageSequence d → OSHilbertSpace OS

/-- The transport map is independent of the Section 4.3 preimage choice. -/
theorem bvt_transport_to_osHilbert_onImage_wellDefined
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) :
    ...

/-- Additivity on the transformed-image core. -/
theorem bvt_transport_to_osHilbert_onImage_add
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage (d := d) OS (F + G) =
      bvt_transport_to_osHilbert_onImage (d := d) OS F +
      bvt_transport_to_osHilbert_onImage (d := d) OS G

/-- Complex-linearity on the transformed-image core. -/
theorem bvt_transport_to_osHilbert_onImage_smul
    (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage (d := d) OS (c • F) =
      c • bvt_transport_to_osHilbert_onImage (d := d) OS F

/-- Stage-5 prerequisite: multivariate quotient descent for the explicit
Section-4.3 Fourier-Laplace transform.

This is the multivariate analog of
`fourierPairingDescendsToSection43PositiveEnergy1D_partialFourierSpatial_timeSlice`.
It should identify the abstract quotient-valued transform
`os1TransportComponent` with the concrete iterated `partialFourierSpatial_fun`
/ `complexLaplaceTransform` / `fourierLaplaceExt` computation degreewise. -/
theorem section43_iteratedSlice_descendedPairing
    (n : ℕ) (f : EuclideanPositiveTimeComponent d n) :
    ... := by
  ...

Exact current-code milestone:
- the full slice-descent theorem is now formalized as the private theorem
  `section43_iteratedSlice_descendedPairing` in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
- the earlier theorem `section43_iteratedSlice_descendedPairing_imagAxis`
  remains as the first concrete fragment, but it is no longer the live
  milestone;
- the reusable one-variable interchange step is now formalized privately as
  `one_variable_time_interchange_for_wightman_pairing`, together with the
  kernel-reduction chain down to an ambient upper-half-plane witness, in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
- `OSToWightmanPositivity.lean` is now `sorry`-free; the active public
  theorem-3 `sorry` remains `bvt_W_positive` in
  [OSToWightmanBoundaryValues.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean);
- the slice-side vanishing package is now formalized on both pairing
  orientations, including
  `fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`
  and
  `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`
  in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
- the flattened spectral / dual-cone package is now closed in
  [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean),
  culminating in
  `bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened`;
- the next honest Stage-5 blocker is therefore the actual witness-consuming
  seam: the ambient upper-half-plane witness has now been canonicalized as an
  explicit `fourierLaplaceExt` of the real-time Wightman pairing functional,
  with a concrete imaginary-axis formula; the remaining work is to identify
  those values with the semigroup-side holomorphic matrix element (spectral
  Laplace comparison), together with the canonical-shell boundary-value limit
  into those same witness values;
- the concrete Section-4.3 / Lemma-4.2 adapter
  `lemma42_matrix_element_time_interchange` and the transformed-image kernel
  theorem `bvt_W_matrixElement_onImage` remain the public theorem slots that
  consume that witness, not the immediate next step from slice descent alone;
- `lemma42_matrix_element_time_interchange` is now present in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean)
  on the honest witness-consuming surface: it already turns the positive-
  imaginary-axis witness identification plus the canonical-shell limit theorem
  into the desired per-pair kernel equality, so the remaining exposed blocker
  is exactly the proof of those witness/limit hypotheses rather than another
  hidden reduction layer.

/-- Concrete Section-4.3 / Lemma-4.2 adapter: this theorem is now landed on the
current honest theorem surface. It consumes:
- an upper-half-plane witness `H`,
- identification of `H` with the semigroup-side holomorphic matrix element on
  the positive imaginary axis,
- and the canonical-shell boundary-value limit into those same witness values.

What remains is to prove those hypotheses from the spatial-Fourier / Section-8
machinery, not to invent another reduction theorem. -/
theorem lemma42_matrix_element_time_interchange
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (H : ℂ → ℂ)
    ... :
    ... := by
  -- implemented in `OSToWightmanPositivity.lean`

/-- Stage-5 prerequisite: expose the OS-II `bvt_W` quadratic form on
transformed-image inputs in the same iterated Fourier-Laplace coordinates used
by `section43_iteratedSlice_descendedPairing`, now consuming the concrete
adapter `lemma42_matrix_element_time_interchange`. -/
theorem bvt_W_matrixElement_onImage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d)
    {n m : ℕ}
    (hn : n ≤ F.toBorchers.bound)
    (hm : m ≤ F.toBorchers.bound) :
    ... := by
  ...

/-- OS I Eq. (4.28) on the transformed-image core. -/
theorem bvt_wightmanInner_eq_transport_norm_sq_onImage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re =
      ‖bvt_transport_to_osHilbert_onImage (d := d) OS F‖ ^ 2

/-- Final public theorem-3 closure from the transformed image core. The closure
step uses density in the Hilbert space `H`, not a Schwartz-space density
theorem. -/
theorem bvt_W_positive_of_transportImage_density
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re
```

### 5.9.0. Codomain decision: Option beta

For theorem 3, the codomain choice is now fixed:

1. the paper's Lemma 4.1 codomain is `L(R_+^{4n})`, the half-space Schwartz
   space;
2. the blueprint therefore fixes **Option beta**:
   `Section43PositiveEnergyComponent d n` is a quotient-model realization of
   that half-space Schwartz target;
3. the full-Schwartz / internal-Seeley-extension route from Iteration B is
   retracted and should not be implemented;
4. any later equivalent coding of this codomain must remain definitionally
   about functions on the half-space, not about a fixed extension to all of
   `ℝ^{4n}`.

Proof transcript:

1. define the degreewise transformed image `bvtTransportImage` exactly as in OS
   I Lemma 4.1, i.e. literally as the range of
   `os1TransportComponent d n`;
2. do **not** implement `os1TransportComponent` as the naive unrestricted
   real-axis Laplace integral by itself; the paper route factors through the
   intermediate `(4.19)` space and Lemma 8.2, and that is exactly what keeps
   the codomain on the genuine half-space Schwartz theorem surface rather than
   drifting either to a tempered-only theorem surface or to the false
   support-restricted codomain `tsupport ⊆ PositiveEnergyRegion`;
3. derive additive/scalar closure of the image from linearity of
   `os1TransportComponent`;
4. package finite-support sequences in that image as
   `BvtTransportImageSequence d`;
5. define `bvt_transport_to_osHilbert_onImage` by the Section 4.3 preimage map
   followed by the existing OS Hilbert-space construction;
6. prove preimage-independence / well-definedness using the zero-kernel part of
   OS I Lemma 4.1;
7. prove the multivariate iterated-slice descended-pairing theorem that
   identifies the abstract quotient-valued transform with the concrete
   iterated `partialFourierSpatial_fun` / Fourier-Laplace computation;
8. prove the matching `bvt_W` matrix-element bridge on transformed-image
   inputs, in the same iterated coordinates;
9. prove `bvt_wightmanInner_eq_transport_norm_sq_onImage` by matching the
   Wightman and transport double sums termwise through those two Stage-5
   prerequisites;
10. use the already-built density of positive-time vectors in `OSHilbertSpace OS`
   coming from the completion/GNS construction, not a separate density theorem
   in Schwartz space;
11. extend positivity from the transported image to arbitrary public
   `BorchersSequence d` by the resulting Hilbert-space closure plus continuity
   of `bvt_W`.

This package is the actual theorem-3 closure target.

2026-04-14 transform-surface correction:

The codomain decision above remains correct, but older uses of
`os1TransportComponent` in this subsection must not be read as describing the
current production definition.  At present,

```lean
os1TransportComponent d n f =
  section43PositiveEnergyQuotientMap (d := d) n f.1
```

so its range is only the quotient image of positive-time Euclidean tests.  It
is not the OS I `(4.19)-(4.20)` Fourier-Laplace transformed image.  Therefore
the actual implementation target for this section is

```lean
section43FourierLaplaceTransformComponent
```

or an explicitly renamed/replaced `os1TransportComponent` whose apply theorem
unfolds to the `(4.19)-(4.20)` difference-coordinate spatial-Fourier/time-
Laplace integral.  Until such a map exists, `bvtTransportImage` in production
is only a quotient-image carrier and cannot be used as the transformed image
needed in Eq. `(4.28)`.

Concrete replacement for the proof transcript above:

1. define the degreewise transformed image as the range of
   `section43FourierLaplaceTransformComponent`, not the current
   quotient-inclusion `os1TransportComponent`;
2. prove additive/scalar closure from linearity of that explicit transform;
3. package finite-support sequences in that transformed image;
4. define the Hilbert transport using positive-time preimages through the
   actual transform map;
5. prove preimage-independence by the kernel-zero theorem for the actual
   `(4.19)-(4.20)` transform, not by injectivity of the current quotient
   inclusion alone;
6. only then state the matrix-element bridge and Eq. `(4.28)` on this
   transformed-image core.

OS I / OS II dependency note:

1. in the original paper, Eqs. (4.24)-(4.28) consume the distribution
   `\tilde W` from Eq. (4.12), so Section 4.3 is not literally independent of
   Lemma 8.8;
2. the production route must not rely on the broken OS I Lemma 8.8 itself;
3. instead, the Wightman-side kernel is supplied by the already-repaired OS II
   `bvt_F` / `bvt_W` construction built from `OSLinearGrowthCondition`;
4. the explicit Fourier-Laplace integral `(4.19)-(4.20)` still governs the
   **test-function transport** on the Section-4.3 side.

### 5.9.1. Detailed proof of the replacement Fourier-Laplace component

The production definition currently named

`os1TransportComponent :
  EuclideanPositiveTimeComponent d n ->L[ℂ] Section43PositiveEnergyComponent d n`

does **not** follow the Section-4.3 paper route: it is quotient inclusion of
the underlying Euclidean test.  The proof target in this subsection is
therefore the replacement component

```lean
section43FourierLaplaceTransformComponent
```

or a deliberate refactor of `os1TransportComponent` to that meaning.  The
replacement must follow the Section-4.3 paper route exactly.

Input:
- `f ∈ S_+(ℝ^{(d+1)n})`, i.e. a Schwartz test function supported in ordered
  positive Euclidean times.

Output:
- an element of the corrected Section-4.3 positive-energy codomain, i.e. the
  half-space Schwartz object determined by the Fourier-Laplace transform.

The proof must be decomposed into the following local steps.

1. Separate spatial and time transforms.
   - first apply the ordinary Schwartz Fourier transform in the spatial
     variables;
   - then apply the one-sided Laplace transform in each Euclidean time
     variable, with the sign convention of OS I `(4.19)`-`(4.20)`;
   - only after those one-variable time transforms are assembled may one regard
     the result as a function of full momentum variables `q_k = (q_k^0, q⃗_k)`.

2. Factor the implementation through a degreewise one-variable supplier.
   The production file should not define `os1TransportComponent` directly by one
   giant `n`-variable integral. The correct local supplier package is:

   ```lean
   noncomputable def os1TransportOneVar
       : EuclideanPositiveTimeTest1D →L[ℂ] Section43PositiveEnergy1D

   theorem os1TransportOneVar_restrict_Ici_eq
       (f : EuclideanPositiveTimeTest1D) :
       ...

   theorem os1TransportOneVar_injective :
       Function.Injective os1TransportOneVar

    theorem not_denseRange_os1TransportOneVar :
        ¬ DenseRange os1TransportOneVar

    theorem denseRange_section43PositiveEnergyQuotientMap1D :
        DenseRange section43PositiveEnergyQuotientMap1D
   ```

3. The exact analytic suppliers for that one-variable package are:
   - `SCV.fourierLaplaceExt`,
   - `SCV.paley_wiener_half_line`,
   - `SchwartzMap.fourierTransformCLM`,
   - the fact that Fourier transform is an automorphism of Schwartz space.

4. The mathematical use of those suppliers is:
   - the positive-time support of the Euclidean input gives one-sided Fourier
     support for the relevant time-distribution slices;
   - `SCV.paley_wiener_half_line` gives the corresponding upper-half-plane
     Fourier-Laplace representation;
   - the half-line Paley-Wiener theorem identifies the resulting object with a
     point in the corrected Section-4.3 codomain;
   - the boundary-value uniqueness part of that theorem gives the kernel-zero
     statement after restricting back to the half-line;
   - Fourier automorphism of Schwartz keeps the target on the half-space
     Schwartz side rather than only a tempered-distribution target.

5. The concrete current-code branch `3b` should be built through a companion
   support file, not monolithically inside the frontier theorem file.
   The intended support chain is:
   - `OSReconstruction/SCV/PartialFourierSpatial.lean`,
   - `nPointTimeSpatialCLE`,
   - `partialFourierSpatial_fun`,
   - differentiation-under-the-integral and seminorm bounds there,
   - then the resulting CLM imported back into `OSToWightmanPositivity.lean`.

6. Step 1 of that branch-`3b` implementation must keep the paper's transform
   explicit: `(4.19)`-`(4.20)` define `\check f` by a concrete
   Fourier-Laplace integral on test functions. It is **not** a spectral-measure
   definition.

7. Assemble the degree-`n` map by repeated one-variable transforms.
   - the production proof should introduce a theorem saying the full `n`-point
     transform is the iterated composition of the one-variable operator in each
     time coordinate together with the spatial Fourier transform;
   - this is the place where tensor-product / iterated-variable bookkeeping
     belongs;
   - no many-variable Paley-Wiener theorem is used here.

8. Package continuity and codomain characterization only after the iterated
   formula is proved.
   - continuity is obtained because each elementary one-variable transform is a
     continuous linear map on the chosen Schwartz model;
   - the essential codomain theorem is that the resulting element of the
     corrected Section-4.3 codomain agrees with the Fourier-Laplace transform
     prescribed by Section 4.3;
   - the final CLM to that codomain is defined only after those two facts are
     in place.

The implementation should therefore introduce the following local theorem slots
before the final replacement `def` is closed:

```lean
theorem section43FourierLaplaceTransformComponent_eq_iterated_oneVar
    (f : EuclideanPositiveTimeComponent d n) :
    ...

theorem section43FourierLaplaceTransformComponent_restrict_positiveEnergy
    (f : EuclideanPositiveTimeComponent d n) :
    ...

theorem section43FourierLaplaceTransformComponent_continuous :
    Continuous (section43FourierLaplaceTransformComponent d n)
```

### 5.9.1a. Implementation packet for the replacement transform

This subsection is the next proof-doc target before any production Lean proof
body is reopened.  The goal is to expose the exact OS I `(4.19)-(4.20)`
transform in a theorem surface that cannot be discharged by the current
quotient-inclusion map.

Recommended support-file target:

```lean
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean
```

Production status, 2026-04-14: this file now exists and

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean
```

terminated with exit code `0`.  It contains the compiled first packet:
`section43DiffCoordRealCLE`, `section43DiffPullbackCLM`,
`tsupport_section43DiffPullback_subset_positiveOrthant`,
`section43QTime`, `section43QSpatial`, and
`section43FourierLaplaceIntegral`.  The same exact file check was rerun after
adding
`nPointTimeSpatialSchwartzCLE_section43DiffPullbackCLM_apply` and
`section43FourierLaplaceIntegral_eq_time_spatial_integral`, rerun after adding
`section43TimeSplitCLE` and its simp lemmas, and rerun after adding the
`piFinSuccAbove`-based Fubini bridge `integral_section43TimeSplit`; all later
checks terminated with exit code `0`.

This avoids further enlarging `OSToWightmanPositivity.lean` while the transform
infrastructure is still being built.  The file should import
`EuclideanPositiveTime`, `Section43Codomain`, `SCV/PartialFourierSpatial`, and
`ComplexLieGroups/DifferenceCoordinatesReduced`; it should not import the
theorem-3 positivity frontier.

First local coordinate packet:

```lean
noncomputable abbrev section43DiffCoordRealCLE (d n : ℕ) :
    NPointDomain d n ≃L[ℝ] NPointDomain d n :=
  BHW.realDiffCoordCLE n d

@[simp] theorem section43DiffCoordRealCLE_apply
    (x : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    section43DiffCoordRealCLE d n x k μ =
      if hk : k.val = 0 then x k μ
      else x k μ - x ⟨k.val - 1, by omega⟩ μ

@[simp] theorem section43DiffCoordRealCLE_symm_apply
    (ξ : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    (section43DiffCoordRealCLE d n).symm ξ k μ =
      ∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ
```

Proof transcript:

1. Do not duplicate the difference-coordinate algebra.  Production already has
   the real finite-dimensional equivalence
   `BHW.realDiffCoordCLE n d : (Fin n → Fin (d + 1) → ℝ) ≃L[ℝ]
   (Fin n → Fin (d + 1) → ℝ)`, and `NPointDomain d n` unfolds to that type.
   The two `[simp]` lemmas are direct `simpa [section43DiffCoordRealCLE]`
   consequences of `BHW.realDiffCoordCLE_apply` and
   `BHW.realDiffCoordCLE_symm_apply`.
2. Prove the ordered-support transport theorem:

```lean
theorem tsupport_section43DiffPullback_subset_positiveOrthant
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    tsupport
      ((SchwartzMap.compCLMOfContinuousLinearEquiv
          (section43DiffCoordRealCLE d n).symm f.1 :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)
      ⊆ section43PositiveEnergyRegion d n
```

   This is the Lean form of OS I `(4.19)`: ordered times for `f` become
   nonnegative time differences for `f^+`.
3. The proof should first use the standard support-preimage lemma for
   precomposition by a homeomorphism/continuous map, reducing
   `ξ ∈ tsupport (f.1 ∘ (section43DiffCoordRealCLE d n).symm)` to
   `(section43DiffCoordRealCLE d n).symm ξ ∈ tsupport f.1`.  Then apply `f.2`
   to obtain ordered positive times for the partial sums.
4. Componentwise closure: for each `k`, the time coordinate of
   `(section43DiffCoordRealCLE d n).symm ξ` at `k` is
   `∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ 0`.  Ordered positivity of
   these partial sums implies `0 ≤ ξ k 0`: for `k = 0` this is the first
   partial sum; for `k > 0` it is the difference between consecutive strictly
   increasing partial sums.  This closes membership in
   `section43PositiveEnergyRegion d n`.

Second local transform packet:

```lean
noncomputable def section43DiffPullbackCLM (d n : ℕ) [NeZero d] :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ] SchwartzNPoint d n
```

Apply theorem:

```lean
@[simp] theorem section43DiffPullbackCLM_apply
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (ξ : NPointDomain d n) :
    section43DiffPullbackCLM d n f ξ =
      f.1 ((section43DiffCoordRealCLE d n).symm ξ)
```

This theorem must be a direct application of `SchwartzMap.compCLMOfContinuousLinearEquiv`;
it must not mention `bvt_W`, `OS.S`, or `os1TransportComponent`.

Third local transform packet:

Let

```lean
def qTime (q : NPointDomain d n) : Fin n → ℝ :=
  (nPointTimeSpatialCLE (d := d) n q).1

def qSpatial (q : NPointDomain d n) :
    EuclideanSpace ℝ (Fin n × Fin d) :=
  (nPointTimeSpatialCLE (d := d) n q).2
```

The scalar transform formula to expose is:

```lean
noncomputable def section43FourierLaplaceIntegral
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n) : ℂ :=
  ∫ τ : Fin n → ℝ,
    Complex.exp (-(∑ k : Fin n, (τ k : ℂ) * (qTime (d := d) (n := n) q k : ℂ))) *
      OSReconstruction.partialFourierSpatial_fun
        (d := d) (n := n) (section43DiffPullbackCLM d n f)
        (τ, qSpatial (d := d) (n := n) q)
```

This is the Lean-facing version of OS I `(4.20)`.  The spatial Fourier sign
and `2π` normalization are inherited entirely from
`partialFourierSpatial_fun_eq_integral`; do not rewrite them by hand in this
theorem.  The time factor is the decaying Laplace sign from the scanned OS I
formula:

```text
exp(-Σ_k (ξ_k^0 q_k^0 - i ξ_k^sp · q_k^sp)).
```

Fourth local codomain packet:

To define a continuous linear map into the current quotient-model codomain,
do **not** use arbitrary `Classical.choose` representatives.  One of the
following must be implemented.

Option A, preferred for production:

```lean
noncomputable def section43FourierLaplaceRepresentativeCLM
    (d n : ℕ) [NeZero d] :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ] SchwartzNPoint d n

theorem section43FourierLaplaceRepresentativeCLM_eq_integral_on_positiveEnergy
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    Set.EqOn
      ((section43FourierLaplaceRepresentativeCLM d n f :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)
      (section43FourierLaplaceIntegral (d := d) (n := n) f)
      (section43PositiveEnergyRegion d n)

noncomputable def section43FourierLaplaceTransformComponent
    (d n : ℕ) [NeZero d] :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ]
      Section43PositiveEnergyComponent (d := d) n :=
  (section43PositiveEnergyQuotientMap (d := d) n).comp
    (section43FourierLaplaceRepresentativeCLM d n)
```

Hidden obligation in Option A: the representative CLM is the place where the
half-space Schwartz codomain is represented in the quotient model.  Its proof
must supply a continuous linear representative/extension mechanism for the
OS I `(4.20)` half-space Schwartz function.  If that mechanism is not ready,
do not fake it with a non-linear choice.

Option B, acceptable as the next smaller Lean step:

Prove only the scalar apply theorem needed by the common normal form, without
defining the quotient-level component yet:

```lean
theorem section43FourierLaplaceIntegral_slice_normalForm
    -- fixed `f`, chosen slice coordinate, frozen nonnegative background times,
    -- and spatial momentum variables
    :
    -- the slice appearing in the OS I `(4.23)` expansion
    -- equals the one-variable `complexLaplaceTransform` /
    -- `partialFourierSpatial_timeSliceCanonicalExtension` expression
```

Option B must still expose the same `section43DiffPullbackCLM` and
`section43FourierLaplaceIntegral`; it simply postpones the quotient-level
representative CLM.  It is the right immediate target if the full half-space
representative theorem is too large.

Option choice after the first support-file implementation, 2026-04-14:

Option B is the immediate route.  Option A remains mathematically desirable,
but its hidden obligation is a genuine half-space-to-Schwartz representative
theorem for `(4.20)`, including continuity of the representative map.  That is
larger than the current blocker.  Option B instead keeps the already compiled
scalar function

```lean
section43FourierLaplaceIntegral
```

and proves only the scalar normal forms needed by the hPsi/shell suppliers.

The first Option-B theorem is now implemented:

```lean
theorem section43FourierLaplaceIntegral_eq_time_spatial_integral
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n) :
    section43FourierLaplaceIntegral d n f q =
      ∫ τ : Fin n → ℝ,
        Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
          (∫ η : EuclideanSpace ℝ (Fin n × Fin d),
            𝐞 (-(inner ℝ η (section43QSpatial (d := d) (n := n) q))) •
              nPointTimeSpatialSchwartzCLE (d := d) (n := n)
                (section43DiffPullbackCLM d n f) (τ, η))
```

Its proof is a one-line expansion by `partialFourierSpatial_fun_eq_integral`,
and the exact support-file check after adding it terminated with exit code `0`.

The next Option-B theorem was made Lean-ready and implemented.  The first
missing proof-doc item was the time-coordinate split/Fubini bridge that turns
the outer integral over `τ : Fin n → ℝ` into an iterated integral in one chosen
coordinate `r`; that measure layer now compiles:

```lean
noncomputable def section43TimeSplitCLE (r : Fin n) :
    (Fin n → ℝ) ≃L[ℝ] ℝ × ({i : Fin n // i ≠ r} → ℝ)

@[simp] theorem section43TimeSplitCLE_apply
    (τ : Fin n → ℝ) :
    section43TimeSplitCLE r τ =
      (τ r, fun i : {i : Fin n // i ≠ r} => τ i.1)

@[simp] theorem section43TimeSplitCLE_symm_apply_self
    (s : ℝ) (τbg : {i : Fin n // i ≠ r} → ℝ) :
    (section43TimeSplitCLE r).symm (s, τbg) r = s

@[simp] theorem section43TimeSplitCLE_symm_apply_ne
    (s : ℝ) (τbg : {i : Fin n // i ≠ r} → ℝ)
    (i : Fin n) (hi : i ≠ r) :
    (section43TimeSplitCLE r).symm (s, τbg) i = τbg ⟨i, hi⟩
```

Production status: this algebraic split equivalence and the three apply/symm
simp lemmas now compile in `Section43FourierLaplaceTransform.lean`.  The
measure/Fubini obligation is also compiled in the orientation supported
directly by Mathlib:

```lean
noncomputable abbrev section43TimeSplitMeasurableEquiv {n : ℕ}
    (r : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ)

theorem integral_section43TimeSplit
    {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Fin (n + 1))
    (G : (Fin (n + 1) → ℝ) → E)
    (hG : Integrable G (volume : Measure (Fin (n + 1) → ℝ))) :
    ∫ τ : Fin (n + 1) → ℝ, G τ =
      ∫ τbg : Fin n → ℝ, ∫ s : ℝ,
        G ((section43TimeSplitMeasurableEquiv r).symm (s, τbg))
```

The proof uses `MeasureTheory.volume_preserving_piFinSuccAbove`,
`MeasurePreserving.integral_comp'`, `MeasurePreserving.integrable_comp_of_integrable`,
`MeasureTheory.integral_prod`, and `MeasureTheory.integral_prod_symm`.  Thus
the change-of-variables/Fubini layer is no longer a blocker.

With the split theorem available, the next scalar theorem is also implemented:

```lean
theorem section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplace
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hInt : Integrable
      (fun τ : Fin (n + 1) → ℝ =>
        Complex.exp
          (-(∑ k : Fin (n + 1),
            (τ k : ℂ) * (section43QTime (d := d) (n := n + 1) q k : ℂ))) *
        partialFourierSpatial_fun
          (d := d) (n := n + 1) (section43DiffPullbackCLM d (n + 1) f)
          (τ, section43QSpatial (d := d) (n := n + 1) q))) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        (∫ s : ℝ,
          Complex.exp
            (-(s : ℂ) * (section43QTime (d := d) (n := n + 1) q r : ℂ)) *
          partialFourierSpatial_fun
            (d := d) (n := n + 1) (section43DiffPullbackCLM d (n + 1) f)
            ((section43TimeSplitMeasurableEquiv r).symm (s, τbg),
              section43QSpatial (d := d) (n := n + 1) q))
```

Proof transcript, now tested against Lean:

1. Unfold only `section43FourierLaplaceIntegral`.
2. Apply `integral_section43TimeSplit r` to the displayed integrand, using
   `hInt` as the integrability input.
3. The result has the inner integral in the correct `s` variable and the
   background variable `τbg : Fin n → ℝ`.
4. Prove the exponential factorization
   `exp (-(Σ_all ...)) =
    exp (-(s * q_r)) * exp (-(Σ_bg ...))` by `Fin.sum_univ_succAbove`,
   the simp theorem for `MeasurableEquiv.piFinSuccAbove_symm_apply`, and
   `Complex.exp_add`.
5. Move the background factor outside the inner `s` integral using
   `MeasureTheory.integral_const_mul` or `integral_mul_const` in the exact
   orientation Lean exposes.
6. Close by `ring_nf`/`simp` on the time-split apply theorems.

Production status, 2026-04-14: the theorem
`section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplace` compiles in
`Section43FourierLaplaceTransform.lean`, and the exact check

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean
```

terminated with exit code `0` after this theorem was added.

The earlier remaining proof-doc gap for this scalar packet is now closed in
production: the integrability input `hInt` for the `(4.20)` time integrand is
proved on the honest positive-energy surface.  The coordinate split, Fubini
step, exponential factorization, constant-pullout, support restriction,
exponential bound, and integrability proof are no longer blockers.

Two more local pieces of the integrability proof are now implemented and
checked in `Section43FourierLaplaceTransform.lean`:

```lean
theorem partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_neg
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (τ : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (hτ : ∃ i : Fin n, τ i < 0) :
    partialFourierSpatial_fun
      (d := d) (n := n) (section43DiffPullbackCLM d n f) (τ, ξ) = 0

theorem norm_exp_neg_section43_timePair_le_one
    (q : NPointDomain d n) (τ : Fin n → ℝ)
    (hq : q ∈ section43PositiveEnergyRegion d n)
    (hτ : ∀ i : Fin n, 0 ≤ τ i) :
    ‖Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))‖ ≤ 1
```

The first theorem says the spatial Fourier transform preserves the
positive-difference-time support condition because it only Fourier-transforms
the spatial variables.  The second theorem is the decaying half of OS I
`(4.20)`: on the nonnegative time orthant and positive-energy external
variables, the time exponential has norm at most `1`.

The formerly remaining analytic theorem now has the following compiled shape:

```lean
theorem integrable_section43FourierLaplace_timeIntegrand
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    Integrable
      (fun τ : Fin n → ℝ =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
        partialFourierSpatial_fun
          (d := d) (n := n) (section43DiffPullbackCLM d n f)
          (τ, section43QSpatial (d := d) (n := n) q))
```

Lean proof transcript for this integrability theorem:

1. Prove `Integrable (fun τ => partialFourierSpatial_fun ... (τ, ξ))` for each
   fixed spatial frequency `ξ`.  Use
   `exists_norm_bound_partialFourierSpatial_fun`,
   `exists_timeCoordPow_norm_bound_partialFourierSpatial_fun`, and
   `integrable_of_le_of_pow_mul_le` from Mathlib's temperate-growth package.
2. The only nontrivial estimate inside step 1 is the finite-dimensional norm
   comparison turning the coordinate-power bounds into
   `‖τ‖ ^ volume.integrablePower * ‖partialFourierSpatial_fun ... (τ, ξ)‖ ≤ C`.
   This should be a reusable finite-`Fin` lemma, not buried in the OS theorem.
   The compiled theorem surface is:

```lean
theorem exists_normPow_bound_partialFourierSpatial_timeSlice
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ : Fin n → ℝ,
        ‖τ‖ ^ K *
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C
```

   Proof transcript for this norm-power theorem:

   1. For each coordinate `i : Fin n`, instantiate
      `exists_timeCoordPow_norm_bound_partialFourierSpatial_fun f i K`.
   2. Let `Ccoord i` be the corresponding nonnegative bound, and use
      `C := (∑ i, Ccoord i) + C0`, where `C0` is the global bound from
      `exists_norm_bound_partialFourierSpatial_fun`.  The `+ C0` harmlessly
      covers the empty-index and `K = 0` edge cases.
   3. For a fixed `τ`, if `‖τ‖ = 0` or `K = 0`, close from the global bound.
   4. Otherwise use `Pi.norm_def` and `Finset.exists_mem_eq_sup` on
      `Finset.univ` to choose a coordinate `i` with
      `‖τ‖ = ‖τ i‖`.
   5. Rewrite
      `‖τ‖ ^ K * ‖partialFourierSpatial_fun f (τ, ξ)‖` as
      `‖(((τ i : ℝ) : ℂ) ^ K) *
        partialFourierSpatial_fun f (τ, ξ)‖` using
      `norm_mul`, `norm_pow`, and `Complex.norm_real`.
   6. Apply the chosen coordinate-power bound and then
      `Ccoord i ≤ ∑ j, Ccoord j ≤ C`.

   With that theorem in place, the fixed-spatial-frequency integrability
   theorem is also compiled:

```lean
theorem integrable_partialFourierSpatial_timeSlice
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Integrable
      (fun τ : Fin n → ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ))
```

   Proof transcript:

   1. Use `exists_norm_bound_partialFourierSpatial_fun f` for the first
      hypothesis of `integrable_of_le_of_pow_mul_le`.
   2. Use `exists_normPow_bound_partialFourierSpatial_timeSlice f ξ
      ((volume : Measure (Fin n → ℝ)).integrablePower)` for the second
      hypothesis with `k = 0`.
   3. The AEStronglyMeasurable hypothesis follows from
      `contDiff_partialFourierSpatial_fun_time f ξ`, hence from continuity.
3. Use
   `partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_neg` to
   split pointwise into two cases.  If some `τ i < 0`, the whole integrand is
   zero.  Otherwise all `τ i ≥ 0`.
4. In the nonnegative case, apply
   `norm_exp_neg_section43_timePair_le_one` to bound the exponential norm by
   `1`, so the full integrand is dominated by the integrable partial-spatial
   Fourier time slice.
5. Apply `Integrable.mono` with the continuity/AEStronglyMeasurable facts from
   `contDiff_partialFourierSpatial_fun_time` and `Complex.continuous_exp`.

The support file now also contains the positive-energy consumer theorem
discharging `hInt` in the one-coordinate normal form:

```lean
theorem section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplace_of_mem_positiveEnergy
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1)) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        (∫ s : ℝ,
          Complex.exp
            (-(s : ℂ) * (section43QTime (d := d) (n := n + 1) q r : ℂ)) *
          partialFourierSpatial_fun
            (d := d) (n := n + 1) (section43DiffPullbackCLM d (n + 1) f)
            ((section43TimeSplitMeasurableEquiv r).symm (s, τbg),
              section43QSpatial (d := d) (n := n + 1) q))
```

Exact check after adding the norm-power, time-slice integrability, full
`(4.20)` integrability, and positive-energy iterated-normal-form theorem:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean
```

Result: exit code `0`.

Next Option-B bridge, now Lean-ready:

The compiled theorem
`section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplace_of_mem_positiveEnergy`
uses Mathlib's `piFinSuccAbove` coordinate split.  The older one-variable
Section-4.3 slice API in `OSToWightmanPositivity.lean` is written with
`Function.update t r s`.  Before moving or reusing that slice API, the support
file should expose the exact coordinate identification:

```lean
@[simp] theorem section43TimeSplitMeasurableEquiv_symm_eq_update_zero
    {n : ℕ} (r : Fin (n + 1))
    (s : ℝ) (τbg : Fin n → ℝ) :
    (section43TimeSplitMeasurableEquiv r).symm (s, τbg) =
      Function.update
        ((section43TimeSplitMeasurableEquiv r).symm (0, τbg)) r s
```

Proof transcript:

1. `ext k`.
2. Split on `k = r`.
3. The `k = r` case is the distinguished-coordinate simp theorem for
   `MeasurableEquiv.piFinSuccAbove_symm_apply`.
4. The `k != r` case is the same simp theorem plus `Function.update_noteq`.

Then define the raw one-coordinate Laplace scalar attached to a multivariate
partial-spatial Fourier slice:

```lean
noncomputable def section43OneCoordinateLaplaceIntegral
    {n : ℕ}
    (F : SchwartzNPoint d (n + 1))
    (r : Fin (n + 1))
    (t : Fin (n + 1) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin (n + 1) × Fin d))
    (σ : ℝ) : ℂ :=
  ∫ s : ℝ,
    Complex.exp (-(s : ℂ) * (σ : ℂ)) *
      partialFourierSpatial_fun (d := d) (n := n + 1) F
        (Function.update t r s, ξ)
```

This definition is not a replacement route.  It is the explicit scalar bridge
between the already compiled OS I `(4.20)` integral and the existing
one-variable slice package.  It must not mention `bvt_W`, `OS.S`,
`os1TransportComponent`, or any quotient representative.

The immediate consumer theorem should be:

```lean
theorem section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplaceIntegral_of_mem_positiveEnergy
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1)) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        section43OneCoordinateLaplaceIntegral
          (d := d) (n := n)
          (section43DiffPullbackCLM d (n + 1) f)
          r
          ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
          (section43QSpatial (d := d) (n := n + 1) q)
          (section43QTime (d := d) (n := n + 1) q r)
```

Proof transcript:

1. Rewrite by
   `section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplace_of_mem_positiveEnergy`.
2. Apply `MeasureTheory.integral_congr_ae`; fix `τbg`.
3. Unfold `section43OneCoordinateLaplaceIntegral`.
4. Apply `MeasureTheory.integral_congr_ae`; fix `s`.
5. Rewrite the time vector with
   `section43TimeSplitMeasurableEquiv_symm_eq_update_zero`.
6. Close by `rfl`/`simp`.

Production status, 2026-04-14: the coordinate identity,
`section43OneCoordinateLaplaceIntegral`, and the positive-energy consumer
theorem above are implemented in
`Section43FourierLaplaceTransform.lean`.  The exact check

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean
```

terminated with exit code `0` after these declarations were added.

This is the last purely coordinate-level scalar bridge before deciding whether
to move the one-variable slice package out of `OSToWightmanPositivity.lean`.
After it compiles, the next proof-doc item is the extraction plan for the
following already existing private pure helpers:

```lean
partialFourierSpatial_timeSliceSchwartz
complexLaplaceTransform
fourierInvPairingCLM
fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform
partialFourierSpatial_timeSliceCanonicalExtension_eq_complexLaplaceTransform
partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ
```

Extraction rule: move or duplicate only the pure Section-4.3 one-variable
slice support.  Do not move any theorem whose proof or statement uses
`os1TransportComponent`, `bvt_W`, `bvt_F`, `OS.S`, shell limits, or
semigroup matrix elements.

Implementation-ready extraction plan for the one-variable slice packet:

Do not put the next packet into `OSToWightmanPositivity.lean`.  The pure slice
machinery is currently stranded there, but the destination should be a small
support module:

```lean
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
```

Recommended imports:

```lean
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
```

Use new public names with a `section43` prefix, because
`OSToWightmanPositivity.lean` already has an unprefixed public
`partialFourierSpatial_timeSliceSchwartz` declaration.  The support module may
copy the proven pure arguments under the new names first; once the transformed
route consumes them, the old stranded declarations can be removed or rewritten
as local aliases in a separate cleanup.  This avoids a large same-name import
conflict during the proof-critical move.

Packet A: the slice-as-Schwartz package.

Public declarations to implement:

```lean
theorem section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (η : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    nPointTimeSpatialSchwartzCLE (d := d) (n := n) f.1
      (Function.update t r s, η) = 0

theorem section43PartialFourierSpatial_fun_eq_zero_of_neg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    partialFourierSpatial_fun (d := d) (n := n) f.1
      (Function.update t r s, ξ) = 0

theorem section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    tsupport (fun s : ℝ =>
      partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)) ⊆ Set.Ici 0

noncomputable def section43TimeDerivTransportInput
    {n : ℕ} (r : Fin n) (f : SchwartzNPoint d n) :
    SchwartzNPoint d n

noncomputable def section43IteratedTimeDerivTransport
    {n : ℕ} (r : Fin n) (m : ℕ) (f : SchwartzNPoint d n) :
    SchwartzNPoint d n

theorem section43IteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
    {n : ℕ}
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ∀ (m : ℕ) (f : SchwartzNPoint d n) (s : ℝ),
      iteratedDeriv m
        (fun u : ℝ =>
          partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        s =
      partialFourierSpatial_fun (d := d) (n := n)
        (section43IteratedTimeDerivTransport (d := d) (n := n) r m f)
        (Function.update t r s, ξ)

theorem section43ContDiff_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r s, ξ))

noncomputable def section43PartialFourierSpatialTimeSliceSchwartz
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    SchwartzMap ℝ ℂ
```

Proof transcript for Packet A:

1. Port the existing proofs from `OSToWightmanPositivity.lean` lines
   416-843 under the new names, but keep only the pure statements above.
2. For negative support, use the ordered-support hypothesis on
   `EuclideanPositiveTimeComponent`; no Wightman, OS, or quotient theorem is
   involved.
3. For smoothness and decay, use the already imported
   `partialFourierSpatial_fun` derivative and coordinate-power estimates:
   `differentiableAt_partialFourierSpatial_fun_time`,
   `fderiv_partialFourierSpatial_fun_time_apply_eq_transport`, and
   `exists_timeCoordPow_norm_bound_partialFourierSpatial_fun`.
4. Package the final `SchwartzMap` exactly as the old theorem does: the
   `smooth'` field is `section43ContDiff_partialFourierSpatial_timeSlice`;
   the `decay'` field uses
   `section43IteratedDeriv_partialFourierSpatial_timeSlice_eq_transport` and
   `norm_iteratedFDeriv_eq_norm_iteratedDeriv`.

Production status, 2026-04-14: Packet A is implemented in
`Section43OneVariableSlice.lean` under the `section43`-prefixed names above.
Both checks have terminated successfully:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice
```

The module contains no `sorry`, no `axiom`, no `set_option maxHeartbeats 0`,
and no mentions of `bvt_W`, `bvt_F`, `OS.S`, `OSHilbert`,
`OSInnerProduct`, or `os1TransportComponent`.

Packet B: the raw Laplace and one-sided Fourier pairing package.

Public declarations to implement:

```lean
noncomputable def section43ComplexLaplaceTransform
    (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * f t

theorem section43ComplexLaplaceTransform_integrable_of_nonneg_re
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (s : ℂ) (hs : 0 ≤ s.re) :
    Integrable (fun t : ℝ =>
      Complex.exp (-s * (t : ℂ)) * f t)

noncomputable def section43FourierInvPairingCLM
    (f : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ

theorem section43FourierInvPairing_hasOneSidedFourierSupport
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    SCV.HasOneSidedFourierSupport
      (section43FourierInvPairingCLM f)

theorem section43ComplexLaplaceTransform_hasPaleyWienerExtension
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    ∃ F_ext : ℂ → ℂ,
      DifferentiableOn ℂ F_ext SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine
          (fun x => F_ext (↑x + ↑η * Complex.I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Tendsto
          (fun η : ℝ =>
            ∫ x : ℝ, F_ext (↑x + ↑η * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ t : ℝ, FourierTransform.fourierInv f t * φ t)))
```

Private declarations inside Packet B may keep their existing role:
`section43WeightedNegCoordPowSchwartz`,
`section43IteratedDerivSchwartz`, the Laplace-kernel derivative estimates,
and the rapid-decay/tendsto-at-zero lemmas.  They are implementation details
unless a later public theorem needs them.

Proof transcript for Packet B:

1. Port the existing pure proofs from `OSToWightmanPositivity.lean` lines
   849-1562 under `section43`-prefixed names.
2. The Paley-Wiener supplier should finish exactly by
   `SCV.paley_wiener_half_line` applied to
   `section43FourierInvPairingCLM f` and
   `section43FourierInvPairing_hasOneSidedFourierSupport f hf_supp`.
3. The positive-imaginary-axis computation should remain a theorem internal to
   Packet C unless a public consumer needs the raw `SCV.fourierLaplaceExt`
   equality.

Production status, 2026-04-14: the raw one-sided Fourier/Laplace packet is
implemented in `Section43OneVariableSlice.lean` under `section43` names:

```lean
section43ComplexLaplaceTransform_integrable_of_nonneg_re
section43FourierInvPairingCLM
section43FourierInvPairingCLM_apply
section43FourierInvPairing_hasOneSidedFourierSupport
section43FourierInvPairing_annihilates_FT_of_negSupport_product
section43FourierInvPairingCLM_partialFourierSpatial_timeSlice_annihilates_FT_of_negSupport_product
section43ComplexLaplaceTransform_hasPaleyWienerExtension
section43FourierLaplaceExt_fourierInvPairing_eq_complexLaplaceTransform
section43PartialFourierSpatial_timeSlice_hasPaleyWienerExtension
```

The implementation is still pure Section 4.3 support: it mentions neither
Wightman boundary values nor OS Hilbert-space objects.  The exact check

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
```

terminated with exit code `0` and no warnings after this packet was added.

Packet C: connection from the new `(4.20)` scalar to the one-variable package.

Public declarations to implement after Packets A and B:

```lean
theorem section43OneCoordinateLaplaceIntegral_eq_complexLaplaceTransform
    {n : ℕ}
    (F : SchwartzNPoint d (n + 1))
    (r : Fin (n + 1))
    (t : Fin (n + 1) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin (n + 1) × Fin d))
    (σ : ℝ) :
    section43OneCoordinateLaplaceIntegral (d := d) (n := n)
        F r t ξ σ =
      section43ComplexLaplaceTransform
        (section43PartialFourierSpatialTimeSliceSchwartz
          (d := d) (n := n + 1) F r t ξ)
        (σ : ℂ)

theorem section43FourierLaplaceIntegral_eq_iterated_complexLaplaceTransform_of_mem_positiveEnergy
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1)) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime
                  (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        section43ComplexLaplaceTransform
          (section43PartialFourierSpatialTimeSliceSchwartz
            (d := d) (n := n + 1)
            (section43DiffPullbackCLM d (n + 1) f)
            r
            ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
            (section43QSpatial (d := d) (n := n + 1) q))
          (section43QTime (d := d) (n := n + 1) q r : ℂ)
```

Proof transcript for Packet C:

1. The first theorem is by unfolding
   `section43OneCoordinateLaplaceIntegral`,
   `section43ComplexLaplaceTransform`, and
   `section43PartialFourierSpatialTimeSliceSchwartz`; then `rfl`.
2. The second theorem rewrites by
   `section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplaceIntegral_of_mem_positiveEnergy`,
   applies `MeasureTheory.integral_congr_ae`, and uses the first theorem.
3. No quotient theorem is used in Packet C.

Production status, 2026-04-14: Packet C is implemented in
`Section43OneVariableSlice.lean`:

```lean
section43OneCoordinateLaplaceIntegral_eq_complexLaplaceTransform
section43FourierLaplaceIntegral_eq_iterated_complexLaplaceTransform_of_mem_positiveEnergy
```

These theorems connect the compiled OS I `(4.20)` scalar normal form to the
one-variable Laplace package without using any quotient, shell, Wightman, or OS
inner-product theorem.

Packet D: canonical upper-half-plane slice extension and descended pairing.

Public declarations to implement only after Packet C compiles:

```lean
noncomputable def section43PartialFourierSpatialTimeSliceCanonicalExtension
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (w : ℂ) : ℂ

theorem section43PartialFourierSpatialTimeSliceCanonicalExtension_eq_complexLaplaceTransform
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    section43PartialFourierSpatialTimeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ (η * Complex.I)
      =
    section43ComplexLaplaceTransform
      (section43PartialFourierSpatialTimeSliceSchwartz
        (d := d) (n := n) f.1 r t ξ)
      ((2 * Real.pi * η : ℂ))

theorem section43PartialFourierSpatialTimeSliceCanonicalExtension_imagAxis_eq_descendedPsiZ
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    section43PartialFourierSpatialTimeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ (η * Complex.I) =
      fourierPairingDescendsToSection43PositiveEnergy1D
        (section43FourierInvPairingCLM
          (section43PartialFourierSpatialTimeSliceSchwartz
            (d := d) (n := n) f.1 r t ξ))
        (section43FourierInvPairing_hasOneSidedFourierSupport
          (section43PartialFourierSpatialTimeSliceSchwartz
            (d := d) (n := n) f.1 r t ξ)
          (section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici
            (d := d) (n := n) f r t ξ))
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη)))
```

Proof transcript for Packet D:

1. Port the existing definition of
   `partialFourierSpatial_timeSliceCanonicalExtension`, replacing
   `fourierInvPairingCLM` and `partialFourierSpatial_timeSliceSchwartz` by the
   new `section43` names.
2. The imaginary-axis Laplace theorem is the existing proof with renamed
   dependencies and the same `2 * Real.pi` scaling.
3. The descended-`ψ_Z` theorem is just the quotient apply theorem
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` plus
   `SCV.fourierLaplaceExt_eq`.
4. This packet may mention `section43PositiveEnergyQuotientMap1D` and
   `fourierPairingDescendsToSection43PositiveEnergy1D`, because these are the
   correct one-variable half-line quotient mechanisms.  It must still not
   mention the multivariate `os1TransportComponent` quotient-inclusion map.

Production status, 2026-04-14: Packet D is implemented through the
descended-`ψ_Z` specialization:

```lean
section43OneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
section43PartialFourierSpatialTimeSliceCanonicalExtension
section43PartialFourierSpatialTimeSliceCanonicalExtension_eq_complexLaplaceTransform
section43PartialFourierSpatialTimeSliceCanonicalExtension_imagAxis_eq_descendedPsiZ
```

The descended theorem is the correct one-variable half-line quotient step.  It
uses `section43PositiveEnergyQuotientMap1D` and
`fourierPairingDescendsToSection43PositiveEnergy1D`; it still does not use the
old multivariate `os1TransportComponent` quotient-inclusion route.

Verification after Packets B/C/D:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice
```

Both terminated successfully; the most recent module build ended with:

```text
✔ [8312/8312] Built OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice (9.9s)
Build completed successfully (8312 jobs).
```

Packet E: analytic regularity of the canonical one-variable slice extension.

Next public declaration:

```lean
theorem section43PartialFourierSpatialTimeSliceCanonicalExtension_differentiableOn
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    DifferentiableOn ℂ
      (section43PartialFourierSpatialTimeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ)
      SCV.upperHalfPlane
```

Proof transcript:

1. Define `T := section43FourierInvPairingCLM
   (section43PartialFourierSpatialTimeSliceSchwartz ... f.1 r t ξ)`.
2. Define `Fcore w := if hw : 0 < w.im then SCV.fourierLaplaceExt T w hw else 0`
   and `F := Fcore ∘ fun w => ((2 * Real.pi : ℂ) * w)`.
3. Prove `F` differentiable on `SCV.upperHalfPlane` by composing
   `SCV.fourierLaplaceExt_differentiableOn T` with scalar multiplication by
   `2 * Real.pi`.  The maps-to proof is `Complex.mul_im` plus
   `mul_pos Real.two_pi_pos`.
4. Prove pointwise equality between
   `section43PartialFourierSpatialTimeSliceCanonicalExtension ...` and `F` by
   splitting on `0 < w.im`; in the positive case use `dif_pos` for both
   unscaled and scaled imaginary parts, and in the nonpositive case derive
   nonpositivity of the scaled imaginary part from `Real.two_pi_pos`.
5. Rewrite by that equality and close with the differentiability of `F`.

This theorem is pure analytic support.  It may mention
`SCV.fourierLaplaceExt` and the one-variable slice functional, but it must not
mention `os1TransportComponent`, `bvt_W`, `bvt_F`, `OS.S`, `OSHilbert`, or
`OSInnerProduct`.

Verification after Packet E:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice
```

Production status, 2026-04-14: Packet E is implemented and verified:

```lean
section43PartialFourierSpatialTimeSliceCanonicalExtension_differentiableOn
```

Both commands above terminated successfully; the latest module build ended
with:

```text
✔ [8312/8312] Built OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice (9.9s)
Build completed successfully (8312 jobs).
```

Packet F: general half-line slice support and canonical-extension bridge for
the OS I `(4.20)` scalar.

Why this packet is necessary:

`section43PartialFourierSpatialTimeSliceCanonicalExtension` is specialized to
`EuclideanPositiveTimeComponent`, but the compiled OS I scalar normal form
contains slices of
`section43DiffPullbackCLM d (n + 1) f`.  That object is an ambient
`SchwartzNPoint` supported on `section43PositiveEnergyRegion`, not an ordered
positive-time component.  The next bridge must therefore be stated for a
general one-variable Schwartz slice with support in `Set.Ici 0`, and only then
specialized to the difference-coordinate pullback.  Do not coerce it through
the old `os1TransportComponent` API.

Public support declarations:

```lean
theorem section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time_of_support_positiveEnergy
    {n : ℕ}
    (F : SchwartzNPoint d n)
    (hF_supp :
      tsupport (F : NPointDomain d n → ℂ) ⊆
        section43PositiveEnergyRegion d n)
    (r : Fin n) (t : Fin n → ℝ)
    (η : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    nPointTimeSpatialSchwartzCLE (d := d) (n := n) F
      (Function.update t r s, η) = 0

theorem section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_support_positiveEnergy
    {n : ℕ}
    (F : SchwartzNPoint d n)
    (hF_supp :
      tsupport (F : NPointDomain d n → ℂ) ⊆
        section43PositiveEnergyRegion d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    tsupport (fun s : ℝ =>
      partialFourierSpatial_fun (d := d) (n := n) F
        (Function.update t r s, ξ)) ⊆ Set.Ici 0

theorem section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
    {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    tsupport (fun s : ℝ =>
      partialFourierSpatial_fun (d := d) (n := n)
        (section43DiffPullbackCLM d n f)
        (Function.update t r s, ξ)) ⊆ Set.Ici 0
```

Proof transcript:

1. The first theorem is the Packet-A negative-time proof with the support
   hypothesis replaced by `hF_supp`.  If the updated time vector has
   distinguished coordinate `s < 0`, its inverse under
   `nPointTimeSpatialCLE` is not in `section43PositiveEnergyRegion`; hence it
   is not in `tsupport F`, so `image_eq_zero_of_notMem_tsupport` applies.
2. The partial-Fourier vanishing theorem is by
   `partialFourierSpatial_fun_eq_integral` and `integral_eq_zero_of_ae`.
3. The `tsupport ... ⊆ Set.Ici 0` theorem repeats the Packet-A neighborhood
   argument around a negative `s`.
4. The difference-pullback corollary is direct from
   `tsupport_section43DiffPullback_subset_positiveOrthant`.

General canonical one-variable extension:

```lean
noncomputable def section43FourierInvPairingCanonicalExtension
    (f : SchwartzMap ℝ ℂ) (w : ℂ) : ℂ

theorem section43FourierInvPairingCanonicalExtension_eq_complexLaplaceTransform
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {η : ℝ} (hη : 0 < η) :
    section43FourierInvPairingCanonicalExtension f (η * Complex.I) =
      section43ComplexLaplaceTransform f ((2 * Real.pi * η : ℂ))

theorem section43ComplexLaplaceTransform_eq_fourierInvPairingCanonicalExtension_of_pos
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {σ : ℝ} (hσ : 0 < σ) :
    section43ComplexLaplaceTransform f (σ : ℂ) =
      section43FourierInvPairingCanonicalExtension f
        ((σ / (2 * Real.pi)) * Complex.I)
```

The general canonical extension is the same `SCV.fourierLaplaceExt` definition
as the specialized slice extension, but parameterized only by the one-variable
Schwartz input `f`.  Its positive-imaginary-axis proof is the already compiled
specialized proof without any multivariate data.  The rescaled `σ` theorem is
by choosing `η = σ / (2 * Real.pi)` and using
`field_simp [Real.two_pi_pos.ne']`.

Main Packet-F scalar bridge:

```lean
theorem section43FourierLaplaceIntegral_eq_iterated_canonicalSliceExtension_of_mem_positiveEnergy_of_posCoord
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1))
    (hqr : 0 < section43QTime (d := d) (n := n + 1) q r) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
              (τbg i : ℂ) *
                (section43QTime
                  (d := d) (n := n + 1) q (r.succAbove i) : ℂ))) *
        section43FourierInvPairingCanonicalExtension
          (section43PartialFourierSpatialTimeSliceSchwartz
            (d := d) (n := n + 1)
            (section43DiffPullbackCLM d (n + 1) f)
            r
            ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
            (section43QSpatial (d := d) (n := n + 1) q))
          (((section43QTime (d := d) (n := n + 1) q r) /
              (2 * Real.pi)) * Complex.I)
```

Proof transcript:

1. Rewrite by
   `section43FourierLaplaceIntegral_eq_iterated_complexLaplaceTransform_of_mem_positiveEnergy`.
2. Apply `MeasureTheory.integral_congr_ae`; fix `τbg`.
3. Rewrite the one-variable factor with
   `section43ComplexLaplaceTransform_eq_fourierInvPairingCanonicalExtension_of_pos`,
   using `hqr`.
4. The support hypothesis for that rewrite is
   `section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback`
   applied to the frozen background vector and spatial momentum.

This theorem is the first clean scalar-level meeting point between the OS I
`(4.20)` normal form and the canonical Paley-Wiener slice extension.  It is
still not the final Wightman/OS comparison; it prepares the exact scalar object
that the shell-to-Laplace identification must consume.

Production status, 2026-04-14: Packet F is implemented in
`Section43OneVariableSlice.lean`:

```lean
section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time_of_support_positiveEnergy
section43PartialFourierSpatial_fun_eq_zero_of_neg_time_of_support_positiveEnergy
section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_support_positiveEnergy
section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback
section43FourierInvPairingCanonicalExtension
section43FourierInvPairingCanonicalExtension_eq_complexLaplaceTransform
section43FourierInvPairingCanonicalExtension_imagAxis_eq_descendedPsiZ
section43FourierInvPairingCanonicalExtension_differentiableOn
section43ComplexLaplaceTransform_eq_fourierInvPairingCanonicalExtension_of_pos
section43FourierLaplaceIntegral_eq_iterated_canonicalSliceExtension_of_mem_positiveEnergy_of_posCoord
```

Fresh verification:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice
```

The exact file check terminated with exit code `0` and no warnings.  The narrow
module build ended:

```text
✔ [8312/8312] Built OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice (10s)
Build completed successfully (8312 jobs).
```

Packet G: descended-`ψ_Z` quotient normal form for the OS I scalar.

The Wightman canonical witness already has an imaginary-axis theorem landing in
the one-variable quotient pairing against `ψ_Z`.  After Packet F, the OS I
scalar can be placed in the same codomain by a purely one-variable rewrite.

Public declarations:

```lean
theorem section43FourierInvPairingCanonicalExtension_imagAxis_eq_descendedPsiZ_of_pos
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {σ : ℝ} (hσ : 0 < σ) :
    section43FourierInvPairingCanonicalExtension f
        ((σ / (2 * Real.pi)) * Complex.I) =
      fourierPairingDescendsToSection43PositiveEnergy1D
        (section43FourierInvPairingCLM f)
        (section43FourierInvPairing_hasOneSidedFourierSupport f hf_supp)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ (((σ : ℂ) * Complex.I)) _))

theorem section43FourierLaplaceIntegral_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1))
    (hqr : 0 < section43QTime (d := d) (n := n + 1) q r) :
    section43FourierLaplaceIntegral d (n + 1) f q =
      ∫ τbg : Fin n → ℝ,
        Complex.exp (...) *
        fourierPairingDescendsToSection43PositiveEnergy1D
          (section43FourierInvPairingCLM (...slice...))
          (section43FourierInvPairing_hasOneSidedFourierSupport (...slice...)
            (...diffPullback support...))
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((section43QTime (d := d) (n := n + 1) q r : ℂ) *
                Complex.I)) _))
```

Proof transcript:

1. The first theorem is
   `section43FourierInvPairingCanonicalExtension_imagAxis_eq_descendedPsiZ`
   with `η = σ / (2 * Real.pi)`, followed by the scalar identity
   `2 * Real.pi * (σ / (2 * Real.pi)) = σ`.
2. The second theorem rewrites by Packet F's
   `section43FourierLaplaceIntegral_eq_iterated_canonicalSliceExtension_of_mem_positiveEnergy_of_posCoord`,
   applies `MeasureTheory.integral_congr_ae`, and uses the first theorem.
3. The support proof for each frozen slice is again
   `section43Tsupport_partialFourierSpatial_timeSlice_subset_Ici_diffPullback`.

This is still pure OS I / one-variable quotient support.  It does not mention
the old multivariate `os1TransportComponent`, and it does not assert any
Wightman/Schwinger equality.  It simply puts the OS I scalar into the same
one-variable descended quotient language as the canonical Wightman witness.

Production status, 2026-04-14: Packet G is implemented in
`OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean`.
The exact file check

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
```

terminated with exit code `0` and no warnings.  The narrow module build

```bash
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice
```

also terminated successfully:

```text
✔ [8312/8312] Built OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice (10s)
Build completed successfully (8312 jobs).
```

Consequent next theorem slot: do not add another wrapper around the old
`hφf/hψg` supplier bodies.  The next Lean-facing theorem must consume the
compiled OS I scalar normal form above together with the Wightman canonical
witness descended-`ψ_Z` theorem, and it must state the explicit
Fourier-Laplace transformed representative/common-normal-form hypothesis that
prevents the same-test collapse.  If that theorem cannot yet be stated with a
visible scalar `N`, the proof docs remain the active work surface.

Packet H: explicit transformed-representative surface for consuming Packet G.

The first consumer-facing theorem should not require a full Schwartz-valued
construction of the OS I Fourier-Laplace map.  It is enough, and safer for the
current frontier, to state the exact apply surface that any ambient
representative must satisfy on the positive-energy half-space.

Production declarations:

```lean
def section43FourierLaplaceRepresentative (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (Φ : SchwartzNPoint d n) : Prop :=
  ∀ q : NPointDomain d n, q ∈ section43PositiveEnergyRegion d n →
    Φ q = section43FourierLaplaceIntegral d n f q

theorem section43FourierLaplaceRepresentative_apply
    (hΦ : section43FourierLaplaceRepresentative d n f Φ)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    Φ q = section43FourierLaplaceIntegral d n f q

theorem section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (Φ : SchwartzNPoint d (n + 1))
    (hΦ : section43FourierLaplaceRepresentative d (n + 1) f Φ)
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1))
    (hqr : 0 < section43QTime (d := d) (n := n + 1) q r) :
    Φ q = ∫ τbg : Fin n → ℝ, ...descended one-variable ψZ scalar...

theorem section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_height
    (f : euclideanPositiveTimeSubmodule (d := d) (n + 1))
    (Φ : SchwartzNPoint d (n + 1))
    (hΦ : section43FourierLaplaceRepresentative d (n + 1) f Φ)
    (q : NPointDomain d (n + 1))
    (r : Fin (n + 1))
    (η : ℝ)
    (hq : q ∈ section43PositiveEnergyRegion d (n + 1))
    (hη : 0 < η)
    (hqr : section43QTime (d := d) (n := n + 1) q r =
      2 * Real.pi * η) :
    Φ q = ∫ τbg : Fin n → ℝ, ...same descended scalar, with q_r^0...

theorem section43QTime_complexPsiArg_eq_of_height
    (hqr : section43QTime (d := d) (n := n) q r = 2 * Real.pi * η) :
    ((section43QTime (d := d) (n := n) q r : ℂ) * Complex.I) =
      (((2 * Real.pi * η : ℝ) : ℂ) * Complex.I)

theorem section43_realHeight_complexPsiArg_eq (η : ℝ) :
    (((2 * Real.pi * η : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi : ℂ) * (η * Complex.I))
```

This is not a replacement for the eventual full component map.  It is the
Lean-facing apply contract that prevents the old same-test collapse: the
hypothesis is a pointwise OS I `(4.19)-(4.20)` Fourier-Laplace formula on the
positive-energy region, not the current quotient-inclusion
`os1TransportComponent`.

Proof transcript:

1. `section43FourierLaplaceRepresentative_apply` is direct application of the
   predicate.
2. The descended consumer is
   `section43FourierLaplaceRepresentative_apply`, followed by Packet G's
   `section43FourierLaplaceIntegral_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord`.
3. The height-specialized consumer derives
   `0 < section43QTime ... q r` from `section43QTime ... q r = 2π η` and
   `0 < η`, then calls the positive-coordinate consumer.  It deliberately
   keeps the `ψ_Z` kernel in the `q_r^0` form to avoid dependent proof
   rewriting; the complex equality with the Wightman spelling
   `(2π : ℂ) * (η * I)` should be performed only at the global consumer if
   Lean actually requires that syntactic normal form.
4. The two scalar normalization lemmas give that future global consumer the
   exact non-dependent equalities it needs before it rewrites inside the
   dependent `SCV.schwartzPsiZ` term.

Production status, 2026-04-14:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice
```

All four commands terminated with exit code `0`; the two narrow module builds
ended at `[8311/8311]` and `[8312/8312]`, respectively.

After adding the height-specialized theorem, the exact file check and narrow
module build for `Section43OneVariableSlice` were rerun; both again terminated
with exit code `0`.

After adding the two scalar normalization lemmas, the exact file checks and
narrow module builds for both `Section43FourierLaplaceTransform` and
`Section43OneVariableSlice` were rerun in dependency order; all four commands
again terminated with exit code `0`.

Verification for the extraction:

1. After Packet A, run:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43OneVariableSlice.lean
```

2. Repeat the same exact check after each of Packets B, C, and D.
3. Only after Packet D compiles should `OSToWightmanPositivity.lean` import
   `Section43OneVariableSlice`.  At that point, update consumers one theorem at
   a time to the `section43`-prefixed support names, then run the exact
   Positivity file check.
4. Do not delete the old stranded declarations from
   `OSToWightmanPositivity.lean` until all active consumers have been updated
   and the exact Positivity check terminates with exit code `0`.

Sanity checks before implementation:

1. No theorem in this packet may have hypotheses that can be solved by
   `simp [os1TransportComponent_apply]`.
2. No theorem in this packet may mention `bvt_W`, `bvt_F`, `OS.S`, or
   `OSInnerProductTimeShiftHolomorphicValue`.
3. The first exact Lean check after implementation should be only the new
   support file:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean
```

4. Only after that support file is clean should `OSToWightmanPositivity.lean`
   import it and replace any quarantined surface.

### 5.9.2. Lemma 4.1 density: quotient-side theorem, not the live positivity blocker

The dense-image half of OS I Lemma 4.1 cannot be implemented on the current
support-restricted subtype source. Production now proves the one-variable
counterexample `not_denseRange_os1TransportOneVar`, and the same warning applies
to the literal multivariate subtype target.

What is settled:

1. `DenseRange (os1TransportComponent d (n + 1))` on the current
   `euclideanPositiveTimeSubmodule` source should not be used as a production
   theorem slot. Degree `0` is exceptional and not part of this negative
   theorem.
2. `DenseRange (os1TransportComponent d (n + 1))` in full
   `SchwartzNPoint d (n + 1)` is false and is withdrawn.
3. A fixed Seeley extension has closed range, so no proof should aim at dense
   range in the full ambient Schwartz space.
4. The honest quotient-side dense map is the ambient Schwartz quotient map
   `section43PositiveEnergyQuotientMap`, and production already has its
   one-variable and multivariate surjective/dense-range forms.
5. If Lemma 4.1 is later formalized faithfully, it must be stated on the
   actual half-space codomain `L(R_+^{4n})` from Section 4.3, not on the
   support-restricted subtype currently used for Euclidean inputs.
6. The positivity proof for theorem 3 does not need that Schwartz-density
   theorem as a live prerequisite. What it needs is:
   - the transport-map comparison on positive-time inputs,
   - density of the resulting vectors in the Hilbert space `H`,
   - continuity/closure on the `bvt_W` side.

So the current live route should not contain either
`os1TransportOneVar_denseRange` or `os1TransportComponent_denseRange` as
production targets. The only honest dense-range theorems now on this branch are
the quotient-side maps
`denseRange_section43PositiveEnergyQuotientMap1D` and
`denseRange_section43PositiveEnergyQuotientMap`.

The file should not attempt to prove `bvtTransportImage_dense` by separate
topological arguments. The positivity route should go through injectivity /
kernel-zero on the transport side and Hilbert-space density on the OS side.

### 5.9.3. Detailed proof of the on-image transport map

The Section-4.3 Hilbert transport is **not** a map on raw `BorchersSequence d`.
It is defined only on the transformed image.

The honest current-code package is:

1. represent the transformed-image core by a finite-support sequence whose
   degree-`n` raw Schwartz component becomes a transformed-image point after
   applying `section43PositiveEnergyQuotientMap (d := d) n`;
2. choose, for each degree, a Euclidean positive-time preimage;
3. map that preimage to the existing OS vector
   `euclideanPositiveTimeSingleVector`;
4. sum over the finite degree support in `OSHilbertSpace OS`.

That is why the correct current-code structure is:

```lean
structure BvtTransportImageSequence (d : ℕ) [NeZero d] where
  toBorchers : BorchersSequence d
  image_mem : ∀ n,
    section43PositiveEnergyQuotientMap (d := d) n (toBorchers.funcs n) ∈
      bvtTransportImage (d := d) n
```

The well-definedness proof must use `os1TransportComponent_eq_zero_iff`, not
density. The exact proof is:

1. suppose two Euclidean preimages give the same transformed-image element;
2. subtract them;
3. the difference maps to zero under `os1TransportComponent` after comparing
   both preimages to the same quotient class
   `section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n)`;
4. injectivity / kernel-zero gives equality of the preimages;
5. therefore the OS Hilbert vector does not depend on the choice.

### 5.9.4. Detailed proof of Eq. `(4.28)` on the image

The theorem

`bvt_wightmanInner_eq_transport_norm_sq_onImage`

must be proved first in the diagonal norm-square form. The polarized inner
product identity, if ever wanted later, is downstream and optional.

The proof transcript is:

1. start from a transformed-image sequence `F`;
2. choose degreewise Euclidean preimages `f_n` in the positive-time domain;
3. expand the Wightman quadratic form degreewise using the current public
   `WightmanInnerProduct`;
4. for each component pair, rewrite the Wightman pairing by the
   Section-4.3 / Lemma-4.2 Fourier-Laplace computation:
   - spatial Fourier transform is handled by the ordinary tempered
     distribution Fourier calculus already used elsewhere in the repo;
   - the first direct consumer of the slice-descent theorem is the concrete
     adapter `lemma42_matrix_element_time_interchange`;
   - the purely configuration-space shell inside that adapter is already
     formalized by `conjTensorProduct_timeShift_eq_tailTimeShift` and
   `simpleTensor_timeShift_integral_eq_xiShift_conj` in
   [OSToWightman.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean);
   - inside that adapter, the reusable Section-8 one-variable theorem is now
     already formalized privately as
     `one_variable_time_interchange_for_wightman_pairing` in
     [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
   - do not replace that one-variable step by a naive "the canonical
     `xiShift(wickRotate(y), t * I)` shell is already pointwise inside
     `ForwardTube` for every ambient `y`" argument: that statement is false on
     the corrected ambient theorem surface, because the `xiShift` updates only
     one time-difference coordinate and the remaining Wick-rotated differences
     need not lie in the forward cone;
   - in the current repo, the honest Lean supplier for that one-variable step
     should be routed through `SCV.paley_wiener_one_step` /
     `SCV.paley_wiener_half_line`, not a fresh ad hoc many-variable
     continuation theorem;
   - more precisely: `paley_wiener_half_line` first produces the **ambient**
     witness on `SCV.upperHalfPlane`, because it is a Fourier/Laplace theorem
     for a real-line tempered pairing; it does **not** directly hand us the
     final right-half-plane witness used by the semigroup-side
     `singleSplit_xiShift` comparison;
   - so the immediate post-Paley-Wiener theorem slot is an upper-half-plane
     witness/exact-boundary-value statement for the ambient Wightman pairing;
   - in the current repo, that route has already been reduced further to the
     closed flattened spectral package ending at
     `bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened`
     in
     [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean);
   - so the remaining live content is no longer the paired-vanishing /
     one-sided-support theorem, but the witness-consuming seam itself:
     positive-imaginary-axis identification plus the canonical-shell limit
     theorem for the actual ambient upper-half-plane witness;
   - the first direct consumer of that witness only needs the values on the
     positive imaginary axis: if the canonical shell converges to `H(i t)` and
     `H(i t)` is identified with the semigroup-side holomorphic value, the
     current kernel reduction already closes;
   - only if one wants a whole-domain comparison of holomorphic witnesses does
     one then need the existing upper-half-plane identity theorem or an
     explicit rotation bridge before invoking any right-half-plane uniqueness
     statement;
   - the common kernel is the corrected OS-II-backed analytic-continuation
     object underlying `bvt_F` / `bvt_W`, not a fresh spectral-measure
     construction in Section 4.3 itself.
5. recognize the resulting degreewise finite sum as the Hilbert norm square of
   `bvt_transport_to_osHilbert_onImage`.

No theorem in this package should claim that the raw Wightman quadratic form on
the same literal test function equals the raw OS pairing. The comparison is
only true after transport through the Section-4.3 image.

### 5.9.4a. Current shell-to-Laplace frontier: proof-doc completion target

This subsection is the current gate for the OS-route positivity work. No more
production Lean should be added to the shell-to-Laplace seam until the theorem
slots in this subsection have been made exact and implementable.

Current production facts already available:

1. In
   [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean):
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   proves the explicit canonical `xiShift` shell has Wightman boundary-value
   limit
   `bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint t ψ))`.
2. In
   [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean):
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension`,
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral`,
   and
   `tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_to_imagAxis`
   give the canonical ambient upper-half-plane witness and its horizontal-line
   boundary recovery at `(t : ℂ) * Complex.I`.
3. In
   [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean):
   `tendsto_bvt_F_canonical_xiShift_shell_sub_iterated_to_timeShift_sub_canonicalExtension`
   computes the limit of the explicit shell-minus-iterated expression as

```lean
bvt_W OS lgc (n + m)
  (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))
-
bvt_W_conjTensorProduct_timeShiftCanonicalExtension
  (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)
```

This residual theorem is **diagnostic only**. It must not be turned into an
unconditional zero-limit target for arbitrary `φ, ψ`. Such a theorem would
identify a real-time Wightman value with an imaginary-axis Laplace value for
arbitrary test data, reproducing the old false `hschw` shape in a more
elaborate form.

The corrected target is the transported-image version required by Lemma 4.2.
The next proof must include Section-4.3 quotient hypotheses tying the ambient
Wightman representatives `φ, ψ` to positive-time Euclidean preimages `f, g`.

The theorem that actually closes the shell side is:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, 0 < t →
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)))
```

Older diagnostic equivalence:

The theorem above can be related to the following pointwise descended
Section-4.3 bridge by the already-proved shell boundary-value theorem and the
canonical imag-axis descended-pairing theorem. This is no longer the active
implementation surface; the live pointwise theorem is the Lemma-8.4 supplier
`lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`,
followed by
`bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport`.

```lean
private theorem
    bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, ∀ ht : 0 < t,
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht)))
```

Historical proof transcript for this equivalence:

1. Use
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   to identify the shell limit with the left side of
   `bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport`.
2. Use
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`
   to rewrite the canonical imag-axis value as the descended `ψ_z` pairing on
   the right side.
3. Apply `tendsto_nhds_unique` after rewriting both limits to the same scalar.

Once the shell side is closed, the OS matrix-element target is obtained by the
already-proved ambient/preimage canonical-to-OS reducer:

```lean
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_ambient_descended_psiZ_boundaryValue_eq
```

Its remaining hypothesis is the quotient/slice comparison

```lean
∀ t : ℝ, ∀ ht : 0 < t,
  fourierPairingDescendsToSection43PositiveEnergy1D
    (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc φ ψ hψ_compact)
    (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
      (d := d) OS lgc hm φ ψ hψ_compact)
    (section43PositiveEnergyQuotientMap1D (ψZ t ht))
  =
  selfAdjointSpectralBoundaryValueOffdiagCLM
    (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
    xF xG
    (ψZ t ht)
```

where `ψZ t ht` abbreviates
`SCV.schwartzPsiZ (((2 * Real.pi : ℂ) * (t * Complex.I)))` with the positivity
proof `by simpa [Complex.mul_im, ht.ne'] using mul_pos Real.two_pi_pos ht`, and
`xF, xG` are the OS Hilbert vectors of
`PositiveTimeBorchersSequence.single n f.1 f.2` and
`PositiveTimeBorchersSequence.single m g.1 g.2`.

#### 5.9.4a.1. Implementation packet for the transported-image bridge

Latest correction status, 2026-04-13: this subsection records an older
transported-image draft. It is retained for historical context, but it is not
the current shell-to-Laplace implementation route. The later fixed-`x` scalar
audit withdraws the finite-height shell/horizontal residual plan. The public
Paley-Wiener export and the strengthened BV/FL `Tflat` package remain useful
diagnostic infrastructure, but the immediate Lean target is now the hPsi /
positive-support time-interchange packet in §5.9.4a.1.hPsi.

The shell-minus-horizontal cancellation theorem below is no longer an active
implementation target, because its intended finite-height supplier has been
withdrawn. A future proof may revive it only with a new explicit
boundary-value / positive-support time-interchange theorem that does not assert
finite-height shell/horizontal equality.

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)
```

This shell-minus-horizontal zero theorem is a historical consumer shape, not a
current target. The transported Section-4.3 hypotheses are necessary but not
sufficient: the theorem still needs a non-finite-height Lemma-8.4 supplier, and
must not be proved from the withdrawn finite-height residual packet.

For Lean execution, do **not** prove the residual theorem by an unnamed
analytic lemma. The non-subtracted `singleSplit` shell theorem displayed next
is downstream diagnostic/assembly work retained for older reducers; it is not
an implementation target for the live `lemma42` consumer. The first
irreducible theorem for the live shell-to-Laplace seam is instead the
non-finite-height pointwise Lemma-8.4 supplier
`lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`.

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_singleSplitXiShift_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.1.osConjTensorProduct g.1) y))
```

For the Lean implementation, introduce these private local abbreviations before
the theorem. They are not route-changing wrappers; they name the two exact
scalars already displayed above so the zero-residual proof has a stable target.

```lean
private noncomputable def bvtCanonicalXiShiftShell
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (t : ℝ) : ℝ → ℂ := fun ε =>
  ∫ y : NPointDomain d (n + m),
    bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)) *
      (φ.conjTensorProduct ψ) y

private noncomputable def bvtSingleSplitXiShiftScalar
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (t : ℝ) : ℂ :=
  ∫ y : NPointDomain d (n + m),
    bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
      (f.osConjTensorProduct g) y
```

Withdrawn pointwise-first surface:

```lean
private theorem
    bvt_W_timeShift_sub_descendedPsiZ_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) -
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) =
      0
```

This statement is not false on the transported surface, but it must **not** be
the first implementation target. Its left side contains the bare pointwise
Wightman time-shift value
`bvt_W OS lgc (n + m)
  (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))`.
A direct proof would require a separate point-evaluation normal form for the
time-shift distribution. The existing production infrastructure is shaped for
Schwartz-tested boundary values and horizontal-line pairings, so this theorem
is downstream only. After
`bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport` is obtained from the
limit-level zero residual, the subtractive form is the one-line formal corollary
`sub_eq_zero.mpr`.

Do not attach any slice/Fubini proof transcript to this pointwise theorem. The
slice-kernel zero lemmas are consumed first by the positive-height
shell/interchange theorem below, where both sides remain under integral signs.

Exact route decision after the 2026-04-12 scalar-normal-form audit:

The pointwise-first theorem
`bvt_W_timeShift_sub_descendedPsiZ_zero_of_section43Transport` is withdrawn as
the first hard Lean target. It has a bare value
`bvt_W(... timeShift t ...)`, so a direct proof would require an additional
Schwartz approximate-identity or point-evaluation normal form. That is the
wrong first implementation surface for the code we already have.

The later 2026-04-13 fixed-`x` correction withdraws the stronger
finite-height shell/interchange normal form as a Lean target. The raw
positive-height shell carries the real-time oscillatory factor
`exp (-(I * t * λ))`, while the canonical horizontal witness carries the
imaginary-axis Laplace factor `exp (t * λ)` after the `ψ_Z` calculation. The
conversion between those two expressions is exactly the OS I positive-support
time-interchange step, not a finite-height equality between the two
regularizations.

Therefore the current shell-to-Laplace seam is no longer the transported
finite-height theorem below. The live theorem is the non-finite-height
pointwise positive-support identity

```lean
private theorem
    bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport
```

which identifies the real-time Wightman matrix element with the canonical
upper-half-plane witness at `t * I` under the Section-4.3 transport
hypotheses. Once this pointwise identity is proved, the required shell limit is
formal from the already-compiled boundary-value theorem
`tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`.
The finite-height statements below are retained only as historical diagnostic
drafts and sign checks.

The selected right-block time coordinate is still

```lean
let rψ : Fin m := ⟨0, hm⟩
let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
```

where `r` is the embedded right-block coordinate and `rψ` is the corresponding
coordinate on the isolated right factor. This is a code-level convention, not
just paper notation: in
[OSToWightman.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean),
`xiShift j 0` updates every tail coordinate `i` with `j.val ≤ i.val`. The
comment above its definition explains why this is the correct single
cumulative-difference time variable: shifting only one absolute coordinate
would alter two adjacent difference variables. Therefore the one-variable
time-shift in Lemma 4.2 is the tail-gap coordinate `r = ⟨n, ...⟩`, while the
same variable appears on the isolated right factor as `rψ = 0`.

The finite-height theorem statement must expose the exact measure variables,
frozen background-time maps, and spatial Fourier variables whose integrand is a
linear combination of the two scalar kernels already present in
`OSToWightmanPositivity.lean`:

```lean
fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
  (d := d) (n := n) (m := m) hφf
  rφ tφ htφ ξφ rψ tψ htψ ξψ

fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
  (d := d) (n := n) (m := m) hφf hψg
  rφ tφ htφ ξφ rψ tψ htψ ξψ
```

Here `tφ`, `tψ` are the frozen background-time maps produced by the expanded
time-shift/conj-tensor-product normal form, `htφ` and `htψ` are exactly the
nonnegative frozen-time obligations needed by
`tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`,
and `ξφ`, `ξψ` are the two spatial Fourier variables.

Historical finite-height draft, withdrawn after the fixed-`x` audit:

The theorem below was previously proposed as the finite-height implementation
of OS I p. 96 `(4.23) -> (4.24)`. It is not a current Lean target. Even with
the Section-4.3 transport hypotheses `hφf` and `hψg`, the displayed finite
height equality would still need an additional analytic-continuation theorem
to convert the oscillatory shell factor into the Laplace damping factor. No
current implementation should try to prove this theorem or use it as a
supplier for `lemma42_matrix_element_time_interchange`.

```lean
private theorem
    bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    (∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y) -
    (∫ x : ℝ,
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))) τ) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
    0
```

Implementation-readiness status for this theorem:

1. The shell-side `KShell` packet and the horizontal `KHorizontal` packet are
   diagnostic support infrastructure only. They expose the two analytic
   regularizations as `Tflat` pairings, and their pointwise formulas are useful
   for sign checks, but they do not close the transported residual.
2. The direct theorem name recorded in the previous draft,
   `canonicalShell_horizontal_kernel_eqOn_dualCone_of_section43Transport`, is
   withdrawn before implementation. Even with `hφf` and `hψg` in scope, the
   proof must not assert raw pointwise equality between the canonical
   real-time shell kernel and the horizontal imaginary-axis kernel. The scalar
   audit shows that these raw kernels carry different exponential factors.
3. The previous scalar Section-4.3 finite-height normal form
   `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ`
   is withdrawn for the same reason. The proof docs may keep the surrounding
   `Tflat`, Paley-Wiener, and frozen-slice calculations as diagnostic support,
   but they are not a certificate for a finite-height equality.
4. The first non-formal mathematical claim that remains on route is the
   non-finite-height time-interchange theorem
   `bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport`.
   It must be proved from the one-variable positive-support / Section-4.3
   quotient packet, not from a finite-height residual. After it is available,
   `tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport`
   is a short `Filter.Tendsto.congr`/target-rewrite proof from the existing
   shell boundary-value theorem.

Historical Lean skeleton for the withdrawn finite-height theorem:

```lean
  classical
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc φ ψ hψ_compact
  have hShift :
      (∫ x : NPointDomain d (n + m),
        bvt_F OS lgc (n + m) (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I) *
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x) =
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) :=
    bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) t ε
  have hShellTW :
      (∫ x : NPointDomain d (n + m),
        bvt_F OS lgc (n + m) (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I) *
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x) =
      ∫ x : ℝ,
        TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x :=
    bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact)
      (f := f) (g := g) (hf_compact := hf_compact)
      (hg_compact := hg_compact) hφf hψg
      (ht := ht) (hε := hε)
  calc
    (∫ y : NPointDomain d (n + m), ... xiShift shell ...) -
        (∫ x : ℝ, ... iterated TW expansion ...) =
      (∫ x : NPointDomain d (n + m), ... time-shifted canonical shell ...) -
        (∫ x : ℝ, ... iterated TW expansion ...) := by
        rw [← hShift]
    _ =
      (∫ x : ℝ,
        TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x) -
        (∫ x : ℝ, ... iterated TW expansion ...) := by
        rw [hShellTW]
    _ =
      (∫ x : ℝ, ... iterated TW expansion ...) -
        (∫ x : ℝ, ... iterated TW expansion ...) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simpa using
          hTW_apply ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x))
    _ = 0 := by
        rw [sub_self]
```

The withdrawn statement
`bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ` is
kept below only to preserve the scalar audit trail. It must not be promoted to
a Lean target unless a new analytic theorem explicitly proves the missing
oscillatory-to-Laplace continuation step.

2026-04-13 readiness correction for this statement:

The equality above is stronger than the already-proved shell limit and is not
available from definitional rewriting. The raw dual-cone diagnostics show why:
the canonical shell carries a real-time oscillatory factor, while the
horizontal canonical witness carries Laplace damping. The local frozen-slice
bridge below remains a valid Section-4.3 support lemma, but it acts only after
the one-variable time variable has been separated. It is not a certificate for
the withdrawn finite-height theorem.

```lean
private theorem
    section43_frozenSlicePairing_eq_of_transport_on_positiveGap
    {n m : ℕ}
    {φ : SchwartzNPoint d n} {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n)
    (rψ : Fin m)
    (u : Fin (n + m) → ℝ)
    (hu : u ∈ positiveGapOrthant (n + m))
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    let tφ : Fin n → ℝ :=
      absTimesOfTailGapsSplitLeft (n := n) (m := m) u
    let tψ : Fin m → ℝ :=
      absTimesOfTailGapsSplitRight (n := n) (m := m) u
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz
            (d := d) (n := n) φ rφ tφ ξφ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz
            (d := d) (n := m) ψ rψ tψ ξψ))
```

Proof transcript:

1. Introduce
   `tφ := absTimesOfTailGapsSplitLeft (n := n) (m := m) u` and
   `tψ := absTimesOfTailGapsSplitRight (n := n) (m := m) u`.
2. Obtain
   `hφ_nonneg : ∀ i : Fin n, 0 ≤ tφ i` from
   `absTimesOfTailGapsSplitLeft_nonneg (n := n) (m := m) hu`.
3. Obtain
   `hψ_nonneg : ∀ j : Fin m, 0 ≤ tψ j` from
   `absTimesOfTailGapsSplitRight_nonneg (n := n) (m := m) hu`.
4. Apply
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
   with
   `htφ := fun i _ => hφ_nonneg i` and
   `htψ := fun j _ => hψ_nonneg j`.
5. Close by `simpa [tφ, tψ]`.

This theorem is intentionally small and non-wrapper-shaped: it is the exact
place where Section-4.3 transport acts on a frozen scalar once the
positive-support time-interchange has already reduced the problem to unshifted
representatives. If an expansion contains a shifted ambient slice
`timeShiftSchwartzNPoint τ ψ`, do not use this lemma to force equality. First
prove the non-finite-height one-variable time-interchange theorem.

The older scalar helper below is retained as a historical normal-form draft.
It is not implementation-ready after the fixed-`x` audit:

```lean
private theorem
    bvt_F_canonical_xiShift_shell_eq_integrated_descendedPsiZ_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact
    let hTW :
      SCV.HasOneSidedFourierSupport TW :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
        (d := d) OS lgc hm φ ψ hψ_compact
    (∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y) =
    ∫ x : ℝ,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        TW hTW
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

Mandatory `Fin 1` adapter before applying `schwartz_clm_fubini_exchange`:

Do **not** instantiate `schwartz_clm_fubini_exchange` directly with

```lean
TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ
```

The Fubini axiom is stated for functionals on
`SchwartzMap (Fin m → ℝ) ℂ`, so the normal-form helper must first pass through
the following local one-coordinate adapter. This is type-level infrastructure,
not a theorem-surface wrapper: it is exactly the change from the paper's
one real time variable to the production axiom's `Fin 1 → ℝ` parameter.

```lean
let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1

let fromFin1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1.symm

let T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ :=
  TW.comp fromFin1

let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
  SCV.schwartzPsiZ
    ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
    (by
      have hscaled : 0 < (2 * Real.pi) *
          (((x : ℂ) + ε * Complex.I).im) :=
        mul_pos Real.two_pi_pos (by simpa using hε)
      simpa [Complex.mul_im] using hscaled)

let f1 : SchwartzMap (Fin 1 → ℝ) ℂ :=
  toFin1 ((SchwartzMap.fourierTransformCLM ℂ) ψZt)

let g1 : (Fin 1 → ℝ) → SchwartzMap (Fin 1 → ℝ) ℂ := fun x1 =>
  toFin1 ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε (e1 x1)))
```

The only reindex simplifications allowed here are:

```lean
have h_from_to (χ : SchwartzMap ℝ ℂ) :
    fromFin1 (toFin1 χ) = χ := by
  ext x
  simp [fromFin1, toFin1, e1]

have h_to_apply (χ : SchwartzMap ℝ ℂ) (x1 : Fin 1 → ℝ) :
    toFin1 χ x1 = χ (e1 x1) := by
  simp [toFin1]

have h_fin1_volume (F : ℝ → ℂ) :
    (∫ x1 : Fin 1 → ℝ, F (e1 x1)) = ∫ x : ℝ, F x := by
  simpa [e1] using
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
      (g := F)
```

The corresponding local consequence for the Fubini output is:

```lean
have h_outer_real :
    (∫ x1 : Fin 1 → ℝ, T1 (g1 x1) * f1 x1) =
      ∫ x : ℝ,
        TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  let F : ℝ → ℂ := fun x =>
    TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x
  calc
    (∫ x1 : Fin 1 → ℝ, T1 (g1 x1) * f1 x1)
        = ∫ x1 : Fin 1 → ℝ, F (e1 x1) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x1
            simp [F, T1, g1, f1, h_from_to, h_to_apply]
    _ = ∫ x : ℝ, F x := h_fin1_volume F
    _ = ∫ x : ℝ,
        TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := rfl
```

No Fourier-transform/reindex commutation theorem is required in this package:
`SchwartzMap.fourierTransformCLM ℂ` is applied on `SchwartzMap ℝ ℂ` first, and
only the already transformed test is transported by `toFin1`.

If Lean asks for the two side hypotheses of `schwartz_clm_fubini_exchange`, the
first helper statements must be exactly these, with no stronger theorem surface:

```lean
private theorem
    continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal
    {ε : ℝ} (hε : 0 < ε) :
    Continuous
      (fun x1 : Fin 1 → ℝ =>
        let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
          ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
        let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
          SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
        toFin1
          ((SchwartzMap.fourierTransformCLM ℂ)
            (SCV.schwartzPsiZ
              ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
              (by
                have hscaled : 0 < (2 * Real.pi) *
                    (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                  mul_pos Real.two_pi_pos (by simpa using hε)
                simpa [Complex.mul_im] using hscaled))))

private theorem
    seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth
    {ε : ℝ} (hε : 0 < ε) :
    ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x1 : Fin 1 → ℝ),
        SchwartzMap.seminorm ℝ k n
          (let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
            ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
           let toFin1 : SchwartzMap ℝ ℂ →L[ℂ]
                SchwartzMap (Fin 1 → ℝ) ℂ :=
            SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
           toFin1
            ((SchwartzMap.fourierTransformCLM ℂ)
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                    mul_pos Real.two_pi_pos (by simpa using hε)
                  simpa [Complex.mul_im] using hscaled)))) ≤
          C * (1 + ‖x1‖) ^ N
```

These side helpers are the public versions of the already-used Paley-Wiener
horizontal continuity/growth estimates, transported through `toFin1`. They are
allowed only because they discharge the exact `hg_cont` and `hg_bound` premises
of `schwartz_clm_fubini_exchange`; they must not introduce a new comparison
between Wightman and OS scalars.

Implementation transcript for the two `Fin 1` side helpers:

1. Put these helpers in
   [SCV/PaleyWiener.lean](/Users/xiyin/OSReconstruction/OSReconstruction/SCV/PaleyWiener.lean),
   or in a small imported Paley-Wiener support file, not in the theorem-3
   positivity frontier. They are one-variable Schwartz/PW facts and should be
   available before the OS-specific normal-form helper is attempted.
2. First expose the underlying real-line continuity theorem:

```lean
theorem continuous_schwartzPsiZ_twoPi_horizontal
    {η : ℝ} (hη : 0 < η) :
    Continuous
      (fun x : ℝ =>
        SCV.schwartzPsiZ
          ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
          (by
            have hscaled : 0 < (2 * Real.pi) *
                (((x : ℂ) + η * Complex.I).im) :=
              mul_pos Real.two_pi_pos (by simpa using hη)
            simpa [Complex.mul_im] using hscaled))
```

   Proof: in `PaleyWiener.lean`, reuse the existing private probe
   calculations
   `continuous_weightedDerivToBCFCLM_scaledHorizontal` and the definition
   `scaledHorizontalSchwartzPsi`. The only algebraic rewrite is
   `((2 * Real.pi : ℂ) * ((x : ℂ) + η * Complex.I))
      = ((2 * Real.pi * x : ℝ) : ℂ) +
        (2 * Real.pi * η : ℝ) * Complex.I`.
   If those probe lemmas remain private, this theorem must be placed in the
   same file below them; do not copy the whole probe development into
   `OSToWightmanPositivity.lean`.
3. Derive
   `continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal` by
   composition:

```lean
let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
let L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  toFin1.comp (SchwartzMap.fourierTransformCLM ℂ)
exact
  L.continuous.comp
    ((continuous_schwartzPsiZ_twoPi_horizontal hε).comp e1.continuous)
```

4. Prove the growth helper by the same seminorm-bound pattern as
   `SCV.schwartzCLM_seminorm_horizontal_growth` in
   [FourierLaplaceCore.lean](/Users/xiyin/OSReconstruction/OSReconstruction/SCV/FourierLaplaceCore.lean),
   but with target space `SchwartzMap (Fin 1 → ℝ) ℂ`:

```lean
let L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  toFin1.comp (SchwartzMap.fourierTransformCLM ℂ)
let q : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
  (schwartzSeminormFamily ℂ (Fin 1 → ℝ) ℂ (k, n)).comp L.toLinearMap
have hq_cont : Continuous q := by
  change Continuous (fun φ : SchwartzMap ℝ ℂ =>
    schwartzSeminormFamily ℂ (Fin 1 → ℝ) ℂ (k, n) (L φ))
  exact
    ((schwartz_withSeminorms ℂ (Fin 1 → ℝ) ℂ).continuous_seminorm
      (k, n)).comp L.continuous
obtain ⟨s, D, hD_ne, hq_bound⟩ :=
  Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq_cont
```

   Then finish exactly as `SCV.schwartzCLM_seminorm_horizontal_growth` does,
   using `SCV.schwartzPsiZ_seminorm_horizontal_bound` on the real-line family
   with horizontal height `2 * Real.pi * ε` and real coordinate
   `2 * Real.pi * e1 x1`. The final polynomial rewrite uses continuity of
   `e1` to dominate `|e1 x1|` by a constant multiple of `‖x1‖`, then absorbs
   constants into `C` and `N`. If this final norm-domination step is not
   already a local `simp` consequence of `ContinuousLinearEquiv.funUnique`,
   the only permitted auxiliary lemma is:

```lean
private theorem funUnique_abs_le_norm
    (x1 : Fin 1 → ℝ) :
    |(ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) x1| ≤ ‖x1‖ := by
  simpa [Real.norm_eq_abs] using (norm_le_pi_norm x1 0)
```

   No OS, Wightman, quotient, or semigroup object may appear in this growth
   helper or its auxiliaries.

Implementation-readiness gate for the normal-form helper:

The old descended-quotient statement
`bvt_F_canonical_xiShift_shell_eq_integrated_descendedPsiZ_of_section43Transport`
is now only a proof-presentation variant of the withdrawn finite-height
`TW/ψ_Z` scalar normal form. It must not be implemented first, because the
descended quotient layer can hide exactly the scalar mismatch this audit
exposed. The words "rewrite by the ordered-product split" are not a proof; if
this theorem is ever revived, they must be replaced by a new explicit analytic
continuation lemma for the oscillatory/Laplace exponential mismatch.

The following local normal form is retained only as the withdrawn finite-height
draft. It is not the next Lean theorem on the corrected route.

```lean
private theorem
    bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact
    (∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I) *
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) y) =
    ∫ x : ℝ,
      TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

Finite-height audit correction: this theorem was temporarily treated as the
non-subtractive scalar normal form feeding the transported residual. The
fixed-`x` expansion audit below shows that this is still too strong: it would
identify an oscillatory real-time shell factor with a Laplace-damped
positive-energy factor at finite height. Therefore the theorem is now
withdrawn as an implementation target unless a new explicit analytic
continuation lemma first bridges that factor mismatch. In the old draft, the
larger displayed helper was then obtained formally:

1. rewrite its left side by
   `(bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift ... t ε).symm`;
2. apply
   `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ`;
3. rewrite the right side pointwise by
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` using the local
   `TW` and `hTW`.

Historical proof transcript for the withdrawn theorem
`bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ`:

1. Introduce `ψZt`, `ψZxε x`, `TW`, `hTW`, `rψ`, and
   `r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩`. The positivity proof
   for `ψZxε x` is `mul_pos Real.two_pi_pos (by simpa using hε)`. The
   positivity proof for `ψZt` is `mul_pos Real.two_pi_pos ht`.
   The one-sided support witness for the local time-shift functional is exactly

```lean
have hTW :
    SCV.HasOneSidedFourierSupport TW := by
  simpa [TW] using
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
      (d := d) OS lgc hm φ ψ hψ_compact
```

   Use this `hTW` only when expanding the Section-4.3 descended
   one-variable quotient class. It is not a replacement for the scalar
   time-interchange proof.
2. Do not prove any fresh `xiShift` algebra inside this theorem. If the proof
   enters the existing shell/Fourier-Laplace Fubini packet, rewrite the left
   side by the already-proved configuration-space theorem
   `bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift`; treat that step as
   algebra only, not as analytic comparison. The hard comparison begins only
   after the shell has been expanded to a one-variable Section-4.3 scalar.
   After `TW` has been introduced, the right side may always be unfolded by

```lean
have hTW_apply :
    ∀ χ : SchwartzMap ℝ ℂ,
      TW χ =
        ∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          χ τ := by
  intro χ
  simpa [TW] using
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
      (d := d) OS lgc φ ψ hψ_compact χ
```

   The finite-height residual proof uses `hTW_apply` pointwise under the
   outer `x`-integral, with
   `χ := (SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)`. It should not unfold
   the chosen tempered functional any earlier.
3. Apply `partialFourierSpatial_fun_eq_integral` to the left and right
   configuration factors before any Section-4.3 quotient rewrite. Spatial
   constants may be rewritten only by `partialFourierSpatial_fun_eq_integral`,
   `partialFourierSpatial_fun_eq_integral_realProd`, and
   `physicsFourierFlatCLM_integral`.
4. Frozen-slice coordinate packet. After the product/time-shift split, the
   variables feeding a slice bridge must be organized as follows:

```lean
let rψ : Fin m := ⟨0, hm⟩

-- `rφ` is not fixed by the tail-shift convention. It is the left-factor
-- one-variable slice chosen by the current frozen integrand.
variable (rφ : Fin n)

-- Full time vectors after applying `nPointTimeSpatialCLE` to the split factors.
variable (aφ : Fin n → ℝ)
variable (aψ : Fin m → ℝ)

-- Frozen maps are the full vectors themselves; evaluating at their selected
-- coordinate recovers the original partial-Fourier value by `Function.update`.
let tφ : Fin n → ℝ := aφ
let tψ : Fin m → ℝ := aψ
let sφ : ℝ := tφ rφ
let sψ : ℝ := tψ rψ
```

   The corresponding self-update rewrites are mandatory local normal forms:

```lean
have hφ_update :
    Function.update tφ rφ sφ = tφ := by
  ext i
  by_cases hi : i = rφ
  · subst hi
    simp [sφ]
  · simp [sφ, hi]

have hψ_update :
    Function.update tψ rψ sψ = tψ := by
  ext i
  by_cases hi : i = rψ
  · subst hi
    simp [sψ]
  · simp [sψ, hi]
```

   Hence the exact slice-to-full-time rewrites are:

```lean
have hφ_slice_eval :
    partialFourierSpatial_timeSliceSchwartz
        (d := d) (n := n) φ rφ tφ ξφ sφ =
      OSReconstruction.partialFourierSpatial_fun
        (d := d) (n := n) φ (tφ, ξφ) := by
  simp [partialFourierSpatial_timeSliceSchwartz, sφ, hφ_update]

have hψ_slice_eval :
    partialFourierSpatial_timeSliceSchwartz
        (d := d) (n := m) ψ rψ tψ ξψ sψ =
      OSReconstruction.partialFourierSpatial_fun
        (d := d) (n := m) ψ (tψ, ξψ) := by
  simp [partialFourierSpatial_timeSliceSchwartz, sψ, hψ_update]
```

   Do not set `rφ := 0`, `rφ := Fin.last _`, or any other special left index
   unless a later expansion theorem explicitly produces that choice. The
   existing transport lemmas are generic in `rφ`, and the only fixed coordinate
   forced by the live shell is `rψ = 0` on the right factor.

   Important zero-arity branch: this packet is only available in the branch
   `hn : 0 < n`. The live theorem surface has only `hm : 0 < m`, so the
   eventual proof must start with:

```lean
by_cases hn : 0 < n
```

   In the `hn` branch, choose or bind `rφ : Fin n` and use the four slice
   bridge lemmas displayed below. In the `¬ hn` branch, `n = 0`, so no
   `rφ : Fin n` exists and no left one-variable slice theorem can be
   instantiated. That branch must be discharged by a separate zero-left
   quotient lemma:

```lean
private theorem section43_zero_left_repr_eq_transport_pointwise
    {φ : SchwartzNPoint d 0}
    {f : euclideanPositiveTimeSubmodule (d := d) 0}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        os1TransportComponent d 0 f) :
    φ = (EuclideanPositiveTimeComponent.ofSubmodule f).1 := by
  ext x
  have hq :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        section43PositiveEnergyQuotientMap (d := d) 0 f.1 := by
    simpa [os1TransportComponent_apply] using hφf
  have hEqOn :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := 0) hq
  exact hEqOn (by intro i; exact Fin.elim0 i)
```

   The proof is not a new analytic ingredient: `section43PositiveEnergyRegion
   d 0` is the whole zero-point domain because the `Fin 0` time condition is
   vacuous, so the quotient equality gives pointwise equality on the unique
   zero-point configuration. If Lean does not already expose this as a local
   simp consequence of `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
   this exact zero-left lemma is the only permitted auxiliary for the `n = 0`
   branch. Do not add a `0 < n` hypothesis to the main theorem.
5. The slice-pairing expansion must expose only these four one-variable
   Schwartz functions for frozen data `rφ tφ ξφ rψ tψ ξψ`:

```lean
let φSlice :=
  partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ
let ψSlice :=
  partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ
let fSlice :=
  partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
    (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ
let gSlice :=
  partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
    (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ
```

   The only allowed transport rewrites at this level are:

```lean
fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
  (d := d) (n := n) (m := m) hφf
  rφ tφ htφ ξφ rψ tψ htψ ξψ

fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
  (d := d) (n := n) (m := m) hφf hψg
  rφ tφ htφ ξφ rψ tψ htψ ξψ
```

   After these rewrites, no ambient slice `φSlice` or `ψSlice` may remain in
   the surviving scalar. If one remains, the slice expansion is incomplete and
   the proof must return to this document.
6. Time-shift quotient caveat. The Section-4.3 quotient equalities
   `hφf` and `hψg` compare the **unshifted** ambient representatives with their
   positive-time preimages on the nonnegative time region. They do not commute
   for free with the real-time shift on the right factor:

```lean
timeShiftSchwartzNPoint (d := d) t ψ x =
  ψ (fun i => x i - timeShiftVec d t)
```

   Therefore, for `0 < t`, equality of `ψ` and `g.1` on nonnegative
   configurations does **not** imply equality of
   `timeShiftSchwartzNPoint t ψ` and `timeShiftSchwartzNPoint t g` on the
   Section-4.3 nonnegative region: the shifted preimage point
   `x i - timeShiftVec d t` can have negative time. The support theorem
   `timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg` proves
   only that a shifted **positive-time preimage** still has ordered positive
   support; it does not justify replacing a shifted ambient representative by
   the shifted preimage representative.

   Consequence: the full-orthant packet below is only an unshifted local
   slice-descent tool. It may be used after the shell/Paley-Wiener expansion has
   separated the real-time shift into the external one-variable `ψ_Z` kernel
   and exposed unshifted Section-4.3 slice representatives. It must never be
   used to prove a pointwise equality involving
   `φ.conjTensorProduct (timeShiftSchwartzNPoint t ψ)` by replacing the shifted
   `ψ` directly. The actual shifted comparison has to be a
   positive-support time-shift distribution theorem, i.e. an equality of the
   descended one-variable pairing against `ψ_Z`, not an equality of shifted
   representatives.
7. Tail-gap gate before any frozen slice theorem is used. The hypotheses
   `htφ` and `htψ` for the one-variable transport lemmas are **not** produced
   by the slice support theorem and must not be assumed for arbitrary frozen
   background data. They are available only after the current integrand has
   already been restricted to positive cumulative tail gaps and those gaps have
   been converted to full nonnegative absolute time vectors on the corresponding
   factor:

```lean
have hφ_nonneg : ∀ i : Fin n, 0 ≤ tφ i := by
  -- In the live instantiation:
  --   tφ = absTimesOfTailGapsSplitLeft (n := n) (m := m) u
  exact absTimesOfTailGapsSplitLeft_nonneg (n := n) (m := m) hu i

have hψ_nonneg : ∀ i : Fin m, 0 ≤ tψ i := by
  -- In the live instantiation:
  --   tψ = absTimesOfTailGapsSplitRight (n := n) (m := m) u
  exact absTimesOfTailGapsSplitRight_nonneg (n := n) (m := m) hu i

have htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i := by
  intro i hi
  exact hφ_nonneg i

have htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i := by
  intro i hi
  exact hψ_nonneg i
```

   These obligations are **not** supplied by `ht`, `hε`, `hf_compact`, or
   `hg_compact`. They are also not the support theorem
   `tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`:
   that theorem gives one-sided Fourier support for positive-time preimage
   slices, while `htφ` and `htψ` are the separate nonnegative-background-time
   assumptions needed to move ambient representatives to their positive-time
   preimages on the Section-4.3 quotient surface.

   Therefore the next unshifted local theorem before the frozen-slice scalar
   bridge is a **full absolute-time adapter packet**, not another one-variable
   wrapper. This packet supplies the nonnegative-background hypotheses for
   unshifted slice representatives only after the global tail-gap descent has
   produced them; it is not the shifted `ψ` comparison.
   The packet has two local facts that are already implementation-level from
   current code:

```lean
private theorem partialFourierSpatial_fun_eq_of_repr_eq_transport_on_nonneg
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (τ : Fin n → ℝ)
    (hτ : ∀ i : Fin n, 0 ≤ τ i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) φ (τ, ξ) =
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 (τ, ξ) := by
  have hregion :
      Set.EqOn (φ : NPointDomain d n → ℂ)
        ((f : euclideanPositiveTimeSubmodule (d := d) n) :
          NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) := by
    have hq :
        section43PositiveEnergyQuotientMap (d := d) n φ =
          section43PositiveEnergyQuotientMap (d := d) n f.1 := by
      simpa [os1TransportComponent_apply] using hφf
    exact eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) (f := φ) (g := f.1) hq
  exact
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n) hregion τ hτ ξ

private theorem partialFourierSpatial_fun_eq_zero_of_not_nonneg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (τ : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (hneg : ∃ r : Fin n, τ r < 0) :
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1 (τ, ξ) = 0 := by
  obtain ⟨r, hr⟩ := hneg
  let s : ℝ := τ r
  have hupdate : Function.update τ r s = τ := by
    ext i
    by_cases hi : i = r
    · subst hi
      simp [s]
    · simp [s, hi]
  simpa [s, hupdate] using
    partialFourierSpatial_fun_eq_zero_of_neg_time
      (d := d) (n := n) f r τ ξ hr
```

   The Lean-ready full-orthant slice adapter is:

```lean
private theorem
    unshifted_full_timeOrthant_descended_pairing_eq_of_section43Transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n} {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n) (tφ : Fin n → ℝ)
    (hφ_nonneg : ∀ i : Fin n, 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m → ℝ)
    (hψ_nonneg : ∀ i : Fin m, 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ)) := by
  have htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i := by
    intro i _
    exact hφ_nonneg i
  have htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i := by
    intro i _
    exact hψ_nonneg i
  exact
    fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
      (d := d) (n := n) (m := m) hφf hψg
      rφ tφ htφ ξφ rψ tψ htψ ξψ
```

   This adapter is not the global support theorem. It merely packages the
   already-proved one-variable slice bridge once the proof has a full
   nonnegative absolute time vector. The tail-gap theorem
   `bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant`
   displayed below remains a useful special case, but the live Section-4.3
   hard theorem now consumes the more general Fourier-side support statement
   `tflat_pairing_eq_of_eqOn_dualCone`. The
   Positivity-side expanded normal form must instantiate the full-kernel
   `KAmbient`, `KTransport`, and dual-cone EqOn hypothesis only after the
   time-shift has already been moved into the one-variable Paley-Wiener kernel.
   It is **not** valid to integrate the one-variable slice lemmas over arbitrary
   background times, and it is also **not** valid to apply this packet directly
   to a shifted ambient
   representative.

   Important support-interface correction. The global support theorem must not
   be phrased as a direct application of
   `SCV.hasFourierSupportIn_eqOn` to restrict primal frozen time variables.
   That theorem is a **frequency-side** equality principle for a distribution
   already supported in `DualConeFlat C`; production uses it, for example, to
   remove a dual-cone cutoff that is equal to `1` on `DualConeFlat C`.
   It does not by itself say that a configuration/time test can be replaced by
   its restriction to the nonnegative time orthant.

   The correct Lean shape mirrors the already-compiled one-variable theorem
   `hasOneSidedFourierSupport_bvt_W_conjTensorProduct_timeShift`: first derive
   an appropriate one-/multi-sided Fourier-support statement from the full
   flattened `Tflat` package, then use the resulting Fourier-support pairing
   theorem to prove dependence only on the nonnegative time region. In other
   words, the orthant descent theorem is the multivariable analogue of
   `SCV.fourier_pairing_eq_of_eqOn_nonneg`, not a naked call to
   `SCV.hasFourierSupportIn_eqOn`.

   Coordinate correction for that descent. The primitive one-sided variables
   are **cumulative tail-gap variables**, not independent absolute time
   coordinates. This follows from the same `xiShift` convention recorded
   above: changing one difference coordinate shifts all later absolute
   coordinates. Therefore the global support theorem must first restrict the
   expanded kernel to the positive **tail-gap sector** and only then convert
   those nonnegative gaps to nonnegative absolute time vectors for the
   Section-4.3 adapter.

   The support geometry needed for implementation is the following finite
   family of tail directions:

```lean
def flatTailTimeShiftDirection (d q : ℕ) (j : Fin q) :
    Fin (q * (d + 1)) → ℝ :=
  fun a =>
    if j.val ≤ (finProdFinEquiv.symm a).1.val ∧
        (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1)) then
      (-1 : ℝ)
    else
      0

@[simp] theorem flatTailTimeShiftDirection_zero
    {q : ℕ} (hq : 0 < q) :
    flatTailTimeShiftDirection d q ⟨0, hq⟩ =
      flatTimeShiftDirection d q := by
  ext a
  simp [flatTailTimeShiftDirection, flatTimeShiftDirection]
```

Lean status, 2026-04-13: `flatTailTimeShiftDirection` and the
`@[simp]` theorem `flatTailTimeShiftDirection_zero` are implemented in
`OSToWightmanBoundaryValueLimits.lean` and exact-checked. They are public
production declarations, so downstream files may use the direction and its
`j = 0` reduction.

   The sign lemma generalizes the existing
   `flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone`. For each tail
   index `j`, dual-cone membership implies
   `∑_{i ≥ j} ξ_{i,0} ≥ 0`, hence the negative tail-shift direction pairs
   nonpositively:

```lean
private theorem flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {q : ℕ} (j : Fin q)
    {ξ : Fin (q * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat ((flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q)) :
    ∑ a, flatTailTimeShiftDirection d q j a * ξ a ≤ 0
```

Lean status, 2026-04-13: this theorem is implemented in
`OSToWightmanBoundaryValueLimits.lean` and exact-checked by

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean
```

The implementation uses the Lean order `k < j` on `Fin q` for the before-jump
branch. This is definitionally friendlier than repeatedly normalizing
`k.val < j.val`; the final `flatTailTimeShiftDirection` sum is still rewritten
from the theorem's `j.val ≤ k.val` condition to the complementary `¬ k < j`
branch.

Visibility guard after the production audit: the sign theorem is currently
private in `OSToWightmanBoundaryValueLimits.lean`. That is correct for the
chosen support-packet implementation, because the dual-cone sign argument is
used internally to prove the public theorem
`bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant`. Do not
duplicate this proof in `OSToWightmanPositivity.lean`. If a later full-kernel
EqOn proof genuinely needs the sign theorem outside BVLimits, first promote
this exact theorem to a public declaration; do not copy the proof or recreate a
second theorem with a wrapper-shaped name.

   Proof transcript for `flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone`:

   1. Work classically and set
      `S : ℝ := ∑ k : Fin q, (if j.val ≤ k.val then 1 else 0) *
        ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))`.
   2. Prove `hS_nonneg : 0 ≤ S` by contradiction. If `S < 0`, set
      `W : ℝ := ∑ k : Fin q,
        (if k.val < j.val then (k : ℝ) + 1 else (k : ℝ)) *
        ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))` and
      `ε := (-S) / (2 * (|W| + 1))`; then `0 < ε`.
   3. Define the pure-time test point
      `yε : Fin q → Fin (d + 1) → ℝ` by
      `yε k μ = 0` for `μ ≠ 0`, and
      `yε k 0 = if k.val < j.val then ((k : ℝ) + 1) * ε
        else 1 + (k : ℝ) * ε`.
   4. Prove `yε ∈ ForwardConeAbs d q`.
      For `k = 0`, the first difference is either `ε • e0` if `0 < j.val`
      or `1 • e0` if `j.val = 0`; both are in `InOpenForwardCone d`.
      For `k > 0`, the successive difference is:
      `ε • e0` when both `k-1` and `k` are on the same side of `j`;
      `1 • e0` when `k.val = j.val`; again both are in the open forward cone.
      The required scalar equalities are the same `Nat.sub_add_cancel` and
      `nlinarith` arithmetic used in the existing
      `flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone` proof.
   5. Apply `mem_dualConeFlat.mp hξ` to
      `(flattenCLEquivReal q (d + 1)) yε`, obtaining
      `0 ≤ ∑ a, (flattenCLEquivReal q (d + 1) yε) a * ξ a`.
   6. Rewrite that sum with `sum_over_flat_timeSlots` as `S + ε * W`.
      The coefficient of `S` is the indicator `j.val ≤ k.val`; the remaining
      time-slot coefficient is `(k : ℝ) + 1` before the jump and `(k : ℝ)`
      after the jump, exactly as in the definition of `W`. Do not use the
      old `j = 0` choice `W = ∑ k, (k : ℝ) * ξ_k`; that misses the
      pre-jump `+1` terms and would not justify the displayed `yε` for
      arbitrary `j`.
   7. Prove `ε * W ≤ (-S) / 2` exactly as in the existing proof:
      `ε * W ≤ ε * |W|`,
      `ε * |W| = ((-S) / 2) * (|W| / (|W| + 1))`, and
      `|W| / (|W| + 1) ≤ 1`.
   8. The inequalities `0 ≤ S + ε * W`, `ε * W ≤ -S / 2`, and `S < 0`
      contradict by `linarith`.
   9. Finally rewrite
      `∑ a, flatTailTimeShiftDirection d q j a * ξ a` with
      `sum_over_flat_timeSlots` using the coefficient
      `fun k => if j.val ≤ k.val then (-1 : ℝ) else 0`; the result is `-S`,
      hence nonpositive by `hS_nonneg`.

   The right-block version used by the actual `φ ⊗ ψ` flattened surface should
   be derived by vector equality, not reproved from scratch.

   Implementation note, 2026-04-13: a naive
   `ext a; simp [flatTailTimeShiftDirection, zeroHeadBlockShift]` attempt is
   **not** implementation-ready. Lean exposes the cast/reindex coordinates as
   `a / (d+1)` and `a.modNat`, so the equality must follow the compiled
   split-block pattern already used by
   `zeroHeadBlockShift_flatTimeShiftDirection_pairing_eq_neg_tailTimeSum`:

   1. Define
      `xSplit := zeroHeadBlockShift (m := n*(d+1)) (n := m*(d+1))
        (flatTailTimeShiftDirection d m j)`.
   2. Define
      `vEff := (castFinCLE (by ring : (n+m)*(d+1)=n*(d+1)+m*(d+1))).symm xSplit`
      and `y := (flattenCLEquivReal (n+m) (d+1)).symm vEff`.
   3. Reuse `splitFirst_reindex_flatten_symm_eq` to prove
      `splitFirst n m y = 0`.
   4. Reuse `splitLast_reindex_flatten_symm_eq` to prove
      `splitLast n m y =
        (flattenCLEquivReal m (d+1)).symm (flatTailTimeShiftDirection d m j)`.
   5. Prove the full coordinate formula

```lean
have hy_formula :
  ∀ k : Fin (n + m), ∀ μ : Fin (d + 1),
    y k μ =
      if μ = 0 then
        if (k : ℕ) < n + j.val then 0 else (-1 : ℝ)
      else 0 := by
  intro k μ
  by_cases hk_head : (k : ℕ) < n
  · -- use `hsplitFirst`; RHS is `0` since `k < n ≤ n+j.val`
  · -- set `r : Fin m := ⟨(k : ℕ) - n, by omega⟩`
    -- use `hsplitLast`
    -- prove `j ≤ r ↔ n + j.val ≤ k.val` by `Fin.ext`/`omega`
```

      Lean-ready expansion of the two branches:

```lean
    · let k' : Fin n := ⟨k, hk_head⟩
      have hk_cast : Fin.castAdd m k' = k := by
        apply Fin.ext
        simp [k']
      have hval : y k μ = 0 := by
        have h := congrArg
          (fun z : Fin n → Fin (d + 1) → ℝ => z k') hsplitFirst
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [k', hk_cast] using h'
      have hk_lt_tail : (k : ℕ) < n + j.val := by omega
      simp [hval, hk_lt_tail]
    · let r : Fin m := ⟨(k : ℕ) - n, by omega⟩
      have hk_tail : Fin.natAdd n r = k := by
        apply Fin.ext
        simp [r, Fin.natAdd]
        omega
      have hval :
          y k μ =
            ((flattenCLEquivReal m (d + 1)).symm
              (flatTailTimeShiftDirection d m j)) r μ := by
        have h := congrArg
          (fun z : Fin m → Fin (d + 1) → ℝ => z r) hsplitLast
        have h' := congrArg (fun f : Fin (d + 1) → ℝ => f μ) h
        simpa [splitLast, r, hk_tail] using h'
      have htail_formula :
          ((flattenCLEquivReal m (d + 1)).symm
              (flatTailTimeShiftDirection d m j)) r μ =
            if μ = 0 then
              if j.val ≤ r.val then (-1 : ℝ) else 0
            else 0 := by
        change flatTailTimeShiftDirection d m j (finProdFinEquiv (r, μ)) = _
        simp [flatTailTimeShiftDirection]
      have htail_iff : j.val ≤ r.val ↔ n + j.val ≤ (k : ℕ) := by
        dsimp [r]
        omega
      have hfull_iff :
          ¬ ((k : ℕ) < n + j.val) ↔ n + j.val ≤ (k : ℕ) := by
        omega
      simp [hval, htail_formula, htail_iff, hfull_iff]
```

   6. Convert `hy_formula` back through
      `flattenCLEquivReal.apply_symm_apply`, exactly as in the existing
      zero-head full-tail proof, obtaining

```lean
have hvEff_formula :
  ∀ a,
    vEff a =
      if (finProdFinEquiv.symm a).2 = 0 then
        if ((finProdFinEquiv.symm a).1 : Fin (n + m)).val < n + j.val
        then 0 else (-1 : ℝ)
      else 0
```

      The corresponding Lean block is:

```lean
have hvEff_formula :
    ∀ a,
      vEff a =
        if (finProdFinEquiv.symm a).2 = 0 then
          if ((finProdFinEquiv.symm a).1 : Fin (n + m)).val < n + j.val
          then 0 else (-1 : ℝ)
        else 0 := by
  intro a
  have hv :
      (flattenCLEquivReal (n + m) (d + 1) y) a = vEff a := by
    simpa [y] using
      congrArg (fun z : Fin ((n + m) * (d + 1)) → ℝ => z a)
        ((flattenCLEquivReal (n + m) (d + 1)).apply_symm_apply vEff)
  rw [← hv]
  simpa [flattenCLEquivReal_apply] using
    hy_formula (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2
```

   7. Use `hvEff_formula` to prove the vector equality below. The final
      `ext a` proof should not unfold `zeroHeadBlockShift`; it compares the
      `hvEff_formula` branch with the target `flatTailTimeShiftDirection`
      branch after the `Fin.natAdd` value simplification:

```lean
  ext a
  rw [hvEff_formula a]
  by_cases hμ : (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
  · simp [flatTailTimeShiftDirection, hμ, Fin.natAdd]
    constructor <;> intro h
    · omega
    · omega
  · simp [flatTailTimeShiftDirection, hμ]
```

      If `simp [Fin.natAdd]` leaves the target as
      `(Fin.natAdd n j).val ≤ ((finProdFinEquiv.symm a).1).val`, insert

```lean
have hnatAdd : ((Fin.natAdd n j : Fin (n + m)) : ℕ) = n + j.val := by
  simp [Fin.natAdd]
```

      and rewrite by `hnatAdd` before the `omega` split. Only then should
      the sign corollary rewrite to the already checked base lemma.

```lean
private theorem zeroHeadBlockShift_flatTailTimeShiftDirection_eq
    {n m : ℕ} (j : Fin m) :
    (OSReconstruction.castFinCLE
      (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
      (OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := m * (d + 1))
        (flatTailTimeShiftDirection d m j)) =
      flatTailTimeShiftDirection d (n + m) (Fin.natAdd n j) := by
  -- Do not use bare `simp`; use the split-block coordinate proof above.

private theorem zeroHeadBlockShift_flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {n m : ℕ} (j : Fin m)
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    ∑ a,
      (((OSReconstruction.castFinCLE
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTailTimeShiftDirection d m j))) a) * ξ a ≤ 0 := by
  rw [zeroHeadBlockShift_flatTailTimeShiftDirection_eq]
  exact flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    (d := d) (q := n + m) (j := Fin.natAdd n j) hξ
```

   The multi-gap positive sector is then:

```lean
def positiveGapOrthant (q : ℕ) : Set (Fin q → ℝ) :=
  {u | ∀ j : Fin q, 0 ≤ u j}

def absTimesOfTailGaps {q : ℕ} (u : Fin q → ℝ) : Fin q → ℝ :=
  fun i => ∑ j : Fin q, if j.val ≤ i.val then u j else 0

theorem absTimesOfTailGaps_nonneg
    {q : ℕ} {u : Fin q → ℝ}
    (hu : u ∈ positiveGapOrthant q) :
    ∀ i : Fin q, 0 ≤ absTimesOfTailGaps u i := by
  intro i
  dsimp [absTimesOfTailGaps, positiveGapOrthant] at hu ⊢
  exact Finset.sum_nonneg (by
    intro j _
    by_cases hj : j.val ≤ i.val
    · simpa [hj] using hu j
    · simp [hj])

noncomputable def absTimesOfTailGapsSplitLeft
    {n m : ℕ} (u : Fin (n + m) → ℝ) : Fin n → ℝ :=
  fun i => absTimesOfTailGaps u (Fin.castAdd m i)

noncomputable def absTimesOfTailGapsSplitRight
    {n m : ℕ} (u : Fin (n + m) → ℝ) : Fin m → ℝ :=
  fun j => absTimesOfTailGaps u (Fin.natAdd n j)

noncomputable def absTimesOfTailGapsSplitLeftRev
    {n m : ℕ} (u : Fin (n + m) → ℝ) : Fin n → ℝ :=
  fun i => absTimesOfTailGapsSplitLeft (n := n) (m := m) u (Fin.rev i)

theorem absTimesOfTailGapsSplitLeft_nonneg
    {n m : ℕ} {u : Fin (n + m) → ℝ}
    (hu : u ∈ positiveGapOrthant (n + m)) :
    ∀ i : Fin n, 0 ≤ absTimesOfTailGapsSplitLeft (n := n) (m := m) u i := by
  intro i
  exact absTimesOfTailGaps_nonneg (q := n + m) hu (Fin.castAdd m i)

theorem absTimesOfTailGapsSplitRight_nonneg
    {n m : ℕ} {u : Fin (n + m) → ℝ}
    (hu : u ∈ positiveGapOrthant (n + m)) :
    ∀ j : Fin m, 0 ≤ absTimesOfTailGapsSplitRight (n := n) (m := m) u j := by
  intro j
  exact absTimesOfTailGaps_nonneg (q := n + m) hu (Fin.natAdd n j)

theorem absTimesOfTailGapsSplitLeftRev_nonneg
    {n m : ℕ} {u : Fin (n + m) → ℝ}
    (hu : u ∈ positiveGapOrthant (n + m)) :
    ∀ i : Fin n, 0 ≤ absTimesOfTailGapsSplitLeftRev (n := n) (m := m) u i := by
  intro i
  exact absTimesOfTailGapsSplitLeft_nonneg (n := n) (m := m) hu (Fin.rev i)

def firstRightComponent {m : ℕ} (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

def firstRightIndex {n m : ℕ} (hm : 0 < m) : Fin (n + m) :=
  ⟨n, Nat.lt_add_of_pos_right hm⟩
```

   Public/private guard. These gap-sector definitions and nonnegativity
   theorems must be public if they live in
   `OSToWightmanBoundaryValueLimits.lean`, because the Positivity-side
   instantiation has to state and prove
   `Set.EqOn ... (positiveGapOrthant (n + m))`. Keep only proof-local
   reindexing and padding helpers private.

   Thus the global descent theorem must say "agreement on the positive
   tail-gap sector" rather than "agreement on arbitrary independent absolute
   time coordinates." This is stronger than needed for Section 4.3 in the
   right way: if `u ∈ positiveGapOrthant (n + m)`, then
   `absTimesOfTailGapsSplitLeft u`,
   `absTimesOfTailGapsSplitRight u`, and, when `φ.borchersConj` exposes the
   left factor, `absTimesOfTailGapsSplitLeftRev u` are all nonnegative. The
   local adapter receives its `hφ_nonneg` and `hψ_nonneg` hypotheses by these
   displayed cumulative-sum lemmas, not by support of the one-variable slices.

   The SCV support step required for the multi-gap theorem is a finite-dimensional
   version of the one-variable phase evaluation:

```lean
theorem inverseFourierFlatCLM_integral_eval
    {q : ℕ}
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (p : Fin q → ℝ) :
    ∫ u : Fin q → ℝ,
      Complex.exp (2 * Real.pi * Complex.I *
        (∑ j, (p j : ℂ) * (u j : ℂ))) *
        inverseFourierFlatCLM χ u =
      χ p

private theorem integral_tailGap_phase_mul_inverseFourierFlat_eq_eval
    {q : ℕ}
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (lam : Fin q → ℝ) :
    ∫ u : Fin q → ℝ,
      Complex.exp (-(Complex.I *
        ((∑ j, (lam j : ℂ) * (u j : ℂ))))) *
        inverseFourierFlatCLM χ u =
      χ (fun j => -lam j / (2 * Real.pi))

private theorem integral_tailGap_phase_mul_inverseFourierFlat_eq_zero_of_eqOn_positiveGapOrthant
    {q : ℕ}
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (hχ_zero :
      Set.EqOn (χ : (Fin q → ℝ) → ℂ) 0 (positiveGapOrthant q))
    {lam : Fin q → ℝ}
    (hlam : ∀ j : Fin q, lam j ≤ 0) :
    ∫ u : Fin q → ℝ,
      Complex.exp (-(Complex.I *
        ((∑ j, (lam j : ℂ) * (u j : ℂ))))) *
        inverseFourierFlatCLM χ u = 0 := by
  rw [integral_tailGap_phase_mul_inverseFourierFlat_eq_eval (χ := χ) lam]
  exact hχ_zero (fun j => -lam j / (2 * Real.pi)) (by
    intro j
    exact div_nonneg (by linarith [hlam j]) Real.two_pi_pos.le)
```

   Proof transcript for `integral_tailGap_phase_mul_inverseFourierFlat_eq_eval`:

   1. First implement the non-OS Fourier helper
      `inverseFourierFlatCLM_integral_eval` in `SCV/PaleyWienerSchwartz.lean`
      near `inverseFourierFlatCLM`, `physicsFourierFlatCLM_apply`, and the
      private `fourierTransformFlat_eval`. This helper is the multivariable
      analogue of `fourierInv_eq_cexp_integral_local`, and it is the correct
      public surface for the gap variables.
   2. In that helper, set
      `e : EuclideanSpace ℝ (Fin q) ≃L[ℝ] (Fin q → ℝ) :=
        EuclideanSpace.equiv (Fin q) ℝ`.
      Let
      `χE := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e χ`.
      Use
      `FourierTransform.fourierInv_fourier_eq χE`, evaluated at `e.symm p`.
   3. Rewrite the Euclidean inverse Fourier value by
      `FourierTransform.fourierInv_eq'`, the multidimensional inverse formula

```lean
FourierTransform.fourierInv φ p =
  ∫ u, Complex.exp (2 * Real.pi * Complex.I *
    (∑ j, (p j : ℂ) * (u j : ℂ))) * φ u
```

      If Mathlib exposes this only on `EuclideanSpace`, copy the transport
      proof pattern from `fourierTransformFlat_eval`: use
      `(PiLp.volume_preserving_toLp (ι := Fin q)).integral_comp` and
      `PiLp.inner_apply`, then rewrite the inner product to
      `∑ j, p j * u j`.
   4. Transport back through the two
      `SchwartzMap.compCLMOfContinuousLinearEquiv` maps in the definition of
      `inverseFourierFlatCLM`. The final `simpa [inverseFourierFlatCLM]`
      should expose exactly the displayed flat integral.
   5. Then put `p : Fin q → ℝ := fun j => -lam j / (2 * Real.pi)` in
      `integral_tailGap_phase_mul_inverseFourierFlat_eq_eval`.
   6. Show the exponent equality pointwise:
      `2 * Real.pi * Complex.I * ∑ j, (p j : ℂ) * (u j : ℂ)
        = -(Complex.I * ∑ j, (lam j : ℂ) * (u j : ℂ))`.
      This is `rw [Finset.mul_sum]` followed by the scalar identity
      `(2 * Real.pi) * (-lam j / (2 * Real.pi)) = -lam j`.
   7. Rewrite by `inverseFourierFlatCLM_integral_eval (χ := χ) p`, then
      `rfl`/`simpa [p]`.

   This avoids an invalid partition-of-unity argument over the complement of
   the orthant. The proof uses direct multivariable Fourier inversion with the
   Mathlib-convention flat transform `inverseFourierFlatCLM`: a test that is
   zero on the positive gap sector evaluates to zero at the frequency point
   forced by the dual-cone sign inequalities. Do not replace this by
   `physicsFourierFlatCLM`; that would introduce the wrong normalization for
   the gap-test side. The spacetime flattened Wightman test still uses
   `physicsFourierFlatCLM`, exactly as in the existing `Tflat` representation.

   Fubini padding correction. The axiom
   `schwartz_clm_fubini_exchange` requires the parameter space dimension to
   match the Schwartz-space dimension of `Tflat`. In the existing one-variable
   proof this is why the real variable is inserted as the first coordinate of
   a full `Fin M → ℝ` test and all remaining coordinates are integrated against
   `normedUnitBumpSchwartzPi`. The multi-tail-gap proof must do the same for
   `q := n + m` gap variables inside
   `M := (n + m) * (d + 1)` flattened spacetime variables.

   Implementation correction, 2026-04-13. Do **not** prove the padding collapse
   by a raw call to `integral_fin_add_split` with an arbitrary multiplier `P`;
   that theorem requires an `Integrable` hypothesis. The Lean-ready proof uses
   the measure-preserving equivalence `MeasurableEquiv.finAddProd q r ℝ`,
   its `MeasureTheory.volume_preserving_finAddProd` theorem from
   `GeneralResults/FinProductIntegral.lean`, and then the unconditional
   factorized identity `MeasureTheory.integral_prod_mul`. If
   `OSToWightmanBoundaryValueLimits.lean` does not already import
   `OSReconstruction.GeneralResults.FinProductIntegral`, add that import
   before implementing the helper below.

   Required padding helper:

```lean
private noncomputable def tailGapPadSchwartz
    {q M : ℕ} (h : q ≤ M)
    (χ : SchwartzMap (Fin q → ℝ) ℂ) :
    SchwartzMap (Fin M → ℝ) ℂ :=
  OSReconstruction.reindexSchwartzFin (Nat.add_sub_of_le h)
    (χ.tensorProduct (normedUnitBumpSchwartzPi (M - q)))

private theorem tailGapPadSchwartz_apply
    {q M : ℕ} (h : q ≤ M)
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (x : Fin M → ℝ) :
    tailGapPadSchwartz h χ x =
      χ (fun j : Fin q =>
          ((OSReconstruction.castFinCLE (Nat.add_sub_of_le h).symm) x)
            (Fin.castAdd (M - q) j)) *
        normedUnitBumpSchwartzPi (M - q)
          (fun k : Fin (M - q) =>
            ((OSReconstruction.castFinCLE (Nat.add_sub_of_le h).symm) x)
              (Fin.natAdd q k)) := by
  simp [tailGapPadSchwartz, OSReconstruction.reindexSchwartzFin_apply,
    SchwartzMap.tensorProduct_apply]

private theorem tailGapPadSchwartz_integral_after_reindex
    {q r : ℕ}
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (P : (Fin q → ℝ) → ℂ) :
    (∫ z : Fin (q + r) → ℝ,
      P (fun j : Fin q => z (Fin.castAdd r j)) *
        (χ.tensorProduct (normedUnitBumpSchwartzPi r)) z) =
      ∫ u : Fin q → ℝ, P u * χ u := by
  -- Use `MeasurableEquiv.finAddProd q r ℝ` and
  -- `MeasureTheory.volume_preserving_finAddProd q r ℝ`, not
  -- `integral_fin_add_split`.
  -- After change of variables, `SchwartzMap.tensorProduct_apply` rewrites the
  -- integrand to `(P u * χ u) * normedUnitBumpSchwartzPi r v`.
  -- Then use `MeasureTheory.integral_prod_mul` and
  -- `integral_normedUnitBumpSchwartzPi r`, followed by `ring`.

private theorem tailGapPadSchwartz_integral
    {q M : ℕ} (h : q ≤ M)
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (P : (Fin q → ℝ) → ℂ) :
    (∫ x : Fin M → ℝ,
      P (fun j : Fin q => x (Fin.castLE h j)) *
        tailGapPadSchwartz h χ x) =
      ∫ u : Fin q → ℝ, P u * χ u
```

   Proof transcript for `tailGapPadSchwartz_integral`:

   1. Set `r := M - q` and
      `hadd : q + r = M := Nat.add_sub_of_le h`.
   2. Change variables by the local `integral_comp_castFinCLE_eq` with
      `hadd.symm`, reducing the left integral to a `Fin (q + r) → ℝ`
      integral. Keep the local function in the exact shape

```lean
fun z : Fin (q + r) → ℝ =>
  P (fun j : Fin q => z (Fin.castAdd r j)) *
    (χ.tensorProduct (normedUnitBumpSchwartzPi r)) z
```

      because this is the shape consumed by
      `tailGapPadSchwartz_integral_after_reindex`.
   3. Use `tailGapPadSchwartz_apply`, `OSReconstruction.reindexSchwartzFin_apply`,
      `OSReconstruction.castFinCLE_symm_apply`, and
      `SchwartzMap.tensorProduct_apply` only to reach that exact after-reindex
      helper shape. Do not unfold `normedUnitBumpSchwartzPi`.
   4. Apply `tailGapPadSchwartz_integral_after_reindex`.
   5. No support or QFT input is used in this helper. If Lean does not solve
      the reindexing by `simp`, copy the existing `hPair_repr` proof in
      `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`
      with `tailGapPadSchwartz_integral_after_reindex` replacing
      `integral_finSucc_cons_eq`.

   The same helper is used twice in the `hΦ_vanish` proof: once to identify
   the padded `Tflat` pairing integral with the genuine `q`-gap pairing, and
   once pointwise to rewrite the Fubini-exchanged `Φ ξ` as the `q`-gap phase
   integral evaluated by
   `integral_tailGap_phase_mul_inverseFourierFlat_eq_zero_of_eqOn_positiveGapOrthant`.

   Implementation-location guard. The flattened witness
   `exists_flattened_bvt_W_dualCone_distribution` is currently private to
   `OSToWightmanBoundaryValueLimits.lean`. The existing right-block theorem
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`
   is the one-variable special case and is a proof pattern, not the correct
   primitive for the global Section-4.3 descent: the global theorem must
   translate the full flattened `(n + m)`-point test along all cumulative
   tail-gap directions. Therefore the tail-gap support theorem that needs
   direct access to the full `Tflat` witness must be proved/exported from
   `OSToWightmanBoundaryValueLimits.lean` (or from a small support companion
   that deliberately exposes a public, non-wrapper theorem).
   `OSToWightmanPositivity.lean` should consume only the resulting public
   tail-gap pairing/descent statement; it must not duplicate the `Tflat`
   reconstruction or attempt to rely on a private theorem from another module.

   Full flattened orbit. This is the public BVLimits theorem surface that
   should replace the schematic "global support" placeholder:

```lean
noncomputable def flatTailGapOrbit (d q : ℕ)
    (u : Fin q → ℝ) : Fin (q * (d + 1)) → ℝ :=
  ∑ j : Fin q, u j • flatTailTimeShiftDirection d q j

private theorem flatTailGapOrbit_pairing_nonpos_of_mem_dualCone
    {q : ℕ} (u : Fin q → ℝ)
    (hu : u ∈ positiveGapOrthant q)
    {ξ : Fin (q * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat ((flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q)) :
    ∑ a, flatTailGapOrbit d q u a * ξ a ≤ 0 := by
  calc
    ∑ a, flatTailGapOrbit d q u a * ξ a
        = ∑ j : Fin q,
            u j * (∑ a, flatTailTimeShiftDirection d q j a * ξ a) := by
            simp [flatTailGapOrbit, Finset.mul_sum, Finset.sum_mul,
              Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ 0 := by
        exact Finset.sum_nonpos (by
          intro j _
          have huj : 0 ≤ u j := by
            simpa [positiveGapOrthant] using hu j
          exact mul_nonpos_of_nonneg_of_nonpos huj
            (flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
              (d := d) (q := q) j hξ))

private theorem integrable_bvt_W_flattened_tailGapOrbit_mul_inverseFourierFlatCLM
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ)
    (χ : SchwartzMap (Fin q → ℝ) ℂ) :
    MeasureTheory.Integrable
      (fun u : Fin q → ℝ =>
        bvt_W OS lgc q
            (unflattenSchwartzNPoint (d := d)
              (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) *
          inverseFourierFlatCLM χ u)

theorem bvt_W_flattened_tailGapOrbit_pairing_eq_zero_of_eqOn_positiveGapOrthant
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ)
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (hχ_zero :
      Set.EqOn (χ : (Fin q → ℝ) → ℂ) 0 (positiveGapOrthant q)) :
    (∫ u : Fin q → ℝ,
      bvt_W OS lgc q
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) *
        inverseFourierFlatCLM χ u) = 0

theorem bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ)
    {χ₁ χ₂ : SchwartzMap (Fin q → ℝ) ℂ}
    (hχ :
      Set.EqOn (χ₁ : (Fin q → ℝ) → ℂ) χ₂ (positiveGapOrthant q)) :
    (∫ u : Fin q → ℝ,
      bvt_W OS lgc q
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) *
        inverseFourierFlatCLM χ₁ u) =
    (∫ u : Fin q → ℝ,
      bvt_W OS lgc q
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) *
        inverseFourierFlatCLM χ₂ u)
```

   Proof transcript for
   `integrable_bvt_W_flattened_tailGapOrbit_mul_inverseFourierFlatCLM`:

   1. Obtain `⟨Tflat, hTflat_supp, hTflat_repr⟩` from
      `exists_flattened_bvt_W_dualCone_distribution (d := d) OS lgc q`.
   2. Use continuity of `Tflat` and `Seminorm.bound_of_continuous` to get a
      finite seminorm control of `|Tflat F|`.
   3. Combine that control with
      `exists_bound_seminorm_physicsFourierFlatCLM_translate_flatTailGapOrbit`
      and `hTflat_repr` to prove a polynomial bound

```lean
have hpair_bound :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ u : Fin q → ℝ,
        ‖bvt_W OS lgc q
            (unflattenSchwartzNPoint (d := d)
              (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ))‖ ≤
          C * (1 + ‖u‖) ^ N
```

   4. Prove measurability of the pairing from
      `continuous_physicsFourierFlatCLM_translate_flatTailGapOrbit`,
      `Tflat.continuous`, and `hTflat_repr`.
   5. Apply `SCV.integrable_poly_growth_schwartz` from
      `SCV/LaplaceSchwartz.lean` to the polynomial-growth pairing and the
      Schwartz test `inverseFourierFlatCLM χ`. If this theorem is not already
      imported into `OSToWightmanBoundaryValueLimits.lean`, add
      `import OSReconstruction.SCV.LaplaceSchwartz` before the BVLimits proof
      work. This supplies the exact hypotheses required by
      `MeasureTheory.integral_sub` in the equality theorem.

   Proof transcript for
   `bvt_W_flattened_tailGapOrbit_pairing_eq_zero_of_eqOn_positiveGapOrthant`:

   1. Obtain `⟨Tflat, hTflat_supp, hTflat_repr⟩` from
      `exists_flattened_bvt_W_dualCone_distribution (d := d) OS lgc q`.
      Do not use the right-block witness here; it cannot move the left frozen
      times.
   2. Let `M := q * (d + 1)` and prove `hqM : q ≤ M` by `nlinarith`/`omega`
      from `Nat.succ_pos d`. Define
      `ψgap := inverseFourierFlatCLM χ` and
      `fpad := tailGapPadSchwartz hqM ψgap`.
   3. Define the Fubini family
      `gFamily : (Fin M → ℝ) → SchwartzMap (Fin M → ℝ) ℂ` by
      `gFamily x =
        physicsFourierFlatCLM
          (SCV.translateSchwartz
            (flatTailGapOrbit d q
              (fun j : Fin q => x (Fin.castLE hqM j))) Ψ)`.
      The continuity and seminorm-growth helpers are direct multi-parameter
      analogues of
      `continuous_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
      and
      `exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`,
      with `flatTailGapOrbit` a continuous finite linear map
      `(Fin q → ℝ) →L[ℝ] (Fin M → ℝ)`.
   4. Apply `schwartz_clm_fubini_exchange Tflat gFamily fpad` to obtain
      `Φ`, `hΦ_eval`, and `hΦ_pair`.
   5. Use `hTflat_repr` and `tailGapPadSchwartz_integral` to identify
      `∫ x, Tflat (gFamily x) * fpad x` with the desired gap integral.
   6. To prove `Φ` vanishes on the dual cone, fix
      `ξ ∈ DualConeFlat ((flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q)`.
      Set
      `lam ξ j := ∑ a, flatTailTimeShiftDirection d q j a * ξ a`.
      The sign lemma gives `∀ j, lam ξ j ≤ 0`.
   7. Rewrite the translated orbit by the full-tail version of
      `physicsFourierFlatCLM_translateSchwartz_apply`; the phase is
      `Complex.exp (-(Complex.I * ∑ j, (lam ξ j : ℂ) * (u j : ℂ)))`.
      Remove the padded dummy variables by `tailGapPadSchwartz_integral`.
   8. Apply
      `integral_tailGap_phase_mul_inverseFourierFlat_eq_zero_of_eqOn_positiveGapOrthant`
      with `hχ_zero` and `lam ξ`.
   9. Feed the resulting `hΦ_vanish` into `hTflat_supp` exactly as in
      `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`,
      then convert `Tflat Φ = 0` back to the gap integral using `hΦ_pair`.

   Proof transcript for
   `bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant`:

   1. Set `χ := χ₁ - χ₂`. From `hχ`, derive
      `hχ_zero : Set.EqOn (χ : (Fin q → ℝ) → ℂ) 0 (positiveGapOrthant q)`
      by pointwise subtraction.
   2. Obtain integrability for the two original integrands from
      `integrable_bvt_W_flattened_tailGapOrbit_mul_inverseFourierFlatCLM`
      applied to `χ₁` and `χ₂`.
   3. Use `map_sub` for `inverseFourierFlatCLM` and
      `MeasureTheory.integral_sub hInt₁ hInt₂` to rewrite the difference of
      the two displayed integrals as the single zero integral for `χ`.
   4. Apply
      `bvt_W_flattened_tailGapOrbit_pairing_eq_zero_of_eqOn_positiveGapOrthant`
      to that `χ` and close by `sub_eq_zero.mp`.

   The production proof pattern for the public BVLimits theorem is the
   compiled one-variable proof
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`,
   with three deliberate changes:

   1. obtain `Tflat` from the full
      `exists_flattened_bvt_W_dualCone_distribution (d := d) OS lgc q`;
   2. use `flatTailGapOrbit d q u` instead of the right-block
      `zeroHeadBlockShift (t • flatTimeShiftDirection d m)`;
   3. pad `inverseFourierFlatCLM χ`, not a physics-convention Fourier
      transform, because the finite gap variable is evaluated by
      `integral_tailGap_phase_mul_inverseFourierFlat_eq_eval`.

   For the corrected route, do **not** add a new wrapper named
   `unshifted_global_tailGap_quotient_descent_of_section43Transport`. The
   reusable BVLimits theorem above remains a valid support theorem, but it is
   no longer on the critical path unless a future proof first gives an explicit
   analytic-continuation lemma resolving the oscillatory/Laplace factor
   mismatch. The old full scalar normal-form theorem
   `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ`
   is withdrawn for the same reason. The Positivity proof may call the public
   tail-gap theorem only after it has produced the following exact normal-form
   data from a sound theorem surface:

   Optional tail-gap support placement after the 2026-04-13 code audit:

   1. In
      [SCV/PaleyWienerSchwartz.lean](/Users/xiyin/OSReconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean),
      add the public Fourier inversion helper
      `inverseFourierFlatCLM_integral_eval` immediately after
      `fourierTransformFlat_eval`. This is not OS-specific. Its proof must
      transport `FourierTransform.fourierInv_fourier_eq` through
      `EuclideanSpace.equiv (Fin q) ℝ`, following the existing
      `fourierTransformFlat_eval` transport proof. The sign convention is:

```lean
∫ u : Fin q → ℝ,
  Complex.exp (2 * Real.pi * Complex.I *
    (∑ j, (p j : ℂ) * (u j : ℂ))) *
    inverseFourierFlatCLM χ u =
  χ p
```

      This is the inverse transform of the Mathlib-convention flat Fourier
      transform. Do not replace it by `physicsFourierFlatCLM`.
   2. In
      [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean),
      add `import OSReconstruction.GeneralResults.FinProductIntegral` if the
      padding proof uses `MeasurableEquiv.finAddProd` and
      `MeasureTheory.volume_preserving_finAddProd`. `SCV.LaplaceSchwartz` is
      already available transitively through `SCV.VladimirovTillmann`, so
      `SCV.integrable_poly_growth_schwartz` should not require a new import.
   3. Still in BVLimits, make the gap-sector API public:
      `positiveGapOrthant`, `absTimesOfTailGaps`,
      `absTimesOfTailGaps_nonneg`, the left/right/reversed split maps, their
      nonnegativity lemmas, `firstRightComponent`, and `firstRightIndex`.
      Positivity needs these names to state the Section-4.3 expanded EqOn
      proof. Keep only proof-local reindexing and padding helpers private.
   4. Still in BVLimits, keep `tailGapPadSchwartz` and its padding-collapse
      lemmas private unless the bump helper
      `normedUnitBumpSchwartzPi` is deliberately promoted. The current
      production file already keeps `normedUnitBumpSchwartzPi`,
      `integral_normedUnitBumpSchwartzPi`, and
      `integral_comp_castFinCLE_eq` private, so the lowest-risk implementation
      colocates the padding proof with them in BVLimits.
   5. Add the public orbit definition `flatTailGapOrbit` in BVLimits, followed
      by the public pairing theorems
      `bvt_W_flattened_tailGapOrbit_pairing_eq_zero_of_eqOn_positiveGapOrthant`
      and
      `bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant`.
      These are the only tail-gap support theorems Positivity should consume.
      Their proof may use the private flattened `Tflat` witness
      `exists_flattened_bvt_W_dualCone_distribution`, the private sign lemma,
      and the private padding helpers.
   6. Only if those BVLimits/SCV declarations compile and the Positivity-side
      expansion theorem has constructed the actual `Ψ`, `χAmbient`, and
      `χTransport` produced by the Paley-Wiener/partial-spatial expansion
      should the finite-height scalar normal form call the public BVLimits
      theorem above. Positivity must prove the EqOn on
      `positiveGapOrthant (n + m)` from the Section-4.3 slice bridges, and it
      must not reach into private `Tflat`, padding, or sign internals.

   Required exact verification sequence once Lean implementation starts:

```bash
lake env lean OSReconstruction/SCV/PaleyWienerSchwartz.lean
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean
```

   Do not run a broad build for these support edits unless the exact touched
   files have already terminated cleanly and a checkpoint build is explicitly
   requested. Also do not implement this optional packet before the active
   scalar-normal-form proof needs it: if the Positivity expansion does not
   produce a fixed `Ψ` and two gap tests, the next Lean target is the full
   Section-4.3 scalar bridge, not this tail-gap specialization.

```lean
private theorem
    finiteHeight_expanded_tailGap_descent_instantiation
    {n m : ℕ}
    {φ : SchwartzNPoint d n} {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (Ψ : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ)
    (χAmbient χTransport :
      SchwartzMap (Fin (n + m) → ℝ) ℂ)
    (hχ :
      Set.EqOn
        (χAmbient : (Fin (n + m) → ℝ) → ℂ)
        χTransport
        (positiveGapOrthant (n + m))) :
    (∫ u : Fin (n + m) → ℝ,
      bvt_W OS lgc (n + m)
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz
              (flatTailGapOrbit d (n + m) u) Ψ)) *
        inverseFourierFlatCLM χAmbient u) =
    (∫ u : Fin (n + m) → ℝ,
      bvt_W OS lgc (n + m)
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz
              (flatTailGapOrbit d (n + m) u) Ψ)) *
        inverseFourierFlatCLM χTransport u) := by
  exact
    bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) hχ
```

   Required BVLimits side helpers for this theorem:

```lean
private theorem translateSchwartz_add
    {M : ℕ} (a b : Fin M → ℝ)
    (Ψ : SchwartzMap (Fin M → ℝ) ℂ) :
    SCV.translateSchwartz (a + b) Ψ =
      SCV.translateSchwartz a (SCV.translateSchwartz b Ψ) := by
  ext x
  simp [SCV.translateSchwartz_apply, Pi.add_apply, add_assoc]

private theorem continuous_translateSchwartz_flatTailGapOrbit
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ) :
    Continuous (fun u : Fin q → ℝ =>
      SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)

private theorem continuous_physicsFourierFlatCLM_translate_flatTailGapOrbit
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ) :
    Continuous (fun u : Fin q → ℝ =>
      physicsFourierFlatCLM
        (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) := by
  exact physicsFourierFlatCLM.continuous.comp
    (continuous_translateSchwartz_flatTailGapOrbit (d := d) Ψ)

private theorem norm_flatTailGapOrbit_le
    {q : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin q → ℝ, ‖flatTailGapOrbit d q u‖ ≤ C * ‖u‖

private theorem exists_bound_seminorm_physicsFourierFlatCLM_translate_flatTailGapOrbit
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ)
    (k l : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ u : Fin q → ℝ,
        SchwartzMap.seminorm ℝ k l
          (physicsFourierFlatCLM
            (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) ≤
          C * (1 + ‖u‖) ^ N
```

   Proof transcript for these side helpers:

   1. `translateSchwartz_add` is an `ext x; simp` proof from
      `SCV.translateSchwartz_apply`.
   2. Prove `continuous_translateSchwartz_flatTailGapOrbit` by induction on
      the finite index set `Fin q`. Write
      `flatTailGapOrbit d q u` as the finite sum of
      `u j • flatTailTimeShiftDirection d q j`, use
      `continuous_translateSchwartz_smul_local` for each coordinate function
      `fun u => u j`, and compose with `translateSchwartz_add`.
   3. `continuous_physicsFourierFlatCLM_translate_flatTailGapOrbit` is the
      displayed one-line composition with the continuous linear map
      `physicsFourierFlatCLM`.
   4. Prove `norm_flatTailGapOrbit_le` by
      `‖∑ j, u j • v j‖ ≤ ∑ j, |u j| * ‖v j‖`, then bound every
      `|u j|` by `‖u‖` with `norm_le_pi_norm`; take
      `C := ∑ j, ‖flatTailTimeShiftDirection d q j‖`.
   5. Prove the seminorm growth helper by copying
      `exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
      with `η` replaced by `flatTailGapOrbit d q u`. The only changed estimate
      is
      `1 + ‖flatTailGapOrbit d q u‖ ≤ (1 + C) * (1 + ‖u‖)`,
      which follows from `norm_flatTailGapOrbit_le`; all remaining
      `Seminorm.bound_of_continuous`, `SCV.seminorm_translateSchwartz_le`,
      finite-sup, and constant-absorption lines are identical.

   Here `finiteHeight_expanded_tailGap_descent_instantiation` is a documentation
   name only and should now be treated as a special-case lemma, not as the live
   hard-theorem gate. In production, the hard theorem should instead construct
   the concrete full Fourier-side kernels `KAmbient` and `KTransport` from:

   1. `partialFourierSpatial_fun_eq_integral`;
   2. the public Paley-Wiener kernel formula `psiZ_twoPi_pairing_formula`;
   3. the flatten/reindex/tensor rewrite to the full `Tflat` surface.

   Implementation-readiness correction. The Positivity-side proof must not call
   the tail-gap theorem with anonymous or existential `χAmbient`/`χTransport`
   data. Moreover, a same-`Ψbase`, different-`χ` factorization is **not** an
   active theorem surface unless a separate expansion lemma has already proved
   that all representative dependence factors through the two gap tests. The
   current production code does not yet contain such a factorization lemma, and
   the older audit below explains why assuming it would be too strong.

   Before the branch decision, the route audit left two logically possible
   branches:

   1. prove the full Fourier-side kernel packet
      `KAmbient`/`KTransport` after Section-4.3 scalar normalization and use
      `tflat_pairing_eq_of_eqOn_dualCone`, as in the full-kernel transcript
      below;
   2. or first prove an explicit factorization theorem reducing those full
      kernels to a common `Ψbase` paired against two gap tests, and only then
      use the tail-gap `χAmbient`/`χTransport` theorem.

   The current route chooses branch 1. In branch 1, `KAmbient` and `KTransport`
   are **not** the raw canonical shell and horizontal kernels. They are the
   full Fourier-side kernels after the proof has expanded the two scalar
   expressions and applied the Section-4.3 slice comparison to put both sides
   on the same transported normal form. If the proof then factors the
   remaining difference through a fixed flattened test `Ψ` and two gap tests
   `χAmbient`, `χTransport`, that factorization is part of the branch-1
   expansion proof, not an assumed shortcut. What remains inactive is the
   branch-2 shortcut where one starts from a same-`Ψbase`/different-`χ`
   certificate without first deriving it from the full scalar expansion. If the
   attempted `KAmbient` pointwise formula still contains an ambient `φ`-slice
   or shifted `ψ`-slice after the normalization step, the branch is not ready.

   Current branch decision after the 2026-04-13 scalar audit: branch 1 is the
   only live branch. Branch 2, the same-`Ψbase`/different-`χ` factorization
   route, is inactive unless a separate explicit factorization theorem is first
   proved. The concrete Lean target for branch 1 is the finite-height
   transported residual theorem
   `bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport`
   displayed earlier in this subsection, together with the formal limit theorem
   `tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_zero_of_section43Transport`.

   Therefore the next proof-doc gap is no longer "choose a branch". The branch
   is chosen. The remaining readiness work is to keep the branch-1 proof
   transcript synchronized with the exact production theorem surfaces listed in
   the status ledger below, and to make sure the finite-height residual proof
   reduces to the already-packaged Section-4.3 slice bridges rather than to raw
   `KShell = KHorizontal` equality.

   Raw-kernel diagnostic for the current canonical time-shift shell. A tempting
   third branch would be to construct the finite-height shell kernel for
   `(φ.conjTensorProduct (timeShiftSchwartzNPoint t ψ))` and compare it
   directly with the horizontal kernel from
   `exists_horizontalKernel_pairing_iteratedFourierLaplace`. This is also not
   allowed. The dual-cone pointwise normal forms already determine the
   obstruction.

```lean
private theorem canonicalTimeShiftShell_kernel_pointwise_on_dualCone
    -- schematic arguments: OS lgc hm φ ψ hψ_compact ht hε, common `Tflat`,
    -- and `KTimeShiftShell` obtained from the canonical shell Fubini packet
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ : ξ ∈ DualConeFlat
      ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    KTimeShiftShell ξ =
      Complex.exp (-(ε : ℂ) * (ηCanonicalPair ξ : ℂ)) *
      physicsFourierFlatCLM
        (_root_.flattenSchwartzNPoint (d := d)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) ξ
```

   The proof is just `hKTimeShiftShell_eval ξ`,
   `multiDimPsiZExt_apply_of_mem_dualCone`, and
   `physicsFourierFlatCLM_integral`. Rewriting the shifted right tensor by the
   local configuration lemma produces the same oscillatory real-time phase as
   the `xiShift` shell diagnostic:

```lean
base ξ *
  Complex.exp (-(Complex.I * (t : ℂ) * (lam ξ : ℂ))) *
  Complex.exp (-(ε : ℂ) * (ηCanonicalPair ξ : ℂ))
```

   The horizontal kernel computed by
   `horizontalKernel_pointwise_eq_exp_of_mem_dualCone` has instead

```lean
base ξ *
  Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam ξ / (2 * Real.pi))) *
  Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam ξ / (2 * Real.pi)))
```

   Hence the raw canonical time-shift shell kernel and the raw horizontal
   kernel do not agree pointwise on the dual cone. This confirms that the
   finite-height scalar normal form cannot be implemented by a direct
   `Set.EqOn KTimeShiftShell KHorizontal` either. The Section-4.3 argument must
   first normalize the scalar through the positive-energy quotient/slice
   comparison, or prove a factorization reducing the difference to a
   positive-gap test killed by the support theorem.

   The following same-`Ψbase` display is retained only as the exact shape that
   any proved reduction to the public tail-gap theorem must expose. It is not
   an assumption and not a standalone branch-2 implementation target for the
   finite-height scalar normal form:

```lean
let Ψbase : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ :=
  physicsFourierFlatCLM
    (OSReconstruction.reindexSchwartzFin
      (Nat.add_mul n m (d + 1)).symm
      (((_root_.flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
        (_root_.flattenSchwartzNPoint (d := d) ψ))))

let χAmbient : SchwartzMap (Fin (n + m) → ℝ) ℂ := by
  -- the gap-variable Schwartz test obtained after expanding the ambient
  -- `φ, ψ` partial-spatial slices and the two `ψ_Z` kernels

let χTransport : SchwartzMap (Fin (n + m) → ℝ) ℂ := by
  -- the same gap-variable Schwartz test with the ambient slices replaced by
  -- the Section-4.3 positive-time preimage slices from `f` and `g`
```

   The displayed `by` bodies are not intended production syntax. They mark the
   exact factorization obligation before the public tail-gap theorem may be
   called: the formulas for `χAmbient` and `χTransport` must be written out
   from the preceding partial-Fourier expansion, and a theorem must prove that
   the full scalar residual really reduces to this common-`Ψbase` form. Without
   that proved expansion, do not call the tail-gap test theorem in the scalar
   normal-form proof. Once the expansion is proved, the only remaining EqOn
   goal is the concrete positive-tail-gap statement:

```lean
have hχ :
    Set.EqOn
      (χAmbient : (Fin (n + m) → ℝ) → ℂ)
      χTransport
      (positiveGapOrthant (n + m)) := by
  intro u hu
  let tabs : Fin (n + m) → ℝ := absTimesOfTailGaps u
  let tφ : Fin n → ℝ :=
    absTimesOfTailGapsSplitLeft (n := n) (m := m) u
  let tψ : Fin m → ℝ :=
    absTimesOfTailGapsSplitRight (n := n) (m := m) u
  have hφ_nonneg : ∀ i : Fin n, 0 ≤ tφ i :=
    absTimesOfTailGapsSplitLeft_nonneg (n := n) (m := m) hu
  have hψ_nonneg : ∀ j : Fin m, 0 ≤ tψ j :=
    absTimesOfTailGapsSplitRight_nonneg (n := n) (m := m) hu
  -- If the expanded left factor is `φ.borchersConj`, rewrite by
  -- `SchwartzMap.borchersConj_apply` and use
  -- `absTimesOfTailGapsSplitLeftRev_nonneg` for the reversed left vector.
  -- Then close by the scalar slice bridges
  -- `fourierInvPairingCLM_*_of_repr_eq_transport`.
```

   This is the only acceptable **χ-only** use of an EqOn theorem in the
   finite-height scalar normal form: it compares two gap test functions on the
   positive gap sector after a full scalar expansion theorem has reduced the
   residual to this surface. It does not compare `KShell` with `KHorizontal` on
   the dual cone, and it must not be used before the expansion theorem is
   actually proved.

   The EqOn proof for the concrete kernels is no longer schematic. For
   `u ∈ positiveGapOrthant (n + m)`, set

```lean
let tabs : Fin (n + m) → ℝ := absTimesOfTailGaps u
let tφ : Fin n → ℝ := absTimesOfTailGapsSplitLeft (n := n) (m := m) u
let tψ : Fin m → ℝ := absTimesOfTailGapsSplitRight (n := n) (m := m) u
```

   Then

```lean
have htabs_nonneg : ∀ i : Fin (n + m), 0 ≤ tabs i :=
  absTimesOfTailGaps_nonneg (q := n + m) hu
have hφ_nonneg : ∀ i : Fin n, 0 ≤ tφ i :=
  absTimesOfTailGapsSplitLeft_nonneg (n := n) (m := m) hu
have hψ_nonneg : ∀ j : Fin m, 0 ≤ tψ j :=
  absTimesOfTailGapsSplitRight_nonneg (n := n) (m := m) hu
```

   These are the exact hypotheses needed to call
   `partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion`,
   `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport`, or the
   already-packaged scalar slice lemmas. This is where the Section-4.3
   hypotheses `hφf` and `hψg` enter. They do **not** enter the BVLimits
   support theorem.

   Left-factor reversal guard. If the expanded normal form exposes the left
   Wightman factor as `φ.borchersConj`, the Section-4.3 EqOn proof is applied
   to `φ` after the `Fin.rev` argument reversal from
   `SchwartzMap.borchersConj_apply`. The required nonnegative vector is
   `absTimesOfTailGapsSplitLeftRev (n := n) (m := m) u`, with proof
   `absTimesOfTailGapsSplitLeftRev_nonneg (n := n) (m := m) hu`.
   Do not change the positive tail-gap
   theorem for this: reversal is a local left-factor bookkeeping step in the
   Positivity instantiation, not part of the BVLimits support theorem.

   The global support theorem is a necessary mathematical blocker for
   implementation readiness, but it is no longer sufficient by itself. It
   handles the unshifted Section-4.3 descent inside the expanded normal form;
   the shifted right factor still has to be handled by the separate
   positive-support time-shift distribution theorem recorded in the `hPsi`
   section below. This is a real theorem, not a wrapper: it is precisely the
   missing bridge from Section-4.3 equality on the full positive-energy region
   to the unshifted integrated time/spatial Fourier pairing used after the
   Paley-Wiener expansion.
8. Use `schwartz_clm_fubini_exchange` only after the mandatory `Fin 1`
   adapter above:

```lean
obtain ⟨Φ1, hΦ1_point, hΦ1_apply⟩ :=
  schwartz_clm_fubini_exchange
    (m := 1) T1 g1 f1
    (continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal hε)
    (seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth hε)
```

   Then rewrite `hΦ1_apply` by `h_outer_real`. Do not use `hTW` in this Fubini
   call; `hTW` is reserved for the Section-4.3 quotient descent on the
   original real-line functional `TW`. If Lean exposes a side goal not literally
   discharged by the two displayed side helpers, record the exact side goal
   here before adding another helper.
9. The scalar kernel identity inside the Fubini proof uses the public
   Paley-Wiener `ψ_Z` pairing formula already available in
   [SCV/PaleyWiener.lean](/Users/xiyin/OSReconstruction/OSReconstruction/SCV/PaleyWiener.lean):

```lean
theorem psiZ_twoPi_pairing_formula
    (φ : SchwartzMap ℝ ℂ) (η ξ : ℝ) :
    ∫ x : ℝ,
      SCV.psiZ ((2 * Real.pi : ℂ) * (x + η * Complex.I)) ξ * φ x =
        SCV.smoothCutoff ξ *
          Complex.exp (-(2 * Real.pi * η : ℂ) * ξ) *
          FourierTransform.fourierInv φ ξ
```

   This is a kernel formula, not an OS/Wightman comparison theorem. It may be
   proved by renaming the existing private theorem or by a short public wrapper
   in the same file if namespace/export constraints require it.
10. After the two slice replacements and the `ψ_Z` kernel computation, the
   remaining one-variable upper-half-plane value is exactly the Section-4.3
   class of `ψZxε x`; use `section43_iteratedSlice_descendedPairing` only at
   this final one-variable stage, with `hw` proved by `by simpa using hε`.

This gate changes only the local-readiness status for the older Section-4.3
finite-height draft: the two `Fin 1` side helpers are Lean-ready, the
coordinate policy for the frozen slices is fixed, and the zero-left branch is
documented. It does **not** make the full shell-to-Laplace residual ready by
itself; the residual still has to pass through the transported finite-height
theorem and the status ledger below.

2026-04-13 correction after the horizontal scalar computation:
the raw canonical-shell/horizontal dual-cone EqOn target is **withdrawn as an
active implementation target**. The checked horizontal scalar has the damping
factor

```lean
base ξ *
  Complex.exp ((ε : ℂ) * (lam ξ : ℂ)) *
  Complex.exp ((t : ℂ) * (lam ξ : ℂ))
```

where `lam ξ` is the zero-head right-time-shift pairing. The positive-height
canonical shell, however, uses `xiShift ... (t : ℂ)` as a real tube shift and
the canonical imaginary direction `ε • canonicalForwardConeDirection`. On the
dual cone its pointwise exponential has the schematic scalar

```lean
base ξ *
  Complex.exp (-(ε : ℂ) * ηCanonicalPair ξ) *
  Complex.exp (-(Complex.I * (t : ℂ) * (lam ξ : ℂ)))
```

up to the already-fixed sign convention
`lam ξ = - tailTimePair ξ`. These two scalars are not equal on the full dual
cone: the shell has an oscillatory real-time factor, while the horizontal
imaginary-axis witness has Laplace damping. Therefore an arbitrary-`φ,ψ`
theorem named

```lean
canonicalShell_horizontal_kernel_eqOn_dualCone
```

would prove the false generic identity between real-time Wightman values and
positive-imaginary-axis Laplace values. Do not implement it, and do not use the
horizontal `KHorizontal` packet to prove a zero residual for arbitrary
ambient representatives.

The sound live implementation order is instead:

1. keep the already-checked canonical shell tube/Fubini package as a diagnostic
   and as support for the actual shell limit;
2. keep the already-checked horizontal Paley/Fubini package as the canonical
   Wightman witness normal form;
3. prove the non-finite-height positive-support identity
   `bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport`;
4. combine that pointwise identity with
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   to supply the `hlimit` hypothesis of
   `lemma42_matrix_element_time_interchange`;
5. supply the separate `hH_imag_os` hypothesis from the hPsi packet and the
   existing canonical-witness/OS-holomorphic reducer.

The raw transport/cutoff packet
`zSplit_mem_forwardTube_of_osConjTensorProduct_support`,
`exists_transportTubeCutoff`,
`exists_transportKernel_pairing_singleSplitXiShiftScalar`, and
`hardSingleSplit_psiZ_timeShift_expands_to_dualCone_eq_kernel_pairing` is
retired for the current route. Do not implement or consume it unless a separate
future correction supplies a valid tube representative.

The former finite-height certificate transcript is withdrawn. In particular,
do not implement
`tendsto_bvt_F_canonical_xiShift_section43Transport_iterated_residual_zero`
from
`bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport`.
That theorem chain assumes exactly the finite-height cancellation invalidated
by the fixed-`x` exponential audit.

The replacement limit supplier is formal only after the following pointwise
identity has been proved:

```lean
private theorem
    bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport
```

Its proof must compare the real-time Wightman value and the canonical
imaginary-axis witness through the one-variable positive-support
Section-4.3 quotient. It must not prove a shell-minus-horizontal finite-height
zero residual first.

Concrete source anchors for the preferred limit-level route:

1. configuration-space shell rewrite:
   `bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift` and
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`;
2. canonical horizontal normal form:
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral` and
   `integral_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_iterated_fourierLaplaceIntegral`;
3. Fubini/CLM exchange source:
   `schwartz_clm_fubini_exchange`, but only through the displayed `Fin 1`
   adapter `T1`, `f1`, `g1`, `h_outer_real`, and the two exact
   continuity/growth helpers
   `continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal` and
   `seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth`;
4. one-variable slice transport:
   `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport`,
   `fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport`,
   and the two `fourierInvPairingCLM...sub_eq_zero...` lemmas;
5. OS I Section-8 time interchange:
   the production one-variable Paley-Wiener/Laplace ingredients
   `complexLaplaceTransform_hasPaleyWienerExtension`,
   `fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform`,
   `partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`,
   and `SCV.psiZ_eq_exp_of_nonneg`.
6. Shift handling source:
   the shift is handled only at the level of the real-time distribution paired
   with `(SchwartzMap.fourierTransformCLM ℂ) ψ_Z`. The proof must use the
   Paley-Wiener `ψ_Z` kernel formula and positive-support distribution
   interchange before applying unshifted Section-4.3 slice descent. It must not
   infer any equality of shifted representatives from `hψg`.

The route choice in this older subsection is retained only for the separate
Section-4.3 OS-identification work. It is no longer the live shell-to-Laplace
blocker. For the shell-to-Laplace seam, production implementation must follow
the corrected canonical positive-height shell packet in §5.9.4a.1.ε. In
particular, do not attempt the raw `singleSplit` transport/cutoff packet, and
do not reopen the pointwise/evaluation-normal-form route unless this
subsection is rewritten with an explicit approximate-identity theorem.

The equality form consumed by the shell-limit theorem is formal:

```lean
private theorem
    bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, ∀ ht : 0 < t,
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht)))
```

Proof transcript for the equality form:

1. Fix `t ht`.
2. Let `hZero` be
   `tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_zero_of_section43Transport`
   at `t ht`.
3. Let `hResidual` be the already-proved obstruction-limit theorem
   `tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_timeShift_sub_canonicalExtension`
   at the same `t ht`.
4. Use `tendsto_nhds_unique hResidual hZero` to obtain
   `bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
      (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)`.
5. Rewrite the canonical imag-axis value with
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`.
6. Close by `simpa` with the local `ψZt` abbreviation. This theorem is
   downstream of the zero residual; it does not prove a pointwise scalar normal
   form directly.

The pointwise transported `singleSplit` scalar bridge is downstream of both the
descended-`ψ_Z` theorem and the `hPsi` spectral identification:

```lean
private theorem
    bvt_W_timeShift_eq_singleSplitXiShiftScalar_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
    bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t
```

Proof transcript for the downstream `singleSplit` scalar bridge:

1. Rewrite the left side by
   `bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport`.
2. Rewrite the descended `ψ_Z` pairing by
   `descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport`.
3. Rewrite the spectral boundary value by
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`
   and then
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`.
4. Rewrite the OS holomorphic value by
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`.
5. Rewrite the resulting `singleSplit` value with
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`.

After the pointwise Lemma-8.4 supplier has supplied
`bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport`, the
shell-limit theorem needed by `lemma42_matrix_element_time_interchange` is
direct assembly:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, 0 < t →
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)))
```

Proof transcript for the direct shell-limit theorem:

1. For fixed `t ht`, let `hShell` be
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   specialized to `φ ψ t`.
2. Let `hPoint` be
   `bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport` at
   `t ht`.
3. Rewrite the target of `hShell` by `hPoint`.
4. Close with `simpa`. This theorem itself is formal; the non-formal content
   is isolated entirely in
   `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`.

The zero-residual `Tendsto` theorem toward the positive-time `singleSplit`
scalar is downstream diagnostic/assembly work. It is formal after the
`singleSplit` scalar bridge above, not the first implementation target:

```lean
private theorem
    tendsto_bvtCanonicalXiShiftShell_sub_singleSplitXiShiftScalar_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun ε : ℝ =>
        bvtCanonicalXiShiftShell (d := d) OS lgc hm φ ψ t ε -
          bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)
```

The displayed `tendsto_bvt_F_canonical_xiShift_to_singleSplitXiShift_of_section43Transport`
is then formal:

1. Let `hzero` be
   `tendsto_bvtCanonicalXiShiftShell_sub_singleSplitXiShiftScalar_zero_of_section43Transport`.
2. Let `hconst` be `tendsto_const_nhds` for
   `bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t`.
3. Use `hzero.add hconst`, then `simpa [bvtCanonicalXiShiftShell,
   bvtSingleSplitXiShiftScalar, sub_eq_add_neg, add_comm, add_left_comm,
   add_assoc]`.

Proof transcript for the zero-residual theorem:

1. Let `hShell` be
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   specialized to `φ ψ t`.
2. Let `hScalar` be
   `bvt_W_timeShift_eq_singleSplitXiShiftScalar_of_section43Transport` at
   `t ht`.
3. Rewrite the target of `hShell` by `hScalar`, obtaining convergence of the
   source function `bvtCanonicalXiShiftShell (d := d) OS lgc hm φ ψ t` to the
   scalar `bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t`.
4. Subtract the constant target with `hShell'.sub tendsto_const_nhds`.
5. Close by `simpa [bvtCanonicalXiShiftShell, bvtSingleSplitXiShiftScalar]`.

Paper and code dependency inventory for the finite-height normal-form helper
`bvt_F_canonical_xiShift_shell_eq_integrated_descendedPsiZ_of_section43Transport`:

Current production-surface ledger for the chosen branch:

1. Already present in
   [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean):
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D`,
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`,
   `bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift`,
   `bvt_F_canonical_xiShift_shell_sub_horizontal_eq_shell_sub_iterated_fourierLaplaceIntegral`,
   `bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral`,
   `tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_timeShift_sub_canonicalExtension`,
   `tendsto_bvt_F_canonical_xiShift_shell_sub_iterated_to_timeShift_sub_canonicalExtension`,
   `tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero`,
   `partialFourierSpatial_timeSlice_eqOn_nonneg_of_transport_eq`,
   `partialFourierSpatial_timeSliceSchwartz_eq_of_transport_eq`,
   `section43_iteratedSlice_descendedPairing_imagAxis`, and
   `section43_iteratedSlice_descendedPairing`.
2. Already present in
   [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean):
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`,
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport`,
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral`,
   and
   `tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_to_imagAxis`.
3. Withdrawn after the fixed-`x` scalar audit:
   `bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport`.
   The theorem is a finite-height zero-residual statement and inherits the
   same oscillatory/Laplace mismatch as the non-subtractive `TW/ψ_Z` scalar
   normal form. It must not be implemented unless a new explicitly stated
   analytic-continuation lemma first bridges that exact mismatch. The
   Section-4.3 frozen-slice bridge remains useful, but it does not by itself
   convert `exp (-I t lam)` into `exp (t lam)` at finite height.
4. Current live implementation route after this correction:
   prove the two non-finite-height Section-4.3 time-interchange packets:
   the pointwise shell-limit supplier
   `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`
   and the Fourier-tested hPsi supplier
   `lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport`.
   These are the theorem surfaces where OS I `(4.23) -> (4.24)` and the
   one-variable positive-support interchange Lemma 8.4 legitimately enter.
5. Optional tail-gap specialization slots are not yet production declarations
   under the documentation names:
   `positiveGapOrthant`, `absTimesOfTailGaps`,
   `absTimesOfTailGapsSplitLeft`, `absTimesOfTailGapsSplitRight`,
   `absTimesOfTailGapsSplitLeftRev`, `flatTailGapOrbit`, `tailGapPadSchwartz`,
   `inverseFourierFlatCLM_integral_eval`, and
   `bvt_W_flattened_tailGapOrbit_pairing_eq_zero_of_eqOn_positiveGapOrthant`.
   These become prerequisites only if a future non-withdrawn scalar expansion
   is explicitly proved to factor through a fixed flattened test and two gap
   tests. Do not
   silently reuse the one-variable `zeroHeadBlockShift` theorem as if it were
   the multi-tail-gap support theorem.
   If the tail-gap specialization is chosen, implementation location is fixed
   by the production audit above:
   `inverseFourierFlatCLM_integral_eval` belongs in
   `SCV/PaleyWienerSchwartz.lean`; the gap-sector API, padding helpers,
   `flatTailGapOrbit`, and the public tail-gap pairing theorems belong in
   `OSToWightmanBoundaryValueLimits.lean`; the finite-height Section-4.3
   instantiation belongs in `OSToWightmanPositivity.lean`.
6. Active implementation gate before Lean work:
   the proof docs for both non-finite-height packets must expose the exact
   Lemma-8.4 interchange proving
   `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`
   and
   `lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport`.
   Any theorem that tries to close the route by a finite-height
   shell/horizontal equality is off route.
7. Formal consequences after the hPsi packet:
   `section43_timeShift_descendedPsiZ_eq_osHolomorphicValue_of_section43Transport`,
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport`,
   `descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport`, and the
   canonical witness imag-axis identification. If the final proof instead uses
   the direct positive-real consumer
   `kernel_eq_of_osHolomorphicValue_eq_bvt_W_timeShift_on_positiveReals`, the
   additional theorem needed is exactly the pointwise Lemma-8.4 supplier above,
   not a finite-height shell equality.

Implementation-readiness checklist for the next Lean round:

1. Do not implement the finite-height scalar normal-form theorem or the
   finite-height zero-residual theorem. The fixed-`x` audit shows they require
   an additional analytic-continuation lemma that is not present in production.
2. Keep the optional tail-gap and frozen-slice lemmas as support diagnostics
   only. They may be useful later, but they are not the next critical-path Lean
   edits.
3. The next Lean implementation packets are the Lemma-8.4 shell-limit supplier
   and the hPsi / positive-real time-interchange supplier. They begin with
   `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`
   and
   `lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport`,
   then assemble the already documented shell-limit, descended-`ψ_Z`, and
   spectral-boundary consequences.
4. If a Lean attempt creates a goal involving raw `KShell = KHorizontal`,
   `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ`,
   or a finite-height zero residual, stop and return to this checklist. That
   goal has left the corrected route.

Non-finite-height shell-limit supplier:

The hPsi packet identifies the canonical upper-half-plane witness with the OS
holomorphic matrix element on the positive imaginary axis, but it does not by
itself identify the canonical `ξ`-shell limit with that witness. The missing
supplier is the pointwise OS I Lemma-8.4 time-component interchange, stated on
the exact canonical witness surface:

```lean
private theorem
    lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
    ∫ τ : ℝ,
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
      (SchwartzMap.fourierTransformCLM ℂ ψZ) τ
```

This is the exact non-finite-height replacement for the withdrawn residual.
It is not a wrapper: it is precisely the passage from the pointwise Wightman
time-shift value to the Fourier-tested Paley-Wiener `ψ_Z` value. In the paper
this is the time-component part of `(4.23) -> (4.24)`, justified by Lemma 8.4.

Lean-ready reduction of the shell supplier:

The hard theorem should not carry the already-formal real-line integral
expansion. Put the remaining mathematical content on the Section-4.3
descended one-variable quotient surface:

```lean
private theorem
    lemma84_bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact)
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
        (d := d) OS lgc hm φ ψ hψ_compact)
      (section43PositiveEnergyQuotientMap1D ψZ)
```

Then
`lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`
is formal:

```lean
  let ψZ : SchwartzMap ℝ ℂ := ...
  have hPoint :=
    lemma84_bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact)
      (f := f) (g := g) (hf_compact := hf_compact)
      (hg_compact := hg_compact) hφf hψg ht
  have hIntegral :
      ∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ ψZ) τ =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D ψZ) := by
    simpa [ψZ] using
      integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (f := φ) (g := ψ) (hg_compact := hψ_compact) ht
  exact hPoint.trans hIntegral.symm
```

Therefore the implementation blocker is no longer "prove an integral equals a
point value" as a single opaque scalar equality. It is: prove that the point
value is the descended `ψ_Z` quotient evaluation after the OS-I partial-spatial
slice expansion and Section-4.3 transport.

Proof transcript for `lemma84_bvt_W_timeShift...`:

1. Fix `t ht` and introduce
   `ψZ := SCV.schwartzPsiZ (((2 * Real.pi : ℂ) * (t * Complex.I))) ...`.
2. Expand the left pointwise Wightman value by isolating the first right-factor
   time variable. In the concatenated `(n + m)`-point test this is the embedded
   coordinate `⟨n, Nat.lt_add_of_pos_right hm⟩`; on the right factor itself it
   is the local coordinate

```lean
let rψ : Fin m := ⟨0, hm⟩
```

   After the ordinary spatial Fourier normalization, each local scalar is a
   one-variable Fourier-Laplace value for an opposite-factor pairing
   functional. Up to the symmetry
   `fourierInvPairingCLM_fourierTransform_symm`, the expected local normal form
   is

```lean
let fSlice : SchwartzMap ℝ ℂ :=
  partialFourierSpatial_timeSliceSchwartz
    (d := d) (n := n)
    (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ
let Tloc : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  fourierInvPairingCLM fSlice
let hTloc_supp : SCV.HasOneSidedFourierSupport Tloc :=
  fourierInvPairing_hasOneSidedFourierSupport fSlice
    (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
      (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f)
      rφ tφ ξφ)
SCV.fourierLaplaceExt Tloc
  (((2 * Real.pi * t : ℂ) * Complex.I))
  (by
    simpa [Complex.mul_im, ht.ne']
      using mul_pos Real.two_pi_pos ht)
```

   If the expansion exposes the opposite orientation, use
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
   to put it on this `Tloc` surface. The `n = 0` branch uses the already
   documented zero-left representative path instead of manufacturing an
   artificial left slice. This is the pointwise side of OS I `(4.23)`.
3. Expand the right Fourier-tested Wightman value only through
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` and then the
   same partial-spatial Fourier / time-slice normal form. After the mandatory
   `Fin 1` Fubini adapter, the local scalar is on the same `Tloc` surface:

```lean
OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
  Tloc
  hTloc_supp
  (section43PositiveEnergyQuotientMap1D ψZ)
```

   This is the Fourier-tested side of OS I `(4.24)`. No theorem in this step
   may mention `bvt_F`, `KShell`, `KHorizontal`, or a finite-height residual.
4. The local one-variable Lemma-8.4 atom is the general Paley-Wiener evaluation
   of an arbitrary one-sided Fourier-support functional on `ψ_Z`. Add the
   following bridge if Lean needs a named theorem rather than rewriting
   `SCV.fourierLaplaceExt_eq` and the quotient apply theorem inline:

```lean
private theorem
    lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt T
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by
          simpa [Complex.mul_im, hη.ne']
            using mul_pos Real.two_pi_pos hη) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        T hT_supp
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη)))
```

   Proof in Lean is just the two defining rewrites:

```lean
  rw [SCV.fourierLaplaceExt_eq]
  symm
  exact
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
      (T := T) (hT_supp := hT_supp)
      (f := SCV.schwartzPsiZ
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by
          simpa [Complex.mul_im, hη.ne']
            using mul_pos Real.two_pi_pos hη))
```

5. Ambient representatives may be replaced by positive-time representatives
   only through the existing Section-4.3 slice bridges. Supply `ha_supp` from
   `tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`
   after replacing ambient slices by transported positive-time slices. The
   only permitted replacements are
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`,
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   and
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`.
6. The background-time nonnegativity hypotheses for those slice lemmas are an
   explicit local obligation:

```lean
htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i
htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i
```

   In local slice helpers, carry `htφ` and `htψ` as hypotheses. In the global
   `lemma84...` proof, prove `htφ` and `htψ` from the concrete background-time
   maps produced by the spatial/time-slice expansion. Do not cite
   `absTimesOfTailGapsSplitLeft_nonneg`,
   `absTimesOfTailGapsSplitRight_nonneg`, or
   `absTimesOfTailGapsSplitLeftRev_nonneg` unless those adapter declarations
   have first been added to production with their displayed definitions.
   Compact support and `0 < t` are not substitutes for these hypotheses.
   The minimal production support packet needed for the common head-slice
   expansion is:

```lean
private def headSliceIndex {q : ℕ} (hq : 0 < q) : Fin q :=
  ⟨0, hq⟩

private def orderedHeadGapTimes {q : ℕ} (hq : 0 < q)
    (x : NPointDomain d q) : Fin q → ℝ :=
  fun i => x i 0 - x (headSliceIndex hq) 0

set_option linter.unusedSectionVars false in
private theorem orderedHeadGapTimes_nonneg_of_orderedPositive
    {q : ℕ} (hq : 0 < q)
    {x : NPointDomain d q}
    (hx : x ∈ OrderedPositiveTimeRegion d q) :
    ∀ i : Fin q, i ≠ headSliceIndex hq →
      0 ≤ orderedHeadGapTimes (d := d) hq x i
```

   Proof transcript:

```lean
  intro i hi
  have h0i : headSliceIndex hq < i := by
    rw [Fin.lt_def, headSliceIndex]
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hi (Fin.ext hzero))
  have hlt : x (headSliceIndex hq) 0 < x i 0 :=
    (hx (headSliceIndex hq)).2 i h0i
  dsimp [orderedHeadGapTimes]
  linarith
```

   The global expansion should instantiate
   `rψ := headSliceIndex hm` and
   `tψ := orderedHeadGapTimes hm xψ` on the right factor, giving
   `htψ := orderedHeadGapTimes_nonneg_of_orderedPositive hm hxψ`. If `0 < n`,
   use the same head-gap packet for the left positive-time slice. If the left
   factor is exposed after Borchers conjugation or reversal, first reindex it
   back to the positive-time representative before applying the slice bridge;
   otherwise the proof has again drifted to a raw combined-kernel route.
7. Apply `schwartz_clm_fubini_exchange` only through the mandatory `Fin 1`
   adapter documented earlier in this file:

```lean
let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
let fromFin1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1.symm
let T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ :=
  TW.comp fromFin1
```

   The Fubini output is used only via its pair field and converted back to the
   real-line integral by `MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ`.
   Then close the global theorem by `MeasureTheory.integral_congr_ae`,
   the local `ψZ` abbreviation, and the local atom in Step 4.

Once `lemma84_bvt_W_timeShift...` is proved, the pointwise canonical-witness
identity is formal:

```lean
private theorem
    bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, 0 < t →
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)
```

Proof transcript:

1. Fix `t ht` and set `ψZ` as above.
2. Rewrite the right side by
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral`
   with `η := t`.
3. Apply
   `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`.
4. Close by `simpa [ψZ]`.

The shell-limit supplier for the public `lemma42_matrix_element_time_interchange`
is then formal:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, 0 < t →
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)))
```

Proof transcript:

1. Fix `t ht`.
2. Let `hShell` be
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   at `φ ψ t`.
3. Let `hPoint` be
   `bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport`
   at `t ht`.
4. Retarget `hShell` by `simpa [hPoint] using hShell`. No
   shell-minus-horizontal theorem or finite-height residual is used.

Finally, the transported-image public adapter is formal after both the hPsi
packet and this shell-limit supplier:

```lean
private theorem
    lemma42_matrix_element_time_interchange_of_section43Transport
    -- same transported-image hypotheses
```

Proof transcript:

1. Apply the existing public
   `lemma42_matrix_element_time_interchange` with
   `H := bvt_W_conjTensorProduct_timeShiftCanonicalExtension
      (d := d) OS lgc φ ψ hψ_compact`.
2. Supply `hH_imag_os` from
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`,
   proved by the hPsi packet.
3. Supply `hlimit` from
   `tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport`.
4. Close by `simpa`.

Chosen next proof-doc path after the fixed-`x` scalar audit:

The next documentation/Lean pass should complete the two **non-finite-height**
time-interchange packets, not the finite-height scalar bridge and not the
optional tail-gap specialization. The reason is mathematical, not cosmetic:
production already computes the finite-height horizontal factor as Laplace
damping, while the canonical time-shift shell retains an oscillatory real-time
factor. The place where OS I permits this conversion is the positive-support
time-interchange argument `(4.23) -> (4.24)`, not a finite-height
shell/horizontal equality.

The concrete hard theorems that must be implementation-ready are:

```lean
private theorem
    lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport

private theorem
    lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport
```

The positive-real time-interchange proof still uses the same local frozen-slice
bridge when it expands the OS I `(4.23)` integrand. Its
representative-dependent scalar is exactly:

```lean
fourierInvPairingCLM
    (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
      (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
    ((SchwartzMap.fourierTransformCLM ℂ)
      (partialFourierSpatial_timeSliceSchwartz
        (d := d) (n := n) φ rφ tφ ξφ))
-
fourierInvPairingCLM
    (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
    ((SchwartzMap.fourierTransformCLM ℂ)
      (partialFourierSpatial_timeSliceSchwartz
        (d := d) (n := m) ψ rψ tψ ξψ))
```

where `tφ` and `tψ` are the nonnegative frozen background-time maps produced
after OS I Lemma 8.4 has interchanged the time Fourier/Laplace order. The
shifted representative `timeShiftSchwartzNPoint τ ψ` must be gone before this
bridge is applied; it is handled by the positive-support time-interchange, not
by `hψg` pointwise.

Readiness reconciliation with the 2026-04-13 review thread:

* The corrected route now has two active non-finite-height packets. The hPsi
  packet identifies the canonical witness with the OS holomorphic matrix
  element on the positive imaginary axis. The Lemma-8.4 shell-limit packet
  identifies the pointwise Wightman time-shift value with the canonical witness
  at that same positive imaginary-axis point.
* The finite-height shell theorem is **withdrawn** as an implementation target,
  not merely postponed. The fixed-`x` audit shows that its intended scalar
  expansion would have to identify the oscillatory shell factor with the
  Laplace-damped positive-energy factor at finite height.
* Do not describe the missing item as "prove the shell kernel has the same
  dual-cone factorization as the horizontal kernel." That is the withdrawn raw
  kernel route. The raw diagnostic remains true: before the OS I Lemma-8.4
  time-interchange, the shell and horizontal kernels carry different
  exponential factors. The next implementable targets are
  `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`
  and
  `lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport`,
  with frozen-slice residuals used only after the shifted time variable has
  been eliminated.

The following finite-height frozen-slice cancellation lemma is still fully
specified and may be useful as support after the positive-gap API is public,
but it is no longer a certificate for a finite-height shell/horizontal theorem:

```lean
private theorem
    finiteHeight_frozenSliceResidual_eq_zero_on_positiveGap
    {n m : ℕ}
    {φ : SchwartzNPoint d n} {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n)
    (rψ : Fin m)
    (u : Fin (n + m) → ℝ)
    (hu : u ∈ positiveGapOrthant (n + m))
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    let tφ : Fin n → ℝ :=
      absTimesOfTailGapsSplitLeft (n := n) (m := m) u
    let tψ : Fin m → ℝ :=
      absTimesOfTailGapsSplitRight (n := n) (m := m) u
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz
            (d := d) (n := n) φ rφ tφ ξφ))
    -
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz
            (d := d) (n := m) ψ rψ tψ ξψ)) =
    0
```

Proof transcript:

1. Introduce the same `tφ` and `tψ` abbreviations as in
   `section43_frozenSlicePairing_eq_of_transport_on_positiveGap`.
2. Let
   `hpair := section43_frozenSlicePairing_eq_of_transport_on_positiveGap
      (d := d) hφf hψg rφ rψ u hu ξφ ξψ`.
3. Close by `exact sub_eq_zero.mpr (by simpa [tφ, tψ] using hpair)`.

This is the complete local cancellation theorem. It does **not** make a
finite-height shell theorem ready, and after the fixed-`x` audit it should not
be used as a certificate for one. The finite-height scalar chain below is
retained as a historical draft because it records useful quotient-apply
bookkeeping, but it is not an implementation plan on the corrected route.

Historical finite-height support rewrite:

The formal descended-`ψ_Z` rewrite below is still a valid quotient-apply
normalization, but after the fixed-`x` audit it is not on the critical path and
does not make the finite-height scalar theorem implementation-ready.

```lean
private theorem
    integrated_descendedPsiZ_eq_integrated_TW_psiZ
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact
    ∫ x : ℝ,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        TW
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D (ψZxε x)) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    ∫ x : ℝ,
      TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

Proof transcript:

1. Introduce `ψZxε`, `ψZt`, and `TW`.
2. Apply `MeasureTheory.integral_congr_ae`.
3. At each `x`, rewrite by
   `OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply`
   with
   `hT_supp :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
        (d := d) OS lgc hm φ ψ hψ_compact`
   and `f := ψZxε x`.
4. Close by `simpa [ψZxε, ψZt, TW]`.

Withdrawn hard shell-side draft:

```lean
private theorem
    bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_descendedPsiZ
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact
    (∫ x : NPointDomain d (n + m),
      bvt_F OS lgc (n + m) (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
            Complex.I) *
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x) =
    ∫ x : ℝ,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        TW
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D (ψZxε x)) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

This theorem was previously identified as the single hard finite-height
certificate. It is now withdrawn as an implementation target. The transcript
below is retained only as an audit record of the attempted normalizations; it
must not be used to justify a Lean proof unless a new analytic-continuation
lemma first bridges the fixed-`x` exponential mismatch recorded immediately
after it.

1. Move the displayed time-shifted canonical shell to the already-supported
   `xiShift` shell surface by
   `bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift` if the proof uses
   the existing shell/Fourier-Laplace Fubini packet. This is allowed only as
   configuration-space algebra; it is not a shell-to-horizontal comparison and
   carries no Section-4.3 content by itself.
2. Use the common `Tflat` package from
   `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`.
3. Represent only the shell side by the shell/Fourier-Laplace Fubini packet.
   The right side must remain the descended quotient pairing at this stage.
   Rewriting it by
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` here would erase
   the Section-4.3 surface and recreate the withdrawn raw horizontal-kernel
   comparison.
4. Expand the shell pointwise through
   `partialFourierSpatial_fun_eq_integral_realProd`,
   `physicsFourierFlatCLM_integral`, and `SCV.psiZ_twoPi_pairing_formula`
   until the shell contribution at each horizontal parameter `x` is a
   one-variable Section-4.3 pairing against
   `section43PositiveEnergyQuotientMap1D (ψZxε x)`.
5. Compare that pointwise descended scalar with the right-hand descended
   scalar by reducing their difference to
   `finiteHeight_frozenSliceResidual_eq_zero_on_positiveGap`.
6. Only after the theorem above is proved may the formal theorem
   `integrated_descendedPsiZ_eq_integrated_TW_psiZ` rewrite the descended
   quotient integral to the `TW ((SchwartzMap.fourierTransformCLM ℂ) ...)`
   integral. This final rewrite is not part of the hard shell expansion.
7. The frequency/height factors that survive the shell expansion must already
   be present in the one-variable descended `ψ_Z` scalar. If Lean shows a
   residual factor not shared by the descended scalar, stop and record the
   exact factor mismatch here. Do not repair it by changing the theorem
   surface.

Fixed-`x` expansion audit, 2026-04-13:

The requested fixed-horizontal-parameter expansion exposes the same obstruction
as the raw-kernel diagnostic. After the allowed
`bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift` algebra and the
shell/Fourier-Laplace Fubini packet, the dual-cone shell factor still contains
the real-time oscillatory term

```lean
Complex.exp (-(Complex.I * (t : ℂ) * (lam ξ : ℂ))) *
  Complex.exp (-(ε : ℂ) * (ηCanonicalPair ξ : ℂ))
```

By contrast, the fixed-`x` descended `ψ_Z` pairing, before the final formal
quotient-apply rewrite, evaluates the same one-variable positive-energy
frequency by the Paley-Wiener kernel as

```lean
(ψZxε x) (-lam ξ / (2 * Real.pi))
```

and the subsequent `x`-pairing against `𝓕ψZt` gives the Laplace damping

```lean
Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam ξ / (2 * Real.pi))) *
  Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam ξ / (2 * Real.pi)))
```

using exactly the already-checked production lemmas
`horizontalPhasePairingCLM_fourierTransform`,
`horizontalPaley_phase_xIntegral_eq_of_nonneg`, and
`horizontalKernel_pointwise_eq_exp_of_mem_dualCone`.

Therefore the missing fixed-`x` expansion is not merely incomplete: as stated,
the finite-height theorem

```lean
bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_descendedPsiZ
```

would force equality between an oscillatory real-time shell factor and a
Laplace-damped positive-energy factor before taking a boundary-value or
identity-theorem limit. The Section-4.3 frozen-slice bridge can replace
ambient representatives by transported positive-time representatives; it does
not by itself turn `exp (-I t lam)` into `exp (t lam)` at finite height.

Consequently this finite-height scalar theorem is **withdrawn as an
implementation target** unless a new, explicitly stated analytic continuation
lemma first bridges exactly the displayed exponential mismatch. No such lemma
exists in production, and adding one under a wrapper name would violate the
current route discipline.

Corrected implementation consequence:

1. Keep `section43_frozenSlicePairing_eq_of_transport_on_positiveGap` and
   `finiteHeight_frozenSliceResidual_eq_zero_on_positiveGap` as useful local
   Section-4.3 scalar facts.
2. Do not attempt
   `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_descendedPsiZ`
   or
   `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ`
   as the next Lean theorem.
3. Move the implementation frontier to the two non-finite-height
   time-interchange packets: the Lemma-8.4 shell-limit supplier
   `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`
   and the hPsi/OS-holomorphic supplier
   `lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport`.
   These are the places where OS I `(4.23) -> (4.24)` and Lemma 8.4
   legitimately convert the real-time Wightman pairing into the
   semigroup/Laplace scalar.
4. After those packets are implemented, either use the existing direct consumer
   `kernel_eq_of_osHolomorphicValue_eq_bvt_W_timeShift_on_positiveReals` from
   the pointwise positive-real equality, or use
   `lemma42_matrix_element_time_interchange` with the formal shell-limit
   supplier documented above. Do not derive the shell limit from the withdrawn
   finite-height equality.

The following formal transitivity block is retained only as the historical
finite-height plan. It must not be implemented unless the withdrawn shell-side
theorem is revived by a new explicit analytic-continuation lemma for the
exponential mismatch recorded above:

```lean
private theorem
    bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ
    -- same hypotheses as
    -- `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_descendedPsiZ`
```

Proof transcript:

1. Let `hShellDesc` be
   `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_descendedPsiZ`.
2. Let `hDescTW` be
   `integrated_descendedPsiZ_eq_integrated_TW_psiZ`.
3. Close by `exact hShellDesc.trans hDescTW`.

Historical support theorem for the withdrawn full scalar bridge:

The current production file has only the positive-imaginary-axis meeting point

```lean
partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ
```

but the horizontal integral in the withdrawn finite-height bridge uses
`w = (x : ℂ) + ε * Complex.I`. If that bridge is ever revived by a new
analytic-continuation theorem, one would first generalize the imag-axis theorem
to the full upper half-plane:

```lean
private theorem
    partialFourierSpatial_timeSliceCanonicalExtension_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {w : ℂ} (hw : 0 < w.im) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ w =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
        (fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) f r t ξ))
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * w))
            (by
              have hscaled : 0 < (2 * Real.pi) * w.im :=
                mul_pos Real.two_pi_pos hw
              simpa [Complex.mul_im] using hscaled)))
```

Proof transcript:

1. Let
   `T := fourierInvPairingCLM
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)`
   and
   `ψ := SCV.schwartzPsiZ (((2 * Real.pi : ℂ) * w)) _`.
2. Prove
   `fourierPairingDescendsToSection43PositiveEnergy1D ... (section43PositiveEnergyQuotientMap1D ψ)
     = T ((SchwartzMap.fourierTransformCLM ℂ) ψ)`
   by `fourierPairingDescendsToSection43PositiveEnergy1D_apply`.
3. Unfold
   `partialFourierSpatial_timeSliceCanonicalExtension` at `w`; the guard is
   `dif_pos hw`.
4. Unfold `SCV.fourierLaplaceExt_eq`; the argument is already
   `((2 * Real.pi : ℂ) * w)`, so the imag-axis-only `harg` rewrite from the
   existing theorem disappears. The final line should be
   `simpa [T, ψ] using hApply.symm`.

This is a genuine missing theorem because it moves an existing imag-axis
bridge to the exact horizontal surface used by the Paley packet. It should be
implemented before the larger scalar bridge, and it should not be replaced by a
new `H` witness or by a wrapper around the imag-axis theorem.

The analogous Wightman time-shift functional bridge should also be generalized
from the imag-axis helper already present in production:

```lean
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    {w : ℂ} (hw : 0 < w.im) :
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact w =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc f g hg_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * w))
            (by
              have hscaled : 0 < (2 * Real.pi) * w.im :=
                mul_pos Real.two_pi_pos hw
              simpa [Complex.mul_im] using hscaled)))
```

Proof transcript:

1. Let `TW` be
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional (d := d) OS lgc f g hg_compact`
   and let `ψ := SCV.schwartzPsiZ (((2 * Real.pi : ℂ) * w)) _`.
2. Rewrite the left side by the upper-half-plane Fourier-Laplace formula for
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension`. If production only
   exposes the horizontal real-parameter theorem
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral`,
   first add the general theorem

```lean
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    {w : ℂ} (hw : 0 < w.im) :
    let ψ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * w))
        (by
          have hscaled : 0 < (2 * Real.pi) * w.im :=
            mul_pos Real.two_pi_pos hw
          simpa [Complex.mul_im] using hscaled)
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact w =
      ∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ g)) *
        (SchwartzMap.fourierTransformCLM ℂ ψ) τ
```

   This helper is a direct definition/unfolding theorem for the canonical
   witness, not a new comparison theorem.
3. Rewrite the descended pairing by
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
4. Close by `simpa [TW, ψ]`.

These two upper-half-plane `ψ_Z` bridge lemmas are the first concrete Lean
support needed by `integrated_TW_psiZ_to_section43SliceIntegral`. They also
make clear why the existing imag-axis theorems are insufficient for the
finite-height horizontal integral, even though they remain enough for the final
`hH_imag_os` consumer.

Second concrete support theorem: the Section-4.3 `ψ_Z` time-shift comparison
must also be stated on the upper half-plane, with the OS holomorphic parameter
rotated into the right half-plane. The imag-axis theorem displayed later in the
hPsi section is only the specialization `w = t * Complex.I`.

```lean
private theorem
    section43_timeShift_descendedPsiZ_eq_osHolomorphicValue_upperHalfPlane_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {w : ℂ} (hw : 0 < w.im) :
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact)
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
        (d := d) OS lgc hm φ ψ hψ_compact)
      (section43PositiveEnergyQuotientMap1D
        (SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * w))
          (by
            have hscaled : 0 < (2 * Real.pi) * w.im :=
              mul_pos Real.two_pi_pos hw
            simpa [Complex.mul_im] using hscaled))) =
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f.1 f.2)
      (PositiveTimeBorchersSequence.single m g.1 g.2)
      (-Complex.I * w)
```

Proof transcript:

1. Define the upper-half-plane function `L w` by the left side, guarded with
   `if hw : 0 < w.im then ... else 0`, and define `R w` by
   `OSInnerProductTimeShiftHolomorphicValue ... (-Complex.I * w)`.
2. Prove `DifferentiableOn ℂ L SCV.upperHalfPlane` from the previous
   upper-half-plane Wightman/`ψ_Z` bridge and the differentiability of
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension`. Equivalently, first
   prove that `L w` equals
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension (d := d) OS lgc φ ψ
     hψ_compact w`
   on `SCV.upperHalfPlane`, then reuse its differentiability.
3. Prove `DifferentiableOn ℂ R SCV.upperHalfPlane` by composing
   `OSInnerProductTimeShiftHolomorphicValue_differentiableOn` on the right
   half-plane with the linear map `w ↦ -Complex.I * w`; on
   `SCV.upperHalfPlane`, `(-Complex.I * w).re = w.im`.
4. On the positive imaginary axis, set `w = t * Complex.I`. The left side
   reduces to
   `section43_timeShift_descendedPsiZ_eq_osHolomorphicValue_of_section43Transport`
   from the hPsi section, and the right side simplifies because
   `-Complex.I * (t * Complex.I) = t`.
5. Apply `identity_theorem_upperHalfPlane` to conclude equality for every
   `w` with `0 < w.im`, then discharge the guard by `dif_pos hw`.

This theorem is not a replacement for the shell-to-Laplace limit theorem. Its
role is to make the horizontal-line `TW` side available on the same
upper-half-plane surface as the rotated OS holomorphic scalar. It is also the
clean way to avoid pretending that the imag-axis hPsi theorem can be rewritten
at `x + ε i`.

Important correction to the shell-side gate:

The next live theorem must not assert finite-height equality between the
canonical `bvt_F` shell and the rotated OS horizontal integral. The canonical
shell height is

```lean
canonicalForwardConeDirection (d := d) (n + m) k 0 = (k : ℕ) + 1
```

whereas the one-variable rotated OS horizontal integral sees only the scalar
height `ε` through `-Complex.I * ((x : ℂ) + ε * Complex.I)`. These are
different regularizations. OS I `(4.23) -> (4.24)` is therefore a
shell-to-Laplace comparison on the boundary-value limit surface, not permission
to state an arbitrary positive-height shell equality. The raw finite-height
statement

```lean
canonicalShell_eq_rotated_OSHolomorphic_horizontalIntegral_of_section43Transport
```

is withdrawn as an implementation target unless a separate proof first shows
that the extra canonical-height dependence cancels on the transported scalar.
No current production theorem supplies such a cancellation.

The old diagnostic shell-side theorem was the canonical horizontal
zero-residual theorem below. It is no longer the corrected live theorem; the
live shell-side theorem is the pointwise Lemma-8.4 supplier
`lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)
```

This was the older limit-level shell half consumed by

```lean
tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero
```

It is retained as a diagnostic obstruction theorem only. Its previous proof
plan used the withdrawn finite-height iterated residual
`bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport`,
so it is not the live shell-limit route.

The live canonical-shell limit theorem is formal from the pointwise Lemma-8.4
identity, not from a zero residual:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport
    -- same hypotheses as above
```

Proof transcript:

1. Let `hShell` be
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`.
2. Let `hPoint` be
   `bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_section43Transport`,
   whose only hard input is
   `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`.
3. Rewrite the target of `hShell` by `hPoint` and close by `simpa`.

The final semigroup-target limit consumed by `lemma42_matrix_element_time_interchange`
is then also formal:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_of_section43Transport
    -- same hypotheses as above
```

Proof transcript:

1. Let `hCanonLimit` be
   `tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport`.
2. Let `hCanonOS` be
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`
   or the equivalent upper-half-plane bridge specialized to `w = t * Complex.I`.
3. Rewrite the target of `hCanonLimit` by `hCanonOS`; close by `simpa`.

Guard obligations for this corrected theorem chain:

1. The finite positive `ε` is used only inside the canonical boundary-value
   shell. The theorem conclusion is a limit as `ε -> 0+`; no finite-height
   shell/horizontal equality is asserted.
2. The canonical forward-cone height and the one-variable horizontal height are
   not identified pointwise.
3. The right-hand horizontal integral is justified by the existing canonical
   witness boundary-value theorem and the horizontal Paley packet. If the OS
   horizontal integral is displayed in a later helper, use polynomial growth of
   the rotated OS holomorphic matrix element and rapid decay of
   `(SchwartzMap.fourierTransformCLM ℂ ψZ)`.
4. The Wick-rotation sign must still be checked locally:

```lean
have hrot_re :
    (-Complex.I * ((x : ℂ) + ε * Complex.I)).re = ε := by
  simp [Complex.mul_re]

have hrot_imagAxis :
    -Complex.I * (t * Complex.I) = (t : ℂ) := by
  ring_nf
  simp [Complex.I_mul_I]
```

   These two rewrites are the guard against accidentally using
   `Complex.I * w`, `w * Complex.I`, or a same-domain theorem with the wrong
   half-plane.
5. The Section-4.3 hypotheses `hφf` and `hψg` may replace unshifted slice
   representatives only after the time variable has been isolated in the
   Paley-Wiener/OS holomorphic expression. They must never rewrite
   `timeShiftSchwartzNPoint (d := d) τ ψ` pointwise.

This correction makes the current live gap narrower and safer: the docs now
need the proof transcript for
`lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`
to be fully expanded through the one-variable positive-support interchange,
not a finite-height shell/OS equality.

1. Paper target:
   OS I Lemma 4.2, specifically the passage from `(4.23)` to `(4.24)` on p. 96.
   The spatial variables are handled by the existing
   `partialFourierSpatial_fun` / `partialFourierSpatial_timeSliceSchwartz`
   normal forms and the `fourierInvPairingCLM` slice-pairing lemmas listed
   below. The time variable is the one-variable positive-support boundary
   theorem cited there as Lemma 8.4. The current proof uses the OS-II
   correction only through the already-built `OSLinearGrowthCondition` /
   boundary-value construction; it must not invoke the false many-variable
   OS-I Lemma 8.8.
2. Wightman time-shift functional expansion and support:
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport`
   in `OSToWightmanBoundaryValueLimits.lean`.
3. One-variable quotient descent:
   `section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg` and
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` in
   `Section43Codomain.lean`.
4. Ambient-to-preimage slice bridge:
   `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport`,
   `section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   and
   `fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport`
   in `OSToWightmanPositivity.lean`.
5. Scalar slice-pairing bridge:
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`,
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   and
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`
   in `OSToWightmanPositivity.lean`.
6. Positive-support facts for slices:
   `tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`,
   `partialFourierSpatial_timeSliceTest`, and
   `fourierInvPairing_hasOneSidedFourierSupport` in
   `OSToWightmanPositivity.lean`.
7. One-variable analytic and canonical-slice comparison used after quotient
   rewriting:
   `complexLaplaceTransform_hasPaleyWienerExtension`,
   `fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform`,
   `partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`,
   `section43_iteratedSlice_descendedPairing_imagAxis`, and
   `section43_iteratedSlice_descendedPairing` in
   `OSToWightmanPositivity.lean`.
8. Kernel-zero support facts:
   `SCV.fourier_pairing_vanishes_of_eqOn_nonneg` in `SCV/PaleyWiener.lean`
   and `SCV.psiZ_eq_exp_of_nonneg` in `SCV/FourierLaplaceCore.lean`.

Hidden obligations for
`lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_section43Transport`:

1. The `ψ_Z` constructor positivity proof comes from
   `mul_pos Real.two_pi_pos ht`; the nonnegativity needed to evaluate
   `ψ_Z` pointwise by `SCV.psiZ_eq_exp_of_nonneg` comes from the positive-time
   slice support theorem. These two positivity proofs must not be interchanged.
2. The selected time slice is the embedded right-block index
   `⟨n, Nat.lt_add_of_pos_right hm⟩`, equivalently the local right-factor
   coordinate `rψ : Fin m := ⟨0, hm⟩` after the tensor-product expansion. Any
   helper with a different selected coordinate is off-surface for this theorem.
3. Every call to a one-variable quotient theorem needs a proof
   `∀ i, i ≠ r → 0 ≤ t i` for the frozen background times. Those proofs must
   be carried explicitly by the local slice helper that invokes the quotient
   theorem. In the global Lemma-8.4 proof, the same proof must be derived from
   the concrete frozen-time map produced by the expansion. If that map is later
   expressed via cumulative tail gaps, first add the corresponding
   `absTimesOfTailGaps*` declarations to production; do not cite the
   documentation-only names as existing lemmas. The support hypotheses `f.2`
   and `g.2` only prove vanishing of the positive-time preimage side outside
   the orthant; they do not make an arbitrary ambient frozen background
   nonnegative.
4. `hφf` and `hψg` may be used only through
   `section43PositiveEnergyQuotientMap` and the slice bridge theorems above.
   Directly rewriting `(φ : NPointDomain d n → ℂ)` to `f.1` or
   `(ψ : NPointDomain d m → ℂ)` to `g.1` is forbidden.
5. `hf_compact` and `hg_compact` are carried here so this theorem has the same
   surface as the final `lemma42` adapter and the optional `singleSplit`
   diagnostic bridge. They should not be used to rewrite ambient representatives
   directly. `hψ_compact` is the compactness hypothesis actually needed by the
   canonical Wightman time-shift functional and witness.
6. The descended pairing may be expanded only with
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`; do not unfold
   quotient constructions or choose representatives by hand.
7. Integrability source is the existing Wightman time-shift tempered functional,
   one-sided Fourier-support package, and slice-pairing package. Before adding
   any integrability helper, record the exact Lean side goal in this subsection
   and make the helper prove precisely that goal under the displayed
   `φ ψ f g hφf hψg t ht` hypotheses.
8. The Fubini exchange must be applied to
   `T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ`, never directly to
   `TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ`. The conversion back to the real-line
   outer integral is exactly `h_outer_real`; do not introduce a Fourier
   transform / reindex commutation lemma for this step.
9. No step may infer equality of
   `timeShiftSchwartzNPoint (d := d) t ψ` and
   `timeShiftSchwartzNPoint (d := d) t (EuclideanPositiveTimeComponent.ofSubmodule g).1`
   from `hψg`. The shift samples `ψ` at `x - timeShiftVec d t`, so the
   Section-4.3 nonnegative-region equality for the unshifted representatives
   is insufficient. The shifted right factor can only be compared after the
   time-shift distribution has been paired with the Paley-Wiener kernel and
   reduced to unshifted positive-support slice data.

Once a transported shell-limit theorem and the OS holomorphic identification are
available, the semigroup-target version is purely formal. The transported
shell-limit theorem must not be proved by the withdrawn arbitrary
shell-minus-horizontal EqOn; it must use the Section-4.3 hypotheses `hφf` and
`hψg` inside the scalar comparison.

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f.1 f.2)
          (PositiveTimeBorchersSequence.single m g.1 g.2) (t : ℂ)))
```

Proof transcript:

1. Prove the canonical-extension variant under the same `hφf`/`hψg`
   hypotheses from the Lemma-8.4 pointwise supplier, then rewrite by the
   OS-holomorphic identification supplied by hPsi.
2. If using the canonical-extension variant, let `hCanonLimit` be
   `tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport`
   specialized to the fixed `t ht`, and let `hCanonOS` be
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`
   specialized to the same `t ht`.
3. Rewrite the target of `hCanonLimit` by `hCanonOS` and close with `simpa`.
   No same-shell Euclidean/Wightman equality is used in this direct route.

Do not prove the normalized iterated-residual theorem from the semigroup shell
limit or from the canonical witness's OS identification. That would be circular
on the current route. Also do not attempt to prove the arbitrary
shell-minus-horizontal zero theorem: after the horizontal scalar computation it
is diagnostic only, not live route work. The remaining live route work is the
pair of transported non-finite-height Lemma-8.4 comparisons: the pointwise
shell-limit supplier and the Fourier-tested hPsi supplier.

The OS-side comparison needed by the same consumer is the following exact
hypothesis supplier for the already-proved ambient/preimage reducer:

```lean
private theorem
    descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g.1 g.2⟧)) : OSHilbertSpace OS))
    ∀ t : ℝ, ∀ ht : 0 < t,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) =
      selfAdjointSpectralBoundaryValueOffdiagCLM
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        xF xG
        (SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht))
```

Proof transcript for this OS-side theorem:

1. Expand the descended Wightman pairing with
   `OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply`
   and `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
2. Prove or invoke the off-diagonal core helper
   `descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport`.
   This is the only hard comparison inside `hPsi`: it converts the descended
   Wightman `ψ_Z` boundary value directly to
   `ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag`.
3. Rewrite the OS spectral boundary side with
   `selfAdjointSpectralBoundaryValueOffdiagCLM_apply` and
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`,
   using `spectrum_osTimeShiftHilbert_subset_Icc`.
4. Close by transitivity through the common off-diagonal spectral Laplace
   scalar. Do not introduce Wightman-side diagonal polarization and do not add
   a compactness hypothesis for `φ`.

Dependency inventory for `descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport`:

1. Wightman-side pairing expansion:
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` in
   `Section43Codomain.lean` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` in
   `OSToWightmanBoundaryValueLimits.lean`.
2. Wightman-side support:
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport`
   in `OSToWightmanBoundaryValueLimits.lean`.
3. OS spectral boundary conversion:
   `selfAdjointSpectralBoundaryValueOffdiagCLM_apply` in
   `OSToWightmanSemigroup.lean` and
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`
   in `OSToWightmanSemigroup.lean`.
4. Positive spectral support for the semigroup:
   `spectrum_osTimeShiftHilbert_subset_Icc` in `OSToWightmanSemigroup.lean`.
5. The `ψ_Z` kernel evaluation:
   `SCV.psiZ_eq_exp_of_nonneg` in `SCV/FourierLaplaceCore.lean`, used only after the
   spectral variable has been restricted to the nonnegative half-line.
6. The semigroup scalar identity used in the off-diagonal core helper:
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
   in `OSToWightmanSemigroup.lean`.
7. The full-kernel dual-cone descent plus unshifted full-orthant slice adapter
   listed for the finite-height normal-form helper supplies only the unshifted
   ambient-to-positive-time reduction after the time-shift distribution has
   been paired with `ψ_Z`. The one-variable slice bridge inventory is used only
   inside the dual-cone pointwise EqOn proof, after the tail-direction
   nonpositivity lemmas have supplied nonnegative cumulative times and those
   times have been converted to nonnegative absolute background times. No
   additional ambient equality principle is permitted here, and in particular
   `hψg` must not be applied directly to `timeShiftSchwartzNPoint t ψ`.

Hidden obligations for this `hPsi` theorem:

1. The `let xF` and `let xG` vectors must remain exactly the OS Hilbert classes
   of `PositiveTimeBorchersSequence.single n f.1 f.2` and
   `PositiveTimeBorchersSequence.single m g.1 g.2`; do not replace them by
   ambient representatives.
2. The preferred proof does not expand the OS offdiag boundary into four
   diagonal terms; it converts it to the off-diagonal spectral Laplace scalar
   by the existing `..._psiZ` theorem. If a local simplification temporarily
   exposes the four diagonal terms, they must stay in the order expected by
   `selfAdjointSpectralBoundaryValueOffdiag`, and the Wightman side must still
   remain off-diagonal.
3. Every use of `SCV.psiZ_eq_exp_of_nonneg` needs the nonnegativity proof coming
   from the spectral support theorem, not from the sign of the external
   positive real parameter `t`.
4. The Wightman functional is
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional (d := d) OS lgc φ ψ hψ_compact`;
   its `φ ψ` arguments are not rewritten directly. Only the one-variable slice
   quotient classes are transported using `hφf` and `hψg`.
5. This theorem supplies only the `hPsi` hypothesis for the existing
   canonical-to-OS reducer. It should not also rewrite the canonical witness or
   the OS holomorphic value; those steps belong to
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`.

Critical hPsi correction: do **not** polarize the Wightman side diagonally.
The live Wightman functional

```lean
bvt_W_conjTensorProduct_timeShiftTemperedFunctional
  (d := d) OS lgc φ ψ hψ_compact
```

only requires compactness of the right-shifted factor `ψ`. A diagonal
polarization proof on the Wightman side would also require functionals with
`φ` as a right-shifted factor, hence a compactness hypothesis for `φ`, which is
not part of the theorem surface and should not be added. The hPsi proof must
therefore stay genuinely off-diagonal on the Wightman side.

The positive-support time-shift distribution theorem is the expanded integral
form of the off-diagonal core. It is the place where the shifted right factor
is handled, and it is the exact Lean surface that must be proved before the
descended `ψ_Z` theorem can be a one-line quotient expansion.

Important correction: the active theorem must land directly on the
off-diagonal spectral Laplace scalar. It must **not** land first on
`bvtSingleSplitXiShiftScalar`. The raw single-split tube route has been
retired, and using the single-split scalar as the hard target would smuggle the
invalid `zSplit` surface back into the proof. The semigroup scalar is already
available on the correct OS Hilbert vectors, so the non-circular transported
comparison is:

```lean
private theorem
    integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    let A : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
      osTimeShiftHilbert (d := d) OS lgc 1 one_pos
    let hA : IsSelfAdjoint A :=
      osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g.1 g.2⟧)) : OSHilbertSpace OS))
    ∀ t : ℝ, ∀ ht : 0 < t,
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)
```

This is the hard theorem. It is off-diagonal on both sides, uses the ambient
Wightman representatives only through the time-shift functional paired against
`𝓕ψ_Z`, and uses the Section-4.3 transport hypotheses only through quotient /
slice descent. It does not require compactness of `φ`.

Lean-ready proof transcript for this active theorem:

1. Fix `t ht` and introduce `ψZ`, `A`, `hA`, `xF`, and `xG`.
2. Rewrite the left side as
   `OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D TW hTW
      (section43PositiveEnergyQuotientMap1D ψZ)`
   using the already-proved production theorem
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D`.
3. Apply the Section-4.3 transported slice comparison on the quotient class of
   `ψZ`. This is the remaining mathematical core: after expanding the
   one-variable quotient by `fourierPairingDescendsToSection43PositiveEnergy1D_apply`,
   the proof must use the full positive-energy slice bridge, not a pointwise
   rewrite of `timeShiftSchwartzNPoint t ψ`.
4. Convert the resulting OS-side slice scalar to
   `ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)`
   by
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
   only after the Section-4.3 quotient comparison has supplied the OS Hilbert
   vectors `xF` and `xG`.
5. Close by `simpa [ψZ, A, hA, xF, xG]`. If Lean exposes an additional side
   goal, record that exact goal in this subsection before adding support
   lemmas.

Implementation refinement after checking the production semigroup API:

The theorem above should not try to recognize the semigroup spectral scalar
directly from the Wightman slice expansion. The sharper local target is the
Schwinger scalar already used by
`OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single`:

```lean
private theorem
    lemma42_timeShift_pairing_eq_osSchwingerValue_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    (∫ τ : ℝ,
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
      (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
    OS.S (n + m)
      (ZeroDiagonalSchwartz.ofClassical
        (f.1.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g.1)))
```

This is the real OS-I `(4.23) -> (4.24)` hPsi theorem. It is not a wrapper:
it is exactly the Wightman `ψ_Z`-paired scalar on the left and the Euclidean
Schwinger scalar on the right. The already-compiled
`lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport` should
then become formal:

```lean
  have hSchw :=
    lemma42_timeShift_pairing_eq_osSchwingerValue_of_section43Transport
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact)
      (f := f) (g := g) (hf_compact := hf_compact)
      (hg_compact := hg_compact) hφf hψg ht
  have hOS :
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f.1 f.2)
        (PositiveTimeBorchersSequence.single m g.1 g.2) (t : ℂ) =
      OS.S (n + m)
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) :=
    OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
      (d := d) OS lgc f.1 f.2 g.1 g.2 hg_compact t ht
  exact hSchw.trans hOS.symm
```

The proof of
`lemma42_timeShift_pairing_eq_osSchwingerValue_of_section43Transport` is the
only non-formal part of the hPsi packet. As with the shell supplier, the hard
mathematics should be placed on the descended one-variable quotient surface,
because the integral-to-descended expansion is already formal:

```lean
private theorem
    section43_timeShift_descendedPsiZ_eq_osSchwingerValue_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact)
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
        (d := d) OS lgc hm φ ψ hψ_compact)
      (section43PositiveEnergyQuotientMap1D ψZ) =
    OS.S (n + m)
      (ZeroDiagonalSchwartz.ofClassical
        (f.1.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g.1)))
```

Then the integral-facing hPsi theorem is formal by transitivity through
`integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D`.
This is the preferred Lean surface because it prevents the proof attempt from
unfolding the Wightman tempered functional or inventing new integrability
lemmas when the only missing mathematics is the Section-4.3 slice comparison.

Implementation transcript for the descended Schwinger theorem:

1. Expand the left side with
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` only inside the
   local slice proof after the partial-spatial/time-slice normal form is
   exposed. Do not unfold the global quotient construction.
2. Use the opposite-factor slice bridge
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
   after the spatial/time-slice expansion has produced concrete
   `rφ tφ ξφ rψ tψ ξψ` data. The right index is
   `rψ := headSliceIndex hm`, and the proof of `htψ` is
   `orderedHeadGapTimes_nonneg_of_orderedPositive hm`.
3. On the left factor, if `0 < n`, use the same head-gap packet after reindexing
   through the Borchers reversal in `SchwartzMap.conjTensorProduct_apply`. If
   `n = 0`, do not add a new hypothesis; use the production helper
   `section43_zero_left_repr_eq_transport_pointwise` before introducing any
   left slice.
4. Apply `lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ` only to
   the concrete one-variable functional
   `fourierInvPairingCLM gSlice` or `fourierInvPairingCLM fSlice`, with
   one-sided support supplied by
   `fourierInvPairing_hasOneSidedFourierSupport` and
   `tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`.
5. After the slice bridge has replaced ambient slices by the transported
   positive-time slices, collapse the expanded positive-time scalar to
   `OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
     (f.1.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g.1)))`
   by the OS reconstruction side of Lemma 4.2, not by any Wightman-side
   polarization or finite-height shell equality.
6. Any Lean side goal not of the forms `htφ`, `htψ`, quotient-slice equality,
   one-sided support, or the final Schwinger scalar collapse means the proof
   docs are still missing a theorem. Record that exact goal before editing
   production again.

Optional downstream scalar-normalization packet. The local abbreviation
`bvtSingleSplitXiShiftScalar` is the explicit real-axis integral from
`bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`; it may still be useful as
a diagnostic after the main route is closed, but it is not an active
implementation target for hPsi or shell-to-Laplace.

Retired proof transcript for the old single-split integral theorem:

The following transcript is superseded by the canonical-shell correction in
§5.9.4a.1.ε. It is retained only to explain why the frequency-side `Tflat`
idea was introduced; it is not an implementation target on the current route.

1. Fix `t ht` and abbreviate `ψZ`.
2. Expand the left side only far enough to expose the Wightman time-shift
   distribution paired with `(SchwartzMap.fourierTransformCLM ℂ) ψZ`; do not
   replace the shifted ambient representative pointwise.
3. Obtain one common frequency-side distribution `Tflat` from the strengthened
   BVLimits package
   `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`
   below. This single package supplies both:
   the boundary representation
   `bvt_W ... = Tflat (physicsFourierFlatCLM ...)` for the ambient side, and
   the tube representation
   `bvt_F ... = fourierLaplaceExtMultiDim ... Tflat ...` for the transported
   single-split side. This is the non-circular bridge: `KTransport` must be
   built from the Fourier-Laplace representation of `bvt_F`, not by postulating
   another Wightman boundary pairing.
4. Construct `KAmbient` by applying `schwartz_clm_fubini_exchange` to the
   real-time translated Wightman orbit, exactly in the style of
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`.
   The parameter space is `Fin M → ℝ`, where `M = (n + m) * (d + 1)`, with
   first coordinate the real shift `τ` and the remaining coordinates integrated
   against the normalized bump `β`; the scalar test factor is the padded
   `χhat = (SchwartzMap.fourierTransformCLM ℂ) ψZ`.
5. Construct `KTransport` by a different Fubini application. Its parameter is
   the flattened Euclidean configuration `yflat : Fin M → ℝ`; its scalar test
   factor is
   `flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1)`, not the
   padded `χhat`; and its Schwartz-family value is the tube-safe
   Fourier-Laplace kernel at the flattened `xiShift` point. The FL
   representation rewrites the pointwise scalar
   `bvt_F ... (xiShift ... (wickRotatePoint y) ((t : ℂ) * Complex.I))`
   to `Tflat (multiDimPsiZDynamic ... (zSplitFlat y))` on the support of this
   positive-time test. The support-safe extension/cutoff packet below supplies
   the global continuity and polynomial-growth side conditions required by
   `schwartz_clm_fubini_exchange`.
6. Use `psiZ_twoPi_pairing_formula` only in the pointwise evaluation of
   `KAmbient`, after `hKAmbient_eval ξ` has reduced the Fubini output to the
   real-time integral in `τ`. This is the only place where the shifted variable
   `τ` is integrated out. Do not use `SCV.psiZ_eq_exp_of_nonneg`.
7. Prove the full-kernel EqOn:
   `Set.EqOn KAmbient KTransport dualCone`.
   For `ξ` in the dual cone, rewrite both sides by the Fubini pointwise fields.
   Then expand `physicsFourierFlatCLM` on the ambient side and
   `multiDimPsiZDynamic` on the transported side. On the dual cone, the
   dynamic radius/cutoff is irrelevant by
   `fourierLaplaceExtMultiDim_eq_dynamic` and
   `multiDimPsiZR_eval_eq_of_support`, so both sides reduce to the same
   OS I `(4.23) -> (4.24)` slice comparison after the Section-4.3 transport
   equalities are applied.
8. Extract nonnegative frozen background times from the dual-cone hypothesis by
   `flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone` for each tail
   index. These nonnegative cumulative times replace the old positive-gap
   variable `u` in the EqOn proof.
9. Use the unshifted local adapter
   `unshifted_full_timeOrthant_descended_pairing_eq_of_section43Transport`
   pointwise in the remaining spatial variables. If the expanded formula has
   already isolated one side of the one-variable pairing, use the existing
   scalar forms
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
   and
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
   instead; these are equivalent after the full nonnegative background times
   have been supplied.
10. Apply
   `tflat_pairing_eq_of_eqOn_dualCone` to identify the two `Tflat` pairings.
11. Collapse the transported expanded formula back to
   `bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t` using the
   reverse of the same `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`,
   Fourier-Laplace representation, Fubini, and flatten/reindex normal forms.
   The transported collapse does not use `psiZ_twoPi_pairing_formula`; that
   formula belongs to the ambient real-time pairing.
12. The `n = 0` branch uses
   `section43_zero_left_repr_eq_transport_pointwise` before any left slice is
   introduced. Do not add `0 < n` to this theorem.

The old proof transcript had one non-mechanical phrase:
"put that expanded kernel into `χAmbient` / `χTransport`." The current audit of
the existing flattened support proof shows that this phrasing is too narrow for
the actual Section-4.3 transport step.

In `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`
the representative data `φ`, `ψ` enter the **full flattened Fourier-side
Schwartz kernel** through `physicsFourierFlatCLM (flattenSchwartzNPoint ...)`;
they are not carried only by a one-dimensional time-gap test. Therefore the
production blocker must not require a "same `Ψ`, different `χ`" certificate
unless a scratch expansion has already proved that strong factorization. For the
live OS-route theorem, the correct certificate is:

1. construct two full flattened Fourier-side Schwartz kernels `KAmbient` and
   `KTransport` in the domain of the chosen `Tflat`;
2. expand the Wightman `ψ_Z`-paired scalar and the transported single-split
   scalar as pairings against those kernels;
3. prove that those kernels agree on the full dual cone;
4. use the Wightman dual-cone support package to identify the pairings.

This is still exactly OS I `(4.23) -> (4.24)`: the difference is only that the
Lean support theorem should act on the full Fourier-side kernel, not on an
artificial same-`Ψ` tail-gap special case.

The required support theorem is the following general Fourier-side statement.
It can be implemented as a pure support lemma in `SCV/FourierSupportCone.lean`,
or locally in `OSToWightmanBoundaryValueLimits.lean` if we want to avoid opening
a stable SCV file:

```lean
theorem tflat_pairing_eq_of_eqOn_dualCone
    {M : ℕ} {S : Set (Fin M → ℝ)}
    (Tflat : SchwartzMap (Fin M → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp : HasFourierSupportInDualCone S Tflat)
    (KAmbient KTransport : SchwartzMap (Fin M → ℝ) ℂ)
    (hEq :
      Set.EqOn
        (KAmbient : (Fin M → ℝ) → ℂ)
        (KTransport : (Fin M → ℝ) → ℂ)
        (DualConeFlat S)) :
    Tflat KAmbient = Tflat KTransport
```

Proof transcript for
`tflat_pairing_eq_of_eqOn_dualCone`:

1. Work classically and set `Δ := KAmbient - KTransport`.
2. Prove `Δ` vanishes on the dual cone by
   `intro ξ hξ; exact sub_eq_zero.mpr (hEq hξ)`.
3. Unfold `HasFourierSupportInDualCone` and `HasFourierSupportIn` in
   `hTflat_supp`, apply it to `Δ`, and discharge the support-disjointness goal:
   if `ξ ∈ Function.support Δ` and `ξ` is in the dual cone, then the previous
   pointwise vanishing contradicts `Function.mem_support.mp`.
4. Use linearity of `Tflat`: from `Tflat (KAmbient - KTransport) = 0`, obtain
   `Tflat KAmbient = Tflat KTransport` by `map_sub` and `sub_eq_zero.mp`.

This theorem is not a wrapper. It is the exact support principle already used
inside the current one-variable Stage-5 proof, but exposed for the full
frequency-side kernels produced by `schwartz_clm_fubini_exchange`.

The common `Tflat` used by both kernels must also carry the Fourier-Laplace
representation of the interior OS holomorphic function. The existing
`exists_flattened_bvt_W_dualCone_distribution` exposes only the boundary
pairing

```lean
bvt_W OS lgc q (unflattenSchwartzNPoint φ) =
  Tflat (physicsFourierFlatCLM φ)
```

That is enough for `KAmbient`, but it is not enough for `KTransport`, whose
source scalar is the interior single-split shell built from `bvt_F`. The
following BVLimits package is therefore the next required support theorem. It
does not add a new axiom; it is a repackaging of the same
`bv_implies_fourier_support` witness together with the already-available
`fl_representation_from_bv`.

```lean
private theorem
    exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (q : ℕ) :
    let C : Set (Fin q → Fin (d + 1) → ℝ) := ForwardConeAbs d q
    let Cflat : Set (Fin (q * (d + 1)) → ℝ) :=
      (flattenCLEquivReal q (d + 1)) '' C
    ∃ Tflat : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
    ∃ hCflat_open : IsOpen Cflat,
    ∃ hCflat_conv : Convex ℝ Cflat,
    ∃ hCflat_cone : IsCone Cflat,
    ∃ hCflat_salient : IsSalientCone Cflat,
      HasFourierSupportInDualCone Cflat Tflat ∧
      (∀ φ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc q (unflattenSchwartzNPoint (d := d) φ) =
          Tflat (physicsFourierFlatCLM φ)) ∧
      (∀ z : Fin q → Fin (d + 1) → ℂ, z ∈ TubeDomainSetPi C →
        bvt_F OS lgc q z =
          fourierLaplaceExtMultiDim Cflat
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            Tflat (flattenCLEquiv q (d + 1) z))
```

Proof transcript for
`exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`:

1. Copy the initial setup of
   `exists_flattened_bvt_W_dualCone_distribution`: define
   `Wcl : SchwartzNPoint d q →L[ℂ] ℂ` from `bvt_W OS lgc q`, prove
   `hWcl`, and reuse `hC_open`, `hC_conv`, `hC_cone`, `hC_salient`,
   `hF_holo`, `hF_growth`, and `hF_bv`.
2. Set `Cflat := (flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q` and
   prove the four flattened cone facts by the same lines used in
   `vladimirov_tillmann`:
   `eR.toHomeomorph.isOpenMap _ hC_open`,
   `hC_conv.linear_image eR.toLinearEquiv.toLinearMap`, the direct cone-image
   proof using `eR.map_smul`, and the salient proof using
   `(eR.toHomeomorph.image_closure C).symm` plus `eR.injective`.
3. Apply `bv_implies_fourier_support` once, obtaining
   `⟨Tflat, hTflat_supp, hTflat_eq⟩`.
4. Before simplifying `hTflat_eq` into the `bvt_W` boundary representation,
   feed that exact equality into `fl_representation_from_bv`:

```lean
have hFL_repr :
    ∀ z ∈ TubeDomainSetPi (ForwardConeAbs d q),
      bvt_F OS lgc q z =
        fourierLaplaceExtMultiDim Cflat
          hCflat_open hCflat_conv hCflat_cone hCflat_salient
          Tflat (flattenCLEquiv q (d + 1) z) :=
  fl_representation_from_bv
    (ForwardConeAbs d q) hC_open hC_conv hC_cone hC_salient
    (bvt_F OS lgc q) hF_holo Wcl hF_bv
    Cflat rfl hCflat_open hCflat_conv hCflat_cone hCflat_salient
    Tflat hTflat_supp hTflat_eq
```

5. Return `Tflat`, the flattened cone witnesses, `hTflat_supp`, the boundary
   representation
   `by intro φ; simpa [Wcl, unflattenSchwartzNPoint] using hTflat_eq φ`,
   and `hFL_repr`.

Implementation placement: put this theorem immediately after
`exists_flattened_bvt_W_dualCone_distribution` in
`OSToWightmanBoundaryValueLimits.lean`, or replace that theorem's local proof
body by this stronger package and recover the old theorem as a short
projection. The theorem is not a wrapper because it exposes the interior
Fourier-Laplace identity that `KTransport` must consume.

#### 5.9.4a.1.ε Correction: the raw single-split tube-support packet is retired

The transported Fubini side must **not** be implemented from the raw
`singleSplit` surface displayed in the previous draft. The tempting theorem

```lean
zSplit_mem_forwardTube_of_osConjTensorProduct_support
```

is false as stated. In the simplest `n = 1`, `m = 1` case, a point in the
support of `f.osConjTensorProduct g` has its left block in the OS-reflected
support of `f`, hence its first Euclidean time is negative. The raw expression

```lean
xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)
```

does not change the first left point when `n > 0`, so the imaginary part of the
first absolute coordinate has negative time component. But
`ForwardConeAbs d (n + m)` requires the first absolute imaginary increment to
lie in `InOpenForwardCone d`, in particular to have positive time component.
Thus the raw point is not in the forward tube in general.

Operational consequence:

1. Do not invoke the strengthened multivariable Fourier-Laplace representation
   on the raw `singleSplit` integrand at `ε = 0`.
2. Do not implement `exists_transportTubeCutoff`,
   `continuous_transportPsiZFamily_with_cutoff`,
   `seminorm_transportPsiZFamily_with_cutoff_bound`, or
   `exists_transportKernel_pairing_singleSplitXiShiftScalar` from the raw
   `zSplit` surface below. Those names are retained only as historical markers
   for the rejected route.
3. The corrected shell-to-Laplace proof must stay on the canonical
   positive-height shell
   `x + ε * canonicalForwardConeDirection * I`, with `ε > 0`, until after the
   Fourier-Laplace/Fubini comparison has been performed. Only then may the
   already-proved boundary-value limit send `ε → 0+`.

This correction aligns the blueprint with the production theorem surface already
present in `OSToWightmanPositivity.lean`:

```lean
bvt_F_canonical_xiShift_shell_sub_horizontal_eq_shell_sub_iterated_fourierLaplaceIntegral
tendsto_bvt_F_canonical_xiShift_shell_sub_iterated_to_timeShift_sub_canonicalExtension
tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero
```

Correction after the shell/horizontal scalar audit and the later fixed-`x`
audit: the following ambient finite-height equality is **withdrawn as an
implementation target**. It is not a raw equality with
`bvtSingleSplitXiShiftScalar`, but it is still too strong: for arbitrary
ambient `φ, ψ`, and also after the attempted transported scalar normal form,
the shell kernel has the real-time oscillatory phase while the horizontal
canonical witness has imaginary-axis Laplace damping. The transported
finite-height residual
`bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport`
is therefore withdrawn as well unless a new explicit analytic-continuation
lemma bridges the displayed exponential mismatch.

Withdrawn ambient statement:

```lean
private theorem
    bvt_F_canonical_xiShift_shell_eq_iterated_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    (∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y) =
    (∫ x : ℝ,
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))) τ) *
      (SchwartzMap.fourierTransformCLM ℂ
        (SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht))) x)
```

Do not implement this theorem as stated. It is useful only as a diagnostic for
the normal-form mismatch. The older plan of keeping the shell and horizontal
terms under a finite-height residual and then proving the scalar `TW`/`ψ_Z`
normal form is also withdrawn. The `Tflat` kernel packets remain diagnostics
for signs and Fubini support; they are not the closing step of the OS route.

The shell-side support and Fubini packets below remain Lean-ready and already
exist in production; they are support/diagnostic infrastructure, not evidence
for either withdrawn finite-height equality.

First, the canonical shell is genuinely in the forward tube for every real
configuration, precisely because the imaginary part is the fixed positive
canonical direction and the `ξ`-shift parameter `t : ℂ` is real:

```lean
private theorem canonicalXiShift_mem_forwardTube
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (y : NPointDomain d (n + m)) :
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
            Complex.I)
      (t : ℂ) ∈ TubeDomainSetPi (ForwardConeAbs d (n + m))
```

Proof transcript:

1. Unfold `TubeDomainSetPi`.
2. Prove the imaginary part is exactly
   `ε • canonicalForwardConeDirection (d := d) (n + m)`.
   The `xiShift` adds the real scalar `(t : ℂ)`, so it contributes no imaginary
   part.
3. Convert `canonicalForwardConeDirection_mem (d := d) (n + m)` to membership
   in `ForwardConeAbs d (n + m)` using
   `inForwardCone_iff_mem_forwardConeAbs`.
4. Apply `forwardConeAbs_smul d (n + m) ε hε`.

The shell-side Fubini package also needs the flattened tube bridge already used
locally in `VladimirovTillmann.lean`. Promote it as reusable support before the
Fubini theorem:

```lean
theorem flattenCLEquiv_mem_tubeDomain_image
    {n r : ℕ} {C : Set (Fin n → Fin (r + 1) → ℝ)}
    {z : Fin n → Fin (r + 1) → ℂ}
    (hz : z ∈ TubeDomainSetPi C) :
    flattenCLEquiv n (r + 1) z ∈
      SCV.TubeDomain ((flattenCLEquivReal n (r + 1)) '' C)

theorem flattenCLEquiv_symm_mem_tubeDomainSetPi_of_mem_tubeDomain_image
    {n r : ℕ} {C : Set (Fin n → Fin (r + 1) → ℝ)}
    {w : Fin (n * (r + 1)) → ℂ}
    (hw : w ∈ SCV.TubeDomain ((flattenCLEquivReal n (r + 1)) '' C)) :
    (flattenCLEquiv n (r + 1)).symm w ∈ TubeDomainSetPi C
```

Both proofs are one-line imaginary-part transport after
`flattenCLEquiv_im`, `flattenCLEquiv_apply`, and
`flattenCLEquivReal_apply`. They are not route wrappers: they expose the exact
SCV/Pi-domain bridge needed to use the flattened Fourier-Laplace theorem on the
canonical shell.

Second, package the shell side as a `Tflat` pairing at fixed `ε > 0`:

```lean
private theorem
    exists_shellKernel_pairing_canonicalXiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hFL :
      ∀ z : Fin (n + m) → Fin (d + 1) → ℂ,
        z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          bvt_F OS lgc (n + m) z =
            fourierLaplaceExtMultiDim
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              Tflat (flattenCLEquiv (n + m) (d + 1) z)) :
    ∃ KShell : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) =
        Tflat KShell
```

Proof transcript:

1. First apply `canonicalShellPsiZExtFamily_pairing` with
   `fFlat := flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)`.
   This gives `KShell` and the flat identity

```lean
∫ yflat, Tflat (multiDimPsiZExt Cflat ... (zShellFlat yflat)) *
  flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat
= Tflat KShell
```

2. Use `integral_flatten_change_of_variables (n + m) (d + 1)` for the flat
   integrand

```lean
fun yflat =>
  Tflat (multiDimPsiZExt Cflat ... (zShellFlat yflat)) *
    flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat
```

   so the flat integral is the same as the integral over
   `NPointDomain d (n+m)` after substituting
   `yflat = flattenCLEquivReal (n + m) (d + 1) y`.

3. In that substituted integrand, simplify
   `(flattenCLEquivReal ...).symm (flattenCLEquivReal ... y)` to `y` and use
   `flattenSchwartzNPoint_apply` to turn the flat test factor into
   `(φ.conjTensorProduct ψ) y`.

4. Use `canonicalXiShift_mem_forwardTube` to rewrite each shell value by `hFL`.
5. Rewrite `fourierLaplaceExtMultiDim` to
   `Tflat (multiDimPsiZExt ...)` using
   `fourierLaplaceExtMultiDim_eq_ext`. Do **not** use
   `fourierLaplaceExtMultiDim_eq_dynamic` here: the existing public continuity
   API is for the fixed-radius `multiDimPsiZ` / `multiDimPsiZExt` family, and
   the boundary-value proof already contains the exact fixed-radius Fubini
   pattern needed here.
6. Apply `schwartz_clm_fubini_exchange` only through the already-checked
   `canonicalShellPsiZExtFamily_pairing` to the family
   `yflat ↦ multiDimPsiZExt Cflat ... (zShellFlat yflat)`, where

```lean
let zShell (yflat : Fin ((n + m) * (d + 1)) → ℝ) :
    Fin (n + m) → Fin (d + 1) → ℂ :=
  xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
    (fun k μ =>
      (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
          Complex.I)
    (t : ℂ)

let zShellFlat (yflat : Fin ((n + m) * (d + 1)) → ℝ) :
    Fin ((n + m) * (d + 1)) → ℂ :=
  flattenCLEquiv (n + m) (d + 1) (zShell yflat)
```

   The continuity proof copies the `hFubini` continuity block in
   `fourierLaplaceExtMultiDim_boundaryValue`: define
   `ι yflat : SCV.TubeDomain Cflat` by pairing `zShellFlat yflat` with tube
   membership from `canonicalXiShift_mem_forwardTube` and
   `flattenCLEquiv_mem_tubeDomain_image`; then write the family as
   a direct application of the public helper
   `continuous_multiDimPsiZExt_comp_of_mem_tube`.
4. The seminorm-growth proof also copies the fixed-radius growth block in
   `fourierLaplaceExtMultiDim_boundaryValue`, not the dynamic-radius theorem.
   This should not be copied directly into Positivity, because the existing
   proof uses private Paley-Wiener internals such as `multiDimPsiExpCLM`.
   Instead, first promote the reusable analytic estimate inside
   `PaleyWienerSchwartz.lean`:

```lean
theorem multiDimPsiZExt_fixedImaginary_seminorm_bound
    {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    {η : Fin m → ℝ} (hη : η ∈ C)
    (k n : ℕ) :
    ∃ (B : ℝ) (N : ℕ), 0 < B ∧
      ∀ x : Fin m → ℝ,
        SchwartzMap.seminorm ℝ k n
          (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
            (fun i => (x i : ℂ) + (η i : ℂ) * Complex.I)) ≤
          B * (1 + ‖x‖) ^ N
```

   Proof transcript for this public helper:

   1. Set `χ := fixedConeCutoff_exists ...`, `y₀ := η`, and obtain
      `c₀ > 0` from `dualConeFlat_coercivity hC_open hC_cone hη`.
   2. For `z x i := (x i : ℂ) + (η i : ℂ) * Complex.I`, show
      `z x ∈ SCV.TubeDomain C` and
      `(fun i => (z x i).im) = η`.
   3. Use `cexp_bound_on_support` with the fixed coercivity `c₀`, support
      radius `1`, and
      `A₀ := c₀ + ((Fintype.card (Fin m) : ℝ)^2) * ‖η‖`.
   4. Apply `schwartz_seminorm_cutoff_exp_bound_affine_uniform` to obtain the
      pointwise derivative bound for the fixed-radius raw kernel.
   5. Convert the pointwise bound to a Schwartz seminorm by
      `SchwartzMap.seminorm_le_bound` and `multiDimPsiZExt_eq`.
   6. Bound
      `‖multiDimPsiExpCLM (z x)‖ ≤ mR * (‖x‖ + ‖η‖)` by
      `multiDimPsiExpCLM_norm_le` plus the componentwise estimate
      `‖z x‖ ≤ ‖x‖ + ‖η‖`.
   7. Absorb the affine term into a polynomial:
      with `Cpoly := 1 + mR * ‖η‖ + mR`,
      `(1 + ‖multiDimPsiExpCLM (z x)‖)^n
        ≤ Cpoly^n * (1 + ‖x‖)^n`.

   Then specialize this helper in Positivity. The shell imaginary part is the
   fixed vector

```lean
ηShell :=
  flattenCLEquivReal (n + m) (d + 1)
    (ε • canonicalForwardConeDirection (d := d) (n + m))
```

   and `ηShell ∈ Cflat` follows from
   `forwardConeAbs_smul` plus the flattening image. The shell real part is

```lean
xShell yflat i := (zShellFlat yflat i).re
```

   and `zShellFlat yflat` is definitionally equal, coordinatewise by real and
   imaginary parts, to
   `fun i => (xShell yflat i : ℂ) + (ηShell i : ℂ) * Complex.I`.
   The only Positivity-specific estimate needed for the Fubini side condition
   is the affine norm bound

```lean
∃ A > 0, ∀ yflat,
  ‖xShell yflat‖ ≤ A * (1 + ‖yflat‖)
```

   A concrete choice is
   `A := 1 + |t|`: each coordinate of the real part is either the corresponding
   flattened real coordinate or that coordinate plus `t` in the shifted
   time-component region, so
   `|xShell yflat i| ≤ ‖yflat‖ + |t| ≤ (1 + |t|) * (1 + ‖yflat‖)`.
   After applying the public helper to `xShell yflat`, absorb
   `(1 + ‖xShell yflat‖)^N` into a constant multiple of
   `(1 + ‖yflat‖)^N`.
7. Conclude by transitivity with the flat identity from Step 1.

Implementation helpers to write before the shell package, all copied from the
existing `fourierLaplaceExtMultiDim_boundaryValue` proof skeleton:

```lean
theorem continuous_multiDimPsiZExt_comp_of_mem_tube ...        -- implemented
private theorem continuous_canonicalShellPsiZExtFamily ...     -- implemented
private theorem seminorm_canonicalShellPsiZExtFamily_bound ...
private theorem canonicalShellPsiZExtFamily_pairing ...
```

The public continuity helper is already the reusable form of the
`multiDimPsiZExt` continuity block. The two shell-specific helpers discharge
the `schwartz_clm_fubini_exchange` side conditions.

The next implementation should first prove the flat Fubini packet, because it
is the direct consumer of those two side conditions and does not yet need the
boundary-value representation hypothesis:

```lean
private theorem canonicalShellPsiZExtFamily_pairing
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open : IsOpen Cflat)
    (hCflat_conv : Convex ℝ Cflat)
    (hCflat_cone : IsCone Cflat)
    (hCflat_salient : IsSalientCone Cflat)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (fFlat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ) :
    ∃ KShell : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
        Tflat (multiDimPsiZExt Cflat ... (zShellFlat yflat)) *
          fFlat yflat) =
        Tflat KShell
```

Proof transcript:

1. Define
   `gFamily yflat := multiDimPsiZExt Cflat ... (zShellFlat yflat)`.
2. Use `continuous_canonicalShellPsiZExtFamily` for the `hg_cont` hypothesis.
3. Use `seminorm_canonicalShellPsiZExtFamily_bound` for the `hg_bound`
   hypothesis.
4. Apply
   `schwartz_clm_fubini_exchange Tflat gFamily fFlat hg_cont hg_bound`.
5. Return the produced `KShell`; the axiom gives
   `Tflat KShell = ∫ yflat, Tflat (gFamily yflat) * fFlat yflat`, so the
   desired displayed equality is its symmetric form.

Only after this flat packet is checked should the route prove
`exists_shellKernel_pairing_canonicalXiShift`, which adds:

1. `hFL` to rewrite
   `bvt_F OS lgc ... shellZ = Tflat (multiDimPsiZExt Cflat ... zShellFlat)`;
2. `integral_flatten_change_of_variables` plus the
   `flattenSchwartzNPoint_apply` normal form for the change from
   `NPointDomain d (n+m)` to flat coordinates;
3. `fFlat := flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)`.

These helpers are genuine analytic/Fubini content and are permitted; a
one-line wrapper around `hFL` alone is not.

Third, package the horizontal/iterated Fourier-Laplace side as a `Tflat`
pairing using the same `Tflat`:

```lean
private theorem
    exists_horizontalKernel_pairing_iteratedFourierLaplace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∃ KHorizontal : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∫ x : ℝ,
        (∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
              (by
                have hscaled : 0 < (2 * Real.pi) *
                    (((x : ℂ) + ε * Complex.I).im) :=
                  mul_pos Real.two_pi_pos (by simpa using hε)
                simpa [Complex.mul_im] using hscaled))) τ) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) x) =
        Tflat KHorizontal
```

Implementation-readiness refinement.

Do not attempt the displayed double integral as the first Lean theorem. The
safe implementation route factors it through an arbitrary one-variable
time-shift test. This is the missing reusable rung between the shell-side
`KShell` theorem and the full horizontal kernel:

```lean
theorem exists_timeShiftKernel_pairing_fourierTest
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (χ : SchwartzMap ℝ ℂ)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∃ Kχ : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∀ ξ : (Fin ((n + m) * (d + 1)) → ℝ),
        Kχ ξ =
          (∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ * χ τ)) ∧
      ((∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          χ τ) =
        Tflat Kχ)
```

This theorem is implemented in `OSToWightmanBoundaryValueLimits.lean`, not in the
positivity frontier, because its proof is exactly the existing flat
translation/Fubini proof pattern with the negative-support vanishing step
removed. Its statement mentions no private BVLimits constants; the proof may
reuse the private local flattening algebra already in that file.

Proof transcript for `exists_timeShiftKernel_pairing_fourierTest`:

1. Set `M := (n + m) * (d + 1)`. Since `0 < d` is in scope, `0 < M` follows
   from `hm : 0 < m`. Define
   `k := M - 1`, `hk : k + 1 = M`, `β := normedUnitBumpSchwartzPi k`,
   `fpad0 := χ.prependField β`, and
   `fpad := OSReconstruction.reindexSchwartzFin hk fpad0`.
2. Define the public orbit abbreviation

```lean
timeShiftFlatOrbit (d := d) φ ψ τ
```

   for the full expression
   `physicsFourierFlatCLM (reindexSchwartzFin ...
     (SCV.translateSchwartz (zeroHeadBlockShift (τ • flatTimeShiftDirection d m))
       Ψ))`. This keeps the theorem statement parse-stable and gives the
   downstream EqOn proof a canonical name for the horizontal orbit. Here
   `Ψ := (flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
     (flattenSchwartzNPoint (d := d) ψ)`,
   `orbit τ := timeShiftFlatOrbit (d := d) φ ψ τ`,
   `headCoord x := ((OSReconstruction.castFinCLE hk).symm x) 0`, and
   `gFamily x := orbit (headCoord x)`.
3. Prove `Continuous gFamily` using
   `continuous_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
   composed with `headCoord`.
4. Prove the polynomial seminorm bound for `gFamily` from
   `exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
   and `|headCoord x| ≤ ‖x‖`, exactly as in
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`.
5. Apply `schwartz_clm_fubini_exchange Tflat gFamily fpad` and call the
   produced kernel `Kχ`.
6. Rewrite its pointwise formula from the full flat integral to the displayed
   one-variable integral using `integral_comp_castFinCLE_eq`,
   `integral_finSucc_cons_eq`, `MeasureTheory.integral_prod_mul`, and
   `integral_normedUnitBumpSchwartzPi`.
7. Rewrite the scalar pairing field by `hTflat_bv`, the local
   `timeShiftSchwartzNPoint`/flattening translation identity, and the same
   padded-integral calculation. The final result is the displayed equality
   `(∫ τ, bvt_W ... * χ τ) = Tflat Kχ`.

After this theorem is available, the horizontal packet is no longer a raw
double-Fubini problem. It should be assembled in two explicit steps:

1. Build a one-dimensional horizontal Paley kernel `χHorizontal ε t` by applying
   `schwartz_clm_fubini_exchange` on `Fin 1` to the family
   `x ↦ (SchwartzMap.fourierTransformCLM ℂ) (ψZ_{2π(x+εi)})`, using the already
   documented side conditions
   `continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal` and
   `seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth`.
   Its pointwise formula is
   `χHorizontal τ = ∫ x, (𝓕 ψZ_{2π(x+εi)}) τ * (𝓕 ψZ_{2πit}) x`.
2. Apply `exists_timeShiftKernel_pairing_fourierTest` with
   `χ := χHorizontal`. The resulting `Kχ` is the desired
   `KHorizontal`, and its pointwise formula is suitable for the later
   dual-cone EqOn calculation against `KShell`.

The older direct double-Fubini proof transcript is superseded by the
two-stage transcript above. In particular, do not build `KHorizontal` by first
choosing a family of existential inner kernels depending on `x`; that loses the
continuity/growth data needed for the outer Fubini step. The safe Lean order is:
first prove the arbitrary-test flat time-shift theorem, then build the
one-dimensional `χHorizontal`, then apply the arbitrary-test theorem with
`χ := χHorizontal`.

Implementation-ready statement for the one-dimensional horizontal Paley kernel:

```lean
private theorem exists_horizontalPaleyKernel_pairing_fourierTransform
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                ...)) τ *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                (((2 * Real.pi : ℂ) * (t * Complex.I)))
                ...)) x) ∧
      TW χHorizontal =
        ∫ x : ℝ,
          TW
            ((SchwartzMap.fourierTransformCLM ℂ)
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                ...)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              ...)) x
```

Lean proof transcript:

1. Set

```lean
let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
let fromFin1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1.symm
let T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ := TW.comp fromFin1
let ψZt : SchwartzMap ℝ ℂ :=
  SCV.schwartzPsiZ (((2 * Real.pi : ℂ) * (t * Complex.I))) ...
let f1 : SchwartzMap (Fin 1 → ℝ) ℂ :=
  toFin1 ((SchwartzMap.fourierTransformCLM ℂ) ψZt)
let g1 : (Fin 1 → ℝ) → SchwartzMap (Fin 1 → ℝ) ℂ := fun x1 =>
  toFin1
    ((SchwartzMap.fourierTransformCLM ℂ)
      (SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
        ...))
```

2. Apply `schwartz_clm_fubini_exchange T1 g1 f1` with
   `SCV.continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal hε`
   and
   `SCV.seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth hε`.
   Let the produced `Fin 1` kernel be `χ1`.
3. Define `χHorizontal := fromFin1 χ1`.
4. Pointwise formula:
   `χHorizontal τ = χ1 (e1.symm τ)`, then use the Fubini pointwise formula.
   Rewrite
   `toFin1 φ x1 = φ (e1 x1)` and `e1 (e1.symm τ) = τ`.
   Convert the remaining `Fin 1` integral to the real-line integral using
   the measure-preserving equivalence
   `MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ`.
5. Pairing formula:
   `TW χHorizontal = T1 χ1`, use the Fubini pairing equality, rewrite
   `fromFin1 (toFin1 φ) = φ`, and again convert the `Fin 1` integral to the
   real-line integral.
6. Immediately derive the universal form:

```lean
private theorem exists_horizontalPaleyKernel_universal_pairing
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := ...
    let ψZt : SchwartzMap ℝ ℂ := ...
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      ∀ TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ,
        TW χHorizontal =
          ∫ x : ℝ,
            TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

   Proof: choose `χHorizontal` from
   `exists_horizontalPaleyKernel_pairing_fourierTransform hε ht 0`. For an
   arbitrary `TW`, apply
   `exists_horizontalPaleyKernel_pairing_fourierTransform hε ht TW`, obtaining
   `χTW`. Prove `χTW = χHorizontal` by `ext τ` from the identical pointwise
   formula. Transport the `TW` pairing identity across this equality.

   This universal theorem is essential for the dual-cone EqOn proof: at fixed
   flattened frequency `ξ`, instantiate `TW` as the one-variable continuous
   functional

```lean
χ ↦ ∫ τ, timeShiftFlatOrbit (d := d) φ ψ τ ξ * χ τ
```

   after rewriting `timeShiftFlatOrbit` to its oscillatory phase form. This
   avoids a raw ad hoc scalar Fubini step in the EqOn proof.

7. Keep these theorems in `OSToWightmanPositivity.lean` near the existing
   horizontal canonical-witness normal forms. It is generic in `TW`, so it is
   not a wrapper over the Wightman theorem; the immediate next consumer
   instantiates
   `TW := bvt_W_conjTensorProduct_timeShiftTemperedFunctional ...`.

Implementation-ready statement for the immediate Wightman/full-flat consumer:

```lean
private theorem exists_horizontalKernel_pairing_iteratedFourierLaplace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := ...
    let ψZt : SchwartzMap ℝ ℂ := ...
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      ∃ KHorizontal : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        (∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
          KHorizontal ξ =
            ∫ τ : ℝ,
              timeShiftFlatOrbit (d := d) φ ψ τ ξ * χHorizontal τ) ∧
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
          Tflat KHorizontal
```

Proof transcript:

1. Let
   `TW := bvt_W_conjTensorProduct_timeShiftTemperedFunctional
     (d := d) OS lgc φ ψ hψ_compact`.
2. Apply
   `exists_horizontalPaleyKernel_pairing_fourierTransform hε ht TW`,
   obtaining `χHorizontal`, its pointwise formula, and
   `TW χHorizontal = ∫ x, TW (𝓕 ψZxε x) * (𝓕 ψZt) x`.
3. Apply `exists_timeShiftKernel_pairing_fourierTest` to this
   `χHorizontal`, `Tflat`, and `hTflat_bv`, obtaining `KHorizontal`,
   its pointwise formula, and
   `∫ τ, bvt_W(φ ⊗ timeShift τ ψ) * χHorizontal τ = Tflat KHorizontal`.
4. Prove the horizontal scalar equality by the chain

```lean
∫ x, H(x + ε i) * (𝓕 ψZt) x
  = ∫ x, TW (𝓕 ψZxε x) * (𝓕 ψZt) x
  = TW χHorizontal
  = ∫ τ, bvt_W(φ ⊗ timeShift τ ψ) * χHorizontal τ
  = Tflat KHorizontal
```

The first equality is pointwise integral congruence using
`bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral`
together with
`bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
The third equality is exactly
`bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` applied to
`χHorizontal`.

Withdrawn fourth step: the finite-height full-kernel equality below is not a
valid arbitrary-`φ,ψ` target. It is retained only to document the exact theorem
shape that must **not** be implemented without additional transported
Section-4.3 hypotheses:

```lean
private theorem
    canonicalShell_horizontal_kernel_eqOn_dualCone
    ...
    Set.EqOn
      (KShell : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ)
      KHorizontal
      (DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
```

The reason is explicit after the horizontal scalar calculation. On the dual
cone the horizontal packet gives Laplace damping in `t`, while the canonical
shell has a real `xiShift ... (t : ℂ)` and therefore an oscillatory phase.
This mismatch is not a Lean inconvenience; it is the mathematical obstruction
that prevents an unconditional shell-to-canonical-imaginary-axis theorem.

The following support lemma remains sound and useful for shell normal-form
diagnostics, and it is already implemented in `SCV/PaleyWienerSchwartz.lean`.
It should not be followed by the withdrawn raw EqOn theorem.

Implementation-ready support lemma:

```lean
theorem multiDimPsiZExt_apply_of_mem_dualCone {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C)
    {ξ : Fin m → ℝ} (hξ : ξ ∈ DualConeFlat C) :
    multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z ξ =
      Complex.exp (Complex.I * ∑ i, z i * (ξ i : ℂ))
```

Lean proof transcript:

```lean
  rw [multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient z hz]
  let χ : FixedConeCutoff (DualConeFlat C) :=
    (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  change psiZRaw χ 1 z ξ =
    Complex.exp (Complex.I * ∑ i, z i * (ξ i : ℂ))
  have hχ : χ.val ξ = 1 := fixedConeCutoff_eq_one_on_dualCone χ hξ
  simp [psiZRaw, hχ]
```

Expected local adjustment: if `simp [psiZRaw, hχ]` does not rewrite the cutoff
argument because it appears as `fun i => 1⁻¹ * ξ i`, add

```lean
  have hscale : (fun i => (1 : ℝ)⁻¹ * ξ i) = ξ := by
    ext i
    simp
  simp [psiZRaw, hscale, hχ]
```

This theorem is mathematically sound because `multiDimPsiZExt` first reduces to
the fixed-radius `multiDimPsiZ` on the tube; `multiDimPsiZ` is
`psiZRaw χ 1 z`; and `χ = 1` on `DualConeFlat C` by
`FixedConeCutoff.one_on_neighborhood` plus `Metric.infDist_zero_of_mem`.

After this support lemma, the EqOn theorem should be implemented with the
following local notation:

```lean
let q : ℕ := n + m
let M : ℕ := q * (d + 1)
let Cflat : Set (Fin M → ℝ) :=
  (flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q
let Ψ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ :=
  (flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
    (flattenSchwartzNPoint (d := d) ψ)
let Ψfull : SchwartzMap (Fin M → ℝ) ℂ :=
  OSReconstruction.reindexSchwartzFin
    (by ring : n * (d + 1) + m * (d + 1) = M) Ψ
let vTail : Fin M → ℝ :=
  (OSReconstruction.castFinCLE
    (by ring : n * (d + 1) + m * (d + 1) = M))
    (OSReconstruction.zeroHeadBlockShift
      (m := n * (d + 1)) (n := m * (d + 1))
      (flatTimeShiftDirection d m))
let lam ξ : ℝ := ∑ i, vTail i * ξ i
let r ξ : ℝ := - lam ξ / (2 * Real.pi)
let base ξ : ℂ := physicsFourierFlatCLM Ψfull ξ
```

For `ξ ∈ DualConeFlat Cflat`, the public BVLimits sign lemma gives
`lam ξ ≤ 0`, hence `0 ≤ r ξ`. The exact one-variable Fourier normalization is:

```lean
∫ τ : ℝ,
  Complex.exp (-(Complex.I * (lam ξ : ℂ) * τ)) *
    (SchwartzMap.fourierTransformCLM ℂ χ) τ
= χ (r ξ)
```

This is exactly `integral_phase_mul_fourierTransform_eq_eval χ (lam ξ)`.

The fixed-frequency phase functional used with
`exists_horizontalPaleyKernel_universal_pairing` is:

```lean
TWξ χ :=
  base ξ *
    ∫ τ : ℝ,
      Complex.exp (-(Complex.I * (lam ξ : ℂ) * τ)) * χ τ
```

or equivalently the integral of
`Complex.exp (-(I * lam ξ * τ)) * base ξ * χ τ`; choose the former in Lean
because it is the scalar multiple of the existing one-variable
`SchwartzMap.integralCLM` applied after `SchwartzMap.smulLeftCLM` by the
temperate-growth phase. Its evaluation on Fourier transforms is:

```lean
TWξ (SchwartzMap.fourierTransformCLM ℂ χ)
  = base ξ * χ (r ξ)
```

by pulling out `base ξ` and applying
`integral_phase_mul_fourierTransform_eq_eval`.

Implementation-ready support lemma for the full-flat time-shift orbit, to be
placed in `OSToWightmanBoundaryValueLimits.lean` immediately after
`timeShiftFlatOrbit`:

```lean
theorem timeShiftFlatOrbit_apply_phase
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (τ : ℝ) (ξ : Fin ((n + m) * (d + 1)) → ℝ) :
    timeShiftFlatOrbit (d := d) φ ψ τ ξ =
      Complex.exp
        (-(Complex.I *
          (((∑ i,
            (((OSReconstruction.castFinCLE
              (Nat.add_mul n m (d + 1)).symm)
              (OSReconstruction.zeroHeadBlockShift
                (m := n * (d + 1)) (n := m * (d + 1))
                (flatTimeShiftDirection d m))) i) * ξ i : ℝ) : ℂ) *
            (τ : ℂ)))) *
        physicsFourierFlatCLM
          (OSReconstruction.reindexSchwartzFin
            (Nat.add_mul n m (d + 1)).symm
            ((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
              (flattenSchwartzNPoint (d := d) ψ))) ξ
```

Lean proof transcript:

```lean
  classical
  let Ψ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ :=
    (flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
      (flattenSchwartzNPoint (d := d) ψ)
  dsimp [timeShiftFlatOrbit]
  rw [physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift_apply
    (d := d) (n := n) (m := m)
    (a := τ • flatTimeShiftDirection d m) (Ψ := Ψ) (ξ := ξ)]
  congr 1
  have hsum_real :
      (∑ i,
          ((OSReconstruction.castFinCLE
            (Nat.add_mul n m (d + 1)).symm)
            (OSReconstruction.zeroHeadBlockShift
              (m := n * (d + 1)) (n := m * (d + 1))
              (τ • flatTimeShiftDirection d m))) i * ξ i) =
        (∑ i,
          ((OSReconstruction.castFinCLE
            (Nat.add_mul n m (d + 1)).symm)
            (OSReconstruction.zeroHeadBlockShift
              (m := n * (d + 1)) (n := m * (d + 1))
              (flatTimeShiftDirection d m))) i * ξ i) * τ := by
    simp [zeroHeadBlockShift_smul, Finset.mul_sum, Pi.smul_apply,
      mul_assoc, mul_left_comm, mul_comm]
  have hsum :
      (∑ i,
          ((((OSReconstruction.castFinCLE
            (Nat.add_mul n m (d + 1)).symm)
            (OSReconstruction.zeroHeadBlockShift
              (m := n * (d + 1)) (n := m * (d + 1))
              (τ • flatTimeShiftDirection d m))) i : ℝ) : ℂ) *
            (ξ i : ℂ)) =
        ((∑ i,
            (((OSReconstruction.castFinCLE
              (Nat.add_mul n m (d + 1)).symm)
              (OSReconstruction.zeroHeadBlockShift
                (m := n * (d + 1)) (n := m * (d + 1))
                (flatTimeShiftDirection d m))) i) * ξ i : ℝ) : ℂ) * τ := by
    exact_mod_cast hsum_real
  congr 1
  rw [hsum]
```

This theorem is a genuine exposure of existing Fourier algebra, not a wrapper:
it removes the repeated unfold/rewrite burden from the future EqOn proof and
fixes the sign of the phase once, using the already verified translation lemma.

Implementation-ready one-variable phase functional packet, to be placed in
`OSToWightmanPositivity.lean` near the horizontal Paley kernel theorem:

```lean
private theorem horizontalPhase_temperate (lam : ℝ) :
    (fun τ : ℝ =>
      Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ)))).HasTemperateGrowth := by
  let c : ℂ := -(Complex.I * (lam : ℂ))
  suffices htemp : (fun τ : ℝ => Complex.exp (c * (τ : ℂ))).HasTemperateGrowth by
    convert htemp using 1
    ext τ
    simp [c, mul_assoc]
  refine ⟨?_, ?_⟩
  · have hlin : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun τ : ℝ => c * (τ : ℂ)) := by
      simpa using (contDiff_const.mul Complex.ofRealCLM.contDiff)
    exact Complex.contDiff_exp.comp hlin
  · intro n
    refine ⟨0, ‖c ^ n‖, fun τ => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter := congr_fun (SCV.iteratedDeriv_cexp_const_mul_real n c) τ
    rw [hiter]
    have hre : (c * (τ : ℂ)).re = 0 := by
      simp [c, Complex.mul_re]
    calc
      ‖c ^ n * Complex.exp (c * (τ : ℂ))‖ = ‖c ^ n‖ := by
        rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
      _ ≤ ‖c ^ n‖ * (1 + ‖τ‖) ^ 0 := by simp

private noncomputable def horizontalPhasePairingCLM
    (base : ℂ) (lam : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  base •
    ((SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).comp
      (SchwartzMap.smulLeftCLM ℂ
        (fun τ : ℝ =>
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))))))

private theorem horizontalPhasePairingCLM_apply
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    horizontalPhasePairingCLM base lam χ =
      base *
        ∫ τ : ℝ,
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) * χ τ := by
  simp [horizontalPhasePairingCLM, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (horizontalPhase_temperate lam), smul_eq_mul]

private theorem horizontalPhasePairingCLM_fourierTransform
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    horizontalPhasePairingCLM base lam
        ((SchwartzMap.fourierTransformCLM ℂ) χ) =
      base * χ (-lam / (2 * Real.pi)) := by
  rw [horizontalPhasePairingCLM_apply]
  rw [integral_phase_mul_fourierTransform_eq_eval]
```

This packet is the precise way to instantiate
`exists_horizontalPaleyKernel_universal_pairing` at a fixed frequency `ξ`.
The next implementation-ready theorem is the direct instantiation:

```lean
private theorem exists_horizontalPaleyKernel_phasePairing
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      horizontalPhasePairingCLM base lam χHorizontal =
        ∫ x : ℝ,
          (base * (ψZxε x) (-lam / (2 * Real.pi))) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  obtain ⟨χHorizontal, hχ_eval, hχ_pair⟩ :=
    exists_horizontalPaleyKernel_universal_pairing (hε := hε) (ht := ht)
  refine ⟨χHorizontal, ?_, ?_⟩
  · simpa [ψZxε, ψZt] using hχ_eval
  · calc
      horizontalPhasePairingCLM base lam χHorizontal
          = ∫ x : ℝ,
              horizontalPhasePairingCLM base lam
                ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              simpa [ψZxε, ψZt] using
                hχ_pair (horizontalPhasePairingCLM base lam)
      _ = ∫ x : ℝ,
            (base * (ψZxε x) (-lam / (2 * Real.pi))) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [horizontalPhasePairingCLM_fourierTransform]
```

This theorem is not the final shell comparison. Its role is to turn the
horizontal `τ`-kernel into the one remaining `x`-integral at a frozen
frequency. The subsequent theorem uses it with

```lean
base := physicsFourierFlatCLM Ψfull ξ
lam := ∑ i, vTail i * ξ i
```

and use `timeShiftFlatOrbit_apply_phase` to rewrite
`timeShiftFlatOrbit τ ξ` as the integrand represented by
`horizontalPhasePairingCLM base lam`.

The next horizontal-only collapse is implementation-ready:

```lean
private theorem horizontalPaley_phase_xIntegral_eq
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∫ x : ℝ,
      (base * (ψZxε x) (-lam / (2 * Real.pi))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    base *
      ((SCV.smoothCutoff (-lam / (2 * Real.pi)) : ℂ) *
        Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
        ψZt (-lam / (2 * Real.pi))) := by
  classical
  let r : ℝ := -lam / (2 * Real.pi)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hψ_inv :
      FourierTransform.fourierInv
          ((SchwartzMap.fourierTransformCLM ℂ) ψZt) = ψZt := by
    simpa [ψZt] using (FourierTransform.fourierInv_fourier_eq ψZt)
  have hpair :
      (∫ x : ℝ,
          (ψZxε x) r *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
        (SCV.smoothCutoff r : ℂ) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
          ψZt r := by
    calc
      (∫ x : ℝ,
          (ψZxε x) r *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = ∫ x : ℝ,
              SCV.psiZ ((2 * Real.pi : ℂ) * (x + ε * Complex.I)) r *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [ψZxε]
      _ = (SCV.smoothCutoff r : ℂ) *
            Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
            FourierTransform.fourierInv
              ((SchwartzMap.fourierTransformCLM ℂ) ψZt) r :=
            SCV.psiZ_twoPi_pairing_formula
              (φ := (SchwartzMap.fourierTransformCLM ℂ ψZt))
              (η := ε) (ξ := r)
      _ = (SCV.smoothCutoff r : ℂ) *
            Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
            ψZt r := by rw [hψ_inv]
  have hmain :
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
      base *
        ((SCV.smoothCutoff r : ℂ) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
          ψZt r) := by
    calc
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = ∫ x : ℝ,
              base * ((ψZxε x) r *
                (SchwartzMap.fourierTransformCLM ℂ ψZt) x) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
      _ = base *
            ∫ x : ℝ,
              (ψZxε x) r *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            simpa using
              (MeasureTheory.integral_const_mul
                (μ := MeasureTheory.volume) base
                (fun x : ℝ =>
                  (ψZxε x) r *
                  (SchwartzMap.fourierTransformCLM ℂ ψZt) x))
      _ = base *
            ((SCV.smoothCutoff r : ℂ) *
              Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
              ψZt r) := by rw [hpair]
  simpa [r, ψZxε, ψZt] using hmain
```

The remaining horizontal simplification, after this theorem, is purely
pointwise:

1. For `ξ ∈ DualConeFlat Cflat`, the promoted theorem
   `zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone`
   gives `lam ξ ≤ 0`, hence `r ξ = -lam ξ / (2π) ≥ 0`.
2. `SCV.smoothCutoff_one_of_nonneg` removes the outer cutoff at `r ξ`.
3. `SCV.psiZ_eq_exp_of_nonneg` removes the cutoff inside `ψZt (r ξ)`.
4. The exponent algebra is

```lean
Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)
  = -(2 * Real.pi * t : ℂ) * (r : ℂ)
```

so the horizontal scalar becomes

```lean
base *
  Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
  Complex.exp (-(2 * Real.pi * t : ℂ) * r)
```

with `r = -lam / (2 * Real.pi)`.

Implementation-ready cutoff-removal theorem:

```lean
private theorem horizontalPaley_phase_xIntegral_eq_of_nonneg
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ)
    (hr : 0 ≤ -lam / (2 * Real.pi)) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∫ x : ℝ,
      (base * (ψZxε x) (-lam / (2 * Real.pi))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    base *
      (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
       Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
  classical
  let r : ℝ := -lam / (2 * Real.pi)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hr' : 0 ≤ r := by simpa [r] using hr
  have hcut : (SCV.smoothCutoff r : ℂ) = 1 := by
    exact_mod_cast SCV.smoothCutoff_one_of_nonneg hr'
  have hψt :
      ψZt r = Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ)) := by
    calc
      ψZt r
          = SCV.psiZ ((2 * Real.pi : ℂ) * (t * Complex.I)) r := by
              simp [ψZt]
      _ = Complex.exp
            (Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)) := by
            rw [SCV.psiZ_eq_exp_of_nonneg hr']
      _ = Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ)) := by
            congr 1
            calc
              Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)
                  = (Complex.I * Complex.I) *
                      ((2 * Real.pi * t : ℂ) * (r : ℂ)) := by ring
              _ = -(2 * Real.pi * t : ℂ) * (r : ℂ) := by
                    simp [Complex.I_mul_I]
  have hcollapse :=
    horizontalPaley_phase_xIntegral_eq (hε := hε) (ht := ht)
      (base := base) (lam := lam)
  have hmain :
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
      base *
        (Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
         Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ))) := by
    calc
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = base *
              ((SCV.smoothCutoff r : ℂ) *
                Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
                ψZt r) := by
              simpa [r, ψZxε, ψZt] using hcollapse
      _ = base *
            (Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
             Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ))) := by
            rw [hcut, hψt]
            ring
  simpa [r, ψZxε, ψZt] using hmain
```

Implementation-ready dual-cone sign bridge:

```lean
private theorem horizontalPaley_frequency_nonneg_of_mem_dualCone
    {n m : ℕ}
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ : ξ ∈ DualConeFlat
      ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    0 ≤ -(∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i) / (2 * Real.pi) := by
  have hlam :=
    zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (n := n) (m := m) (ξ := ξ) hξ
  have hden_nonneg : 0 ≤ 2 * Real.pi := Real.two_pi_pos.le
  refine div_nonneg ?_ hden_nonneg
  exact neg_nonneg.mpr (by simpa using hlam)
```

Proof transcript:

1. Introduce `ξ hξ` and rewrite both kernels by their Fubini pointwise
   formulas.
2. On the `KHorizontal` side, rewrite `timeShiftFlatOrbit` by
   `physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift_apply` with
   `a := τ • flatTimeShiftDirection d m` and `Ψ := Ψ`. The scalar phase
   simplifies to

```lean
Complex.exp (-(Complex.I * (lam ξ : ℂ) * τ)) * base ξ
```

   using `map_smul`, `Finset.mul_sum`, and commutative-ring normalization.
3. Replace the `τ`-integral against `χHorizontal` by the universal horizontal
   Fubini identity instantiated at `TWξ`. The result is

```lean
∫ x : ℝ,
  base ξ *
    (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) (r ξ) *
    (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

   after `integral_phase_mul_fourierTransform_eq_eval`.
4. Use Fourier inversion to convert the preceding `x`-integral. The planned
   Lean route is to rewrite with
   `psiZ_twoPi_pairing_formula` in the contrapositive orientation already used
   in `PaleyWiener.lean`: the `x`-integral of the horizontal
   `ψ_{2π(x+εi)}` pairing against `𝓕ψ_{2πit}` evaluates to

```lean
smoothCutoff (r ξ) *
  Complex.exp (-(2 * Real.pi * ε : ℂ) * (r ξ)) *
  ψZt (r ξ)
```

   and `0 ≤ r ξ` makes both one-variable smooth cutoffs equal to `1`.
5. Therefore the horizontal kernel becomes

```lean
base ξ *
  Complex.exp (-(2 * Real.pi * ε : ℂ) * (r ξ)) *
  Complex.exp (-(2 * Real.pi * t : ℂ) * (r ξ))
```

   with the `t` factor coming from `ψZt (r ξ)` after cutoff removal. Since
   `r ξ = -lam ξ/(2π)`, the product is

```lean
base ξ * Complex.exp ((ε + t : ℂ) * (lam ξ : ℂ))
```

   up to the precise sign conventions already fixed by
   `integral_phase_mul_fourierTransform_eq_eval` and
   `physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift_apply`.
   This algebra must be confirmed in Lean before the theorem is considered
   closed; the signs are not to be adjusted by wrappers.
6. On the `KShell` side, use
   `multiDimPsiZExt_apply_of_mem_dualCone` with `C := Cflat` and `hξ`. This
   rewrites the shell kernel integrand to the pure exponential

```lean
Complex.exp
  (Complex.I *
    ∑ i,
      (flattenCLEquiv q (d + 1) (zShell yflat) i) *
        (ξ i : ℂ)) *
  flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat
```

   Expanding `zShell` gives

```lean
Complex.exp
  (Complex.I * ∑ i, (yflat i : ℂ) * (ξ i : ℂ)) *
Complex.exp
  (Complex.I * (t : ℂ) * tailTimePair ξ) *
Complex.exp
  (-(ε : ℂ) * ηCanonicalPair ξ)
```

   where

```lean
tailTimePair ξ =
  ∑ k : Fin m, ξ (finProdFinEquiv (Fin.natAdd n k, (0 : Fin (d + 1))))

ηCanonicalPair ξ =
  ∑ k : Fin (n + m), ((k : ℕ) + 1 : ℝ) *
    ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
```

   and the promoted BVLimits sign convention gives
   `lam ξ = -tailTimePair ξ`. Thus the shell scalar is oscillatory in `t`:

```lean
base ξ *
  Complex.exp (-(Complex.I * (t : ℂ) * (lam ξ : ℂ))) *
  Complex.exp (-(ε : ℂ) * ηCanonicalPair ξ)
```

   This is not the horizontal damping scalar from step 5. Consequently the
   raw `KShell = KHorizontal` EqOn must not be implemented.
7. The remaining live bridge must use the OS I positive-support
   time-interchange theorem, not a finite-height shell/horizontal EqOn. The
   Section-4.3 slice comparison replaces representatives; it does not erase
   the external oscillatory/Laplace mismatch at finite height.

The zero-residual theorem below is therefore retained only as the withdrawn
finite-height draft. It must not be implemented unless a new explicit
analytic-continuation lemma first proves that the oscillatory shell factor and
the Laplace-damped horizontal factor represent the same transported scalar.

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)
```

Historical proof transcript for the withdrawn zero-residual theorem:

1. On `nhdsWithin 0 (Set.Ioi 0)`, introduce `hε : 0 < ε`.
2. Rewrite the horizontal term by
   `bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral`.
3. Apply the transported finite-height equality
   `bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport`
   with the same `φ ψ f g hφf hψg ht hε`. This is the only step where
   Section-4.3 transport enters the residual theorem.
4. The rewritten residual is eventually the constant zero function, hence
   tends to `0`.

Lean skeleton:

```lean
  let ψZt : SchwartzMap ℝ ℂ := SCV.schwartzPsiZ ...
  have hEventually :=
    bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht
  have hZero :
      (fun ε : ℝ =>
        if hε : 0 < ε then
          (∫ y : NPointDomain d (n + m), ... shell ... ) -
          (∫ x : ℝ, ... iterated ... )
        else 0)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hεpos
    rw [dif_pos hεpos]
    simpa [ψZt] using
      bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact)
        (f := f) (g := g) (hf_compact := hf_compact)
        (hg_compact := hg_compact) hφf hψg ht hεpos
  exact (Filter.tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℂ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)).congr' (hEventually.trans hZero)
```

If Lean rejects the final `congr'`, rewrite the two eventual equalities into a
single eventual equality from the original residual to `fun _ => 0`:

```lean
  have hOriginalZero :
      originalResidual =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => 0 :=
    hEventually.trans hZero
  exact Filter.Tendsto.congr' hOriginalZero tendsto_const_nhds
```

No theorem without `hφf` and `hψg` may be used to prove this zero residual.
If such a goal appears, it has revived the false arbitrary shell-horizontal
EqOn route. More importantly, no proof of this theorem should be attempted at
all on the current route without the missing analytic-continuation lemma.

If such a theorem is ever revived, the already-existing reducer
`tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero`
supplies the `hlimit` hypothesis of
`lemma42_matrix_element_time_interchange` with
`H := bvt_W_conjTensorProduct_timeShiftCanonicalExtension ...`.

The following raw packet is retained only as the superseded draft that motivated
the correction above. It must not be used as an implementation target unless a
new proof first replaces the false raw tube-support theorem with a valid
permuted/translated tube representative and tracks the resulting Fourier
factors.

Retired raw packet draft:

Let

```lean
let q : ℕ := n + m
let M : ℕ := q * (d + 1)
let C : Set (Fin q → Fin (d + 1) → ℝ) := ForwardConeAbs d q
let Cflat : Set (Fin M → ℝ) := (flattenCLEquivReal q (d + 1)) '' C
let yOfFlat : (Fin M → ℝ) → NPointDomain d q :=
  fun yflat => (flattenCLEquivReal q (d + 1)).symm yflat
let zSplit : (Fin M → ℝ) → Fin q → Fin (d + 1) → ℂ :=
  fun yflat =>
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun i => wickRotatePoint (yOfFlat yflat i))
      ((t : ℂ) * Complex.I)
let zSplitFlat : (Fin M → ℝ) → Fin M → ℂ :=
  fun yflat => flattenCLEquiv q (d + 1) (zSplit yflat)
let fTransport : SchwartzMap (Fin M → ℝ) ℂ :=
  flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1)
```

The exact support theorem needed to justify the FL rewrite under the
single-split integral is:

```lean
private theorem zSplit_mem_forwardTube_of_osConjTensorProduct_support
    {n m : ℕ} (hm : 0 < m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    {t : ℝ} (ht : 0 < t)
    {yflat : Fin ((n + m) * (d + 1)) → ℝ}
    (hy :
      yflat ∈ tsupport
        ((flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1) :
            SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ) :
          (Fin ((n + m) * (d + 1)) → ℝ) → ℂ)) :
    let y : NPointDomain d (n + m) :=
      (flattenCLEquivReal (n + m) (d + 1)).symm yflat
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I) ∈
        TubeDomainSetPi (ForwardConeAbs d (n + m))
```

Proof transcript for
`zSplit_mem_forwardTube_of_osConjTensorProduct_support`:

1. Transfer `hy` through `flattenSchwartzNPoint` to a support statement for
   `(f.1.osConjTensorProduct g.1) y`.
2. Use the support of `osConjTensorProduct` to get the left and right
   component support statements. The left statement is for `f.1` after the
   OS conjugation/reversal; the right statement is for `g.1`.
3. Apply the ordered-positive hypotheses `f.2` and `g.2` to the corresponding
   component supports.
4. Unfold `TubeDomainSetPi`, `ForwardConeAbs`, `xiShift`, and
   `wickRotatePoint`. Successive imaginary differences are exactly the
   positive ordered time gaps from the left/right supports, with the split gap
   increased by `t`; positivity of the split gap uses `ht`.
5. The `n = 0` branch has no left support statement; close it by the same
   split-gap computation using the first right point and `ht`.

To make the Fubini family global and continuous, do not branch directly on
`zSplit yflat ∈ TubeDomainSetPi C`; a raw `if` at the tube boundary is not a
sound continuity strategy. Instead introduce a cutoff supported inside the
tube-safe parameter set:

```lean
private theorem exists_transportTubeCutoff
    {n m : ℕ} (hm : 0 < m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let q : ℕ := n + m
    let M : ℕ := q * (d + 1)
    let Ω : Set (Fin M → ℝ) :=
      {yflat |
        let y : NPointDomain d q := (flattenCLEquivReal q (d + 1)).symm yflat
        xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I) ∈
            TubeDomainSetPi (ForwardConeAbs d q)}
    ∃ ρ : (Fin M → ℝ) → ℂ,
      ContDiff ℝ ∞ ρ ∧
      HasCompactSupport ρ ∧
      (∀ yflat ∈ tsupport
        ((flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1) :
            SchwartzMap (Fin M → ℝ) ℂ) :
          (Fin M → ℝ) → ℂ), ρ yflat = 1) ∧
      tsupport ρ ⊆ Ω ∧
      (∀ k : ℕ, ∃ Cρ : ℝ, ∀ yflat, ‖iteratedFDeriv ℝ k ρ yflat‖ ≤ Cρ)
```

Proof transcript for `exists_transportTubeCutoff`:

1. Prove `Ω` is open from `isOpen_tubeDomain`/`forwardConeAbs_isOpen`,
   continuity of `flattenCLEquivReal.symm`, continuity of `wickRotatePoint`,
   and the affine continuity of `xiShift`.
2. Prove the compact set
   `K := tsupport (flattenSchwartzNPoint (f.1.osConjTensorProduct g.1))`
   is contained in `Ω` using
   `zSplit_mem_forwardTube_of_osConjTensorProduct_support`; compactness comes
   from `hf_compact`, `hg_compact`, compact support of `osConjTensorProduct`,
   and transport through `flattenCLEquivReal`.
3. Use the positive distance between compact `K` and the closed complement
   `Ωᶜ`, then apply `exists_smooth_cutoff_of_closed` after translating/scaling
   its fixed-radius cutoff, to get a smooth compactly supported `ρ` with
   `ρ = 1` on `K` and `tsupport ρ ⊆ Ω`.
4. The derivative bounds are inherited from `exists_smooth_cutoff_of_closed`
   and the finite-dimensional affine scaling.

With such a cutoff, the transported Schwartz family is globally defined by:

```lean
let gTransport : (Fin M → ℝ) → SchwartzMap (Fin M → ℝ) ℂ :=
  fun yflat =>
    (ρ yflat) •
      multiDimPsiZExt Cflat
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (zSplitFlat yflat)
```

The production side conditions for this family are:

```lean
private theorem continuous_transportPsiZFamily_with_cutoff :
    Continuous gTransport

private theorem seminorm_transportPsiZFamily_with_cutoff_bound :
    ∀ k l : ℕ, ∃ Cg : ℝ, ∃ N : ℕ, Cg > 0 ∧
      ∀ yflat : Fin M → ℝ,
        SchwartzMap.seminorm ℝ k l (gTransport yflat) ≤
          Cg * (1 + ‖yflat‖) ^ N
```

Proof transcript for these two side conditions:

1. If `ρ yflat ≠ 0`, then `yflat ∈ Ω`; locally, `multiDimPsiZExt` rewrites to
   `multiDimPsiZ` and continuity follows from
   `multiDimPsiZ_seminorm_continuous` composed with the affine map
   `zSplitFlat`.
2. If `yflat ∉ tsupport ρ`, then `ρ = 0` on a neighborhood of `yflat`, so
   `gTransport` is locally zero.
3. Seminorm growth follows from compact support of `ρ`: on `tsupport ρ`, the
   image of `zSplitFlat` is contained in a compact subset of the tube, so the
   local uniform seminorm bounds for `multiDimPsiZ` give a uniform constant;
   outside `tsupport ρ`, the family is zero. Conclude with `N := 0`, or absorb
   the compact-region constant into `Cg * (1 + ‖yflat‖)^0`.

The retired draft claimed the transported kernel package would be Lean-ready
as follows. This is now false for the live route because the raw support packet
above does not put `zSplitFlat yflat` in the forward tube:

```lean
private theorem
    exists_transportKernel_pairing_singleSplitXiShiftScalar
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportInDualCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)) Tflat)
    (hFL :
      ∀ z : Fin (n + m) → Fin (d + 1) → ℂ,
        z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          bvt_F OS lgc (n + m) z =
            fourierLaplaceExtMultiDim
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              Tflat (flattenCLEquiv (n + m) (d + 1) z)) :
    ∃ KTransport : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t =
        Tflat KTransport ∧
      ∃ ρ : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ,
        ContDiff ℝ ∞ ρ ∧
        HasCompactSupport ρ ∧
        (∀ yflat ∈ tsupport
          ((flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1) :
              SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ) :
            (Fin ((n + m) * (d + 1)) → ℝ) → ℂ), ρ yflat = 1) ∧
        (∀ ξ, KTransport ξ =
          ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
            (((ρ yflat) •
              multiDimPsiZExt
                ((flattenCLEquivReal (n + m) (d + 1)) ''
                  ForwardConeAbs d (n + m))
                hCflat_open hCflat_conv hCflat_cone hCflat_salient
                (flattenCLEquiv (n + m) (d + 1)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i =>
                      wickRotatePoint
                        (((flattenCLEquivReal (n + m) (d + 1)).symm yflat) i))
                    ((t : ℂ) * Complex.I)))) ξ) *
              (flattenSchwartzNPoint (d := d)
                (f.1.osConjTensorProduct g.1)) yflat)
```

In production, the theorem body obtains `ρ` from `exists_transportTubeCutoff`,
defines the displayed family, proves the two Fubini side conditions from
`continuous_transportPsiZFamily_with_cutoff` and
`seminorm_transportPsiZFamily_with_cutoff_bound`, applies
`schwartz_clm_fubini_exchange`, rewrites the scalar integral by
`bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`, and uses `hFL` on the
support where `ρ = 1` and `fTransport` is nonzero. Outside that support, the
integrand is zero by the Schwartz test factor, so no tube-membership claim is
needed.

For symmetry with the transported package, the ambient Fubini construction can
be implemented as its own small theorem before the hard packet:

```lean
private theorem
    exists_ambientKernel_pairing_psiZTimeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∃ KAmbient : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
          Tflat KAmbient
```

Proof transcript for `exists_ambientKernel_pairing_psiZTimeShift`:

1. Use the displayed `M`, `k`, `hk`, `χhat`, `β`, `fpad0`, `fpad`,
   `ΨAmbient0`, `ambientOrbit`, `headCoord`, and `gAmbient` definitions from
   the hard theorem transcript.
2. Prove `hgAmbient_cont` and `hgAmbient_bound` by the exact copied proof from
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`.
3. Apply `schwartz_clm_fubini_exchange Tflat gAmbient fpad`.
4. Rewrite the scalar pairing field with `hTflat_bv`, the local
   right-tail-shift configuration lemma, `integral_comp_castFinCLE_eq`,
   `integral_finSucc_cons_eq`, `MeasureTheory.integral_prod_mul`, and
   `integral_normedUnitBumpSchwartzPi`, exactly as the existing BVLimits proof
   rewrites `hPair_repr`.
5. Return `KAmbient` and the resulting pair equality. The theorem deliberately
   does not prove the dual-cone EqOn; EqOn is the Section-4.3 comparison in the
   hard packet.

```lean
private theorem
    hardSingleSplit_psiZ_timeShift_expands_to_dualCone_eq_kernel_pairing
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    ∃ Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
    ∃ hTflat_supp :
      HasFourierSupportInDualCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)) Tflat,
    ∃ KAmbient KTransport :
      SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
          Tflat KAmbient ∧
      bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t =
          Tflat KTransport ∧
      Set.EqOn
        (KAmbient : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ)
        KTransport
        (DualConeFlat
          ((flattenCLEquivReal (n + m) (d + 1)) ''
            ForwardConeAbs d (n + m)))
```

Implementation transcript for
`hardSingleSplit_psiZ_timeShift_expands_to_dualCone_eq_kernel_pairing`:

1. Define `ψZ` exactly as displayed.
2. Rewrite the shifted right tensor by
   the local configuration lemma below; this is only a configuration-space
   rewrite and does not replace shifted `ψ` by shifted `g`.

```lean
private def rightTailTimeShiftConfig {n m : ℕ} (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) : NPointDomain d (n + m) :=
  fun i =>
    if n ≤ i.val then x i + timeShiftVec d t else x i

private theorem conjTensorProduct_timeShift_eq_rightTailTimeShift
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (τ : ℝ) (x : NPointDomain d (n + m)) :
    (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) x =
      (φ.conjTensorProduct ψ)
        (rightTailTimeShiftConfig (d := d) (n := n) (m := m) hm (-τ) x) := by
  -- Same proof as the private `conjTensorProduct_timeShift_eq_tailTimeShift`
  -- in `OSToWightman.lean`, but restated locally because that theorem and
  -- `tailTimeShiftConfig` are private there.
  simp only [SchwartzMap.conjTensorProduct_apply, timeShiftSchwartzNPoint_apply]
  congr 1
  · ext i μ
    have hi : ¬ n ≤ (Fin.castAdd m i).val := by
      simpa using (not_le_of_gt i.isLt)
    simp [rightTailTimeShiftConfig, hi]
  · ext j μ
    have hj : n ≤ (Fin.natAdd n j).val := by simp
    simp [rightTailTimeShiftConfig, hj, timeShiftVec, sub_eq_add_neg]
```

   Do not call the private imported `conjTensorProduct_timeShift_eq_tailTimeShift`
   from `OSToWightman.lean` in production; either keep the local lemma above in
   the target file or deliberately promote the configuration lemma to a public
   support theorem with a narrow exact-file check.
3. Flatten the full configuration with `flattenCLEquivReal (n + m) (d + 1)`.
   Do **not** try to force the ambient and transported sides into the same
   translated base `Ψ`. The representative data appear in the full Fourier-side
   kernel. The correct outputs are `KAmbient` and `KTransport`, together with
   pointwise formulas for those kernels on the dual cone.
4. Obtain the common distribution package:

```lean
obtain ⟨Tflat, hCflat_open, hCflat_conv, hCflat_cone, hCflat_salient,
  hTflat_supp, hTflat_bv, hTflat_FL⟩ :=
  exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr
    (d := d) OS lgc (n + m)
```

   The ambient pairing will use `hTflat_bv`; the transported shell will use
   `hTflat_FL`.
5. Construct the ambient kernel by the existing translated-orbit Fubini pattern:

```lean
let M : ℕ := (n + m) * (d + 1)
have hM_pos : 0 < M := by
  dsimp [M]
  have hnm_pos : 0 < n + m := by omega
  exact Nat.mul_pos hnm_pos (Nat.succ_pos _)
let k : ℕ := M - 1
have hk : k + 1 = M := by
  dsimp [k]
  exact Nat.succ_pred_eq_of_pos hM_pos
let χhat : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ ψZ
let β : SchwartzMap (Fin k → ℝ) ℂ := normedUnitBumpSchwartzPi k
let fpad0 : SchwartzMap (Fin (k + 1) → ℝ) ℂ := χhat.prependField β
let fpad : SchwartzMap (Fin M → ℝ) ℂ :=
  OSReconstruction.reindexSchwartzFin hk fpad0
let ΨAmbient0 : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ :=
  (flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
    (flattenSchwartzNPoint (d := d) ψ)
let ambientOrbit : ℝ → SchwartzMap (Fin M → ℝ) ℂ :=
  fun τ =>
    physicsFourierFlatCLM
      (OSReconstruction.reindexSchwartzFin
        (by ring : n * (d + 1) + m * (d + 1) = M)
        (SCV.translateSchwartz
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := m * (d + 1))
            (τ • flatTimeShiftDirection d m))
          ΨAmbient0))
let headCoord : (Fin M → ℝ) → ℝ :=
  fun x => ((OSReconstruction.castFinCLE hk).symm x) 0
let gAmbient : (Fin M → ℝ) → SchwartzMap (Fin M → ℝ) ℂ :=
  fun x => ambientOrbit (headCoord x)
```

   The continuity and seminorm-growth proofs are copied from
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`:
   use
   `continuous_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift` and
   `exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
   with `Ψ := ΨAmbient0`. Apply Fubini:

```lean
obtain ⟨KAmbient, hKAmbient_eval, hKAmbient_pair⟩ :=
  schwartz_clm_fubini_exchange Tflat gAmbient fpad
    hgAmbient_cont hgAmbient_bound
```

   Its pair field rewrites the left scalar to `Tflat KAmbient` after
   `hTflat_bv` rewrites each translated Wightman value and
   `integral_comp_castFinCLE_eq`/`integral_normedUnitBumpSchwartzPi` collapse
   the padded variables.
6. Construct the transported kernel by the new transport package:

```lean
obtain ⟨KTransport, hKTransport_pair, ρ, hρ_smooth, hρ_compact,
  hρ_one_on_support, hKTransport_eval⟩ :=
  exists_transportKernel_pairing_singleSplitXiShiftScalar
    (d := d) OS lgc hm f g hf_compact hg_compact ht
    hCflat_open hCflat_conv hCflat_cone hCflat_salient
    Tflat hTflat_supp hTflat_FL
```

   This Fubini call uses the flattened positive-time test
   `flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1)`, not `fpad`.
   The equality `hKTransport_pair` is obtained from the FL representation of
   `bvt_F`; it does not use the Wightman boundary representation and therefore
   is not circular.
7. Apply the public `psiZ_twoPi_pairing_formula` only to the real
   time-shift variable `τ`. The expected exponential is
   `Complex.exp (-(2 * Real.pi * t : ℂ) * ξ)` with the sign/normalization from
   `psiZ_pairing_formula`; do not use `SCV.psiZ_eq_exp_of_nonneg` here.
8. The pair equalities are obtained from the two Fubini pair fields:
   `hKAmbient_pair` rewrites the Wightman `ψ_Z`-paired time-shift integral to
   `Tflat KAmbient`.
   `hKTransport_pair` rewrites `bvtSingleSplitXiShiftScalar ...` to
   `Tflat KTransport` through
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`, the FL representation,
   support-safe cutoff identity `ρ = 1` on the test support, and Fubini.
9. Prove the dual-cone EqOn conjunct by introducing `ξ hξ` and rewriting both
   sides with `hKAmbient_eval ξ` and `hKTransport_eval ξ`. These are not the
   same raw parameter integral. First normalize both pointwise formulas:
   expand `physicsFourierFlatCLM` on the ambient side, apply
   `psiZ_twoPi_pairing_formula` to the `τ` integral, and rewrite the
   transported side by `multiDimPsiZExt_eq` on the cutoff support plus
   `multiDimPsiZR_eval_eq_of_support`/`fourierLaplaceExtMultiDim_eq_dynamic`
   on the dual cone. After these rewrites both pointwise values are expressed
   as the same full spatial/time-slice integral, except that the ambient slices
   are `φ`, `ψ` and the transported slices are `f.1`, `g.1`.
10. At that normalized pointwise equality, extract the nonnegative absolute-time
   data from `hξ ∈ DualConeFlat ((flattenCLEquivReal ...) '' ForwardConeAbs ...)`.
   Use the already documented tail-direction sign lemmas to show the cumulative
   tail time coordinates are nonnegative:

```lean
have htail_nonneg :
    ∀ j : Fin (n + m), 0 ≤
      -(∑ a, flatTailTimeShiftDirection d (n + m) j a * ξ a) := by
  intro j
  have hle :=
    flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (q := n + m) j hξ
  linarith
```

   Convert these cumulative tail values to
   `absTimesOfTailGapsSplitLeft`, `absTimesOfTailGapsSplitRight`, and, if
   needed, `absTimesOfTailGapsSplitLeftRev`. These are the nonnegative
   background times required by the existing Section-4.3 slice lemmas.
11. If the expanded left factor is exposed as `φ.borchersConj`, call the
   Section-4.3 slice bridge on the reversed vector
   `absTimesOfTailGapsSplitLeftRev` with nonnegativity from the previous dual
   cone tail-direction calculation. The right factor uses the unreversed
   `absTimesOfTailGapsSplitRight` vector.
12. Use
   `partialFourierSpatial_fun_eq_of_repr_eq_transport_on_nonneg` when the
   kernel contains full partial-spatial Fourier values, and use
   `unshifted_full_timeOrthant_descended_pairing_eq_of_section43Transport`
   only when the expansion has already isolated a one-variable
   `fourierInvPairingCLM`.
13. The `n = 0` branch bypasses all left slices via
   `section43_zero_left_repr_eq_transport_pointwise`; the same `Ψ` certificate
   is no longer required. The right-factor kernel and dual-cone EqOn proof are
   still produced.
14. The proof of the hard theorem then destructs this packet, applies
    `tflat_pairing_eq_of_eqOn_dualCone` to the EqOn
    conjunct, and closes by transitivity of the two expansion equalities.

Analytic obligations for the full-kernel packet:

1. The outer real-time pairing is introduced through
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` with
   `χ := (SchwartzMap.fourierTransformCLM ℂ) ψZ`. This supplies the exact
   scalar integral and avoids proving ad hoc integrability of the
   `τ`-integrand.
2. The one-sided support fact available for the Wightman time-shift functional
   is
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport`;
   use it only for quotient/descent statements, not as a replacement for the
   concrete expansion equalities.
3. The Fubini/Schwartz-family exchange used to construct `KAmbient` and
   `KTransport` must be an application of `schwartz_clm_fubini_exchange` or of
   a theorem already proved from it. For `KAmbient`, the side conditions are
   the copied translated-orbit continuity and seminorm-growth lemmas from
   BVLimits. For `KTransport`, the side conditions are exactly
   `continuous_transportPsiZFamily_with_cutoff` and
   `seminorm_transportPsiZFamily_with_cutoff_bound`.
4. Existing BVLimits growth lemmas may be reused only when the new
   `gAmbient`/`gTransport` family is definitionally the same translated orbit
   already covered there. If the expansion introduces a different finite orbit,
   first prove the analogue of the continuity and seminorm-growth lemmas for
   that exact family; do not silently reuse the right-block
   `zeroHeadBlockShift` estimates.
5. The public `psiZ_twoPi_pairing_formula` is the only Paley-Wiener identity
   needed in the packet. It is already available in `SCV/PaleyWiener.lean`;
   no additional export step is part of the current route.
6. The packet's final EqOn proof is pointwise in all remaining spatial/Fubini
   parameters. Those parameters must be introduced before the EqOn proof, not
   hidden behind extensional equality of two large integrals.

Retired readiness guard for this packet:

1. This raw packet is no longer Lean-ready because its tube-support premise is
   false. The apparent cutoff/Fubini completion would invoke the
   Fourier-Laplace representation outside its domain.
2. The `Set.EqOn KAmbient KTransport dualCone` idea remains mathematically
   useful, but the transport side must be rebuilt on a valid finite-height
   canonical shell, not on the raw `singleSplit` surface.
3. The active implementation order is the transported scalar-bridge order in
   §5.9.4a.1.ε after the 2026-04-13 scalar mismatch correction. In particular,
   the names
   `zSplit_mem_forwardTube_of_osConjTensorProduct_support`,
   `exists_transportTubeCutoff`,
   `exists_transportKernel_pairing_singleSplitXiShiftScalar`, and
   `hardSingleSplit_psiZ_timeShift_expands_to_dualCone_eq_kernel_pairing`
   must not be added to production for the current route.

The active positive-support theorem for hPsi is the direct spectral version
below. It is not a corollary of a hard single-split theorem; the single-split
surface is retired for the current route.

```lean
private theorem
    integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    let A : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
      osTimeShiftHilbert (d := d) OS lgc 1 one_pos
    let hA : IsSelfAdjoint A :=
      osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g.1 g.2⟧)) : OSHilbertSpace OS))
    ∀ t : ℝ, ∀ ht : 0 < t,
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)
```

Proof transcript for the expanded positive-support theorem:

1. Fix `t ht` and introduce `ψZ`, `A`, `hA`, `xF`, and `xG`.
2. Rewrite the left side by
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D`.
3. Apply the OS-I Lemma-4.2 core theorem
   `section43_timeShift_descendedPsiZ_eq_osHolomorphicValue_of_section43Transport`
   displayed below. This is the only hard Section-4.3 comparison allowed in
   this proof; do not replace it by a same-shell equality or by a theorem that
   rewrites shifted representatives directly.
4. Rewrite the OS holomorphic scalar by
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
   with `by simpa using ht`.
5. Close by `simpa [ψZ, A, hA, xF, xG]`. If Lean exposes a mismatch here, it is
   either a local abbreviation mismatch or a missing proof obligation in the
   core theorem below; record that exact goal in this subsection before adding
   support lemmas.

Implementation-ready replacement for Step 3:

```lean
private theorem
    section43_timeShift_descendedPsiZ_eq_osHolomorphicValue_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, ∀ ht : 0 < t,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f.1 f.2)
        (PositiveTimeBorchersSequence.single m g.1 g.2) (t : ℂ)
```

This theorem is the Lean surface for OS I Lemma 4.2, p. 96, after the OS-II
correction: start from `(4.22)`, insert the Wightman boundary-value
distribution and the Section-4.3 test transform, interchange the time
Fourier/Laplace order as in `(4.23) -> (4.24)`, and recognize the same
semigroup matrix element. It is not a wrapper, because it is the only theorem
in this packet that carries the genuine mathematical content of the
transported `ψ_Z` comparison.

Proof transcript for
`section43_timeShift_descendedPsiZ_eq_osHolomorphicValue_of_section43Transport`:

1. Fix `t ht` and set
   `ψZ := SCV.schwartzPsiZ (((2 * Real.pi : ℂ) * (t * Complex.I))) ...`.
   Let
   `TW := bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc φ ψ hψ_compact`.
2. Expand the left side only by
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply`:

```lean
have hdesc :
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        TW
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D ψZ)
      =
    TW ((SchwartzMap.fourierTransformCLM ℂ) ψZ) := by
  simpa [TW, ψZ] using
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
      (T := TW)
      (hT_supp :=
        bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
      (f := ψZ)
```

3. Expand `TW` only by
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`, obtaining the
   exact real-line scalar

```lean
∫ τ : ℝ,
  bvt_W OS lgc (n + m)
    (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
  (SchwartzMap.fourierTransformCLM ℂ ψZ) τ
```

   This is the Lean incarnation of the Wightman side of OS I `(4.23)`.
4. Apply the Fourier-tested matrix-element interchange theorem below. Its
   target is deliberately the OS holomorphic matrix element, not a new named
   kernel:

```lean
private theorem
    lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    (∫ τ : ℝ,
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
      (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f.1 f.2)
      (PositiveTimeBorchersSequence.single m g.1 g.2) (t : ℂ)
```

   This is not the public `lemma42_matrix_element_time_interchange`; it is the
   single-pair, fixed-`t`, Fourier-tested step used to supply that public
   consumer. It must be proved before the public consumer is invoked.
5. Close `section43_timeShift_descendedPsiZ...` by `rw [hdesc]`, the expansion
   of `TW`, and
   `lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport`.

Proof obligations for
`lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport`:

1. The proof must start from the OS I p. 96 `(4.23) -> (4.24)` interchange, not
   from any already-assembled positivity theorem. The only allowed paper input
   is the one-variable positive-support Fourier/Laplace interchange cited
   there as Lemma 8.4, instantiated on the concrete time variable created by
   `timeShiftSchwartzNPoint`.
   In Lean this is the same local atom documented for the shell-limit supplier:
   `lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ`, applied to
   the opposite-factor functional `Tloc` exposed by the partial-spatial Fourier
   expansion.
2. The spatial part of the interchange is ordinary Fourier transform of a
   tempered distribution. In Lean, expose it through the existing
   `partialFourierSpatial_fun_eq_integral`,
   `partialFourierSpatial_timeSliceSchwartz`, and
   `fourierInvPairingCLM_*partialFourierSpatial_timeSlice*` surfaces. Do not
   unfold the Section-4.3 quotient construction by hand.
3. The right distinguished slice index is fixed:
   `rψ : Fin m := ⟨0, hm⟩`. The left slice index is whatever
   the current frozen left factor exposes; if `n = 0`, use
   `section43_zero_left_repr_eq_transport_pointwise` from the finite-height
   packet instead of adding a `0 < n` hypothesis.
4. The nonnegative background-time hypotheses needed by
   `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport` must be
   explicit hypotheses of the local slice comparison. In the global hPsi
   theorem they must be proved from the actual frozen-time maps exposed by the
   partial-spatial Fourier expansion. If the implementation chooses to express
   those maps through cumulative tail gaps, first promote the displayed
   `absTimesOfTailGaps*` definitions and nonnegativity lemmas to production;
   until then, do not cite those names as existing declarations. These
   hypotheses must not be inferred from `ht`, `hf_compact`, `hg_compact`, or
   support of `ψZ`. For the common head-slice expansion, use the
   `headSliceIndex` / `orderedHeadGapTimes` support packet documented in the
   Lemma-8.4 shell-limit section.
5. The only allowed ambient-to-preimage replacements are the already proved
   scalar slice lemmas:
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`,
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   and
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`.
   After this step, no scalar integrand may still contain an ambient
   `φ`-slice or `ψ`-slice.
6. The shifted right factor is handled only after pairing against `𝓕ψZ`.
   Never use `hψg` to rewrite
   `timeShiftSchwartzNPoint (d := d) τ ψ` pointwise. The Paley-Wiener kernel
   and the time-variable interchange are what convert the shifted Wightman
   pairing into unshifted positive-support slice data.
7. The final recognition of the OS side is by the semigroup package:
   first use the Section-4.3 transformed positive-time slices to get
   `OSInnerProductTimeShiftHolomorphicValue`, then, only in the outer theorem
   above, rewrite to
   `ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag` using
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`.
8. The exact verification command after the Lean implementation of this packet
   is
   `lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`.

Lean implementation order for the `hPsi` packet:

1. Implement
   `lemma42_timeShift_pairing_eq_osHolomorphicValue_of_section43Transport`
   first, in a scratch harness if the first production attempt exposes more
   than local simplification goals. This theorem is the sole non-formal
   mathematical step of the packet.
2. Implement
   `section43_timeShift_descendedPsiZ_eq_osHolomorphicValue_of_section43Transport`
   by the five-line quotient expansion above. If this theorem takes more than
   the `hdesc` rewrite plus the previous theorem, the previous theorem's
   statement is not on the exact Lean surface and must be corrected before
   continuing.
3. Implement
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport`
   by rewriting through
   `section43_timeShift_descendedPsiZ_eq_osHolomorphicValue_of_section43Transport`
   and then
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`.
4. Implement
   `descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport`
   by
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply`,
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`, and the
   expanded integral theorem.
5. Implement
   `descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport` by
   converting the spectral boundary CLM with
   `selfAdjointSpectralBoundaryValueOffdiagCLM_apply` and
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`.
6. Only after those five steps should the existing reducer
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_ambient_descended_psiZ_boundaryValue_eq`
   be applied to get the positive-imaginary-axis canonical witness equality.

Local failure diagnostics:

1. If Step 1 leaves a goal comparing
   `timeShiftSchwartzNPoint (d := d) τ ψ` with a shifted `g`, the expansion is
   off route. Return to the Paley-Wiener/time-interchange stage and isolate
   the `ψ_Z` pairing before applying `hψg`.
2. If Step 1 leaves a goal requiring `HasCompactSupport (φ : NPointDomain d n → ℂ)`,
   the proof has accidentally polarized the Wightman side. The theorem
   statement must not be strengthened; use the off-diagonal route above.
3. If Step 1 leaves a goal involving raw `bvtSingleSplitXiShiftScalar`, the
   proof has drifted to the retired single-split route. Delete that attempt and
   restore the direct descended `ψ_Z` surface.
4. If Step 2 cannot close by unfolding the quotient apply theorem, then the
   expanded theorem is using the wrong `ψZ` positivity proof or the wrong
   `TW`; fix the local abbreviations rather than adding a forwarding lemma.
5. If Step 5 cannot match `selfAdjointSpectralBoundaryValueOffdiagCLM`, use the
   local `A`, `hA`, `xF`, `xG`, `ψZ` abbreviations and the `[simp]` theorem
   `selfAdjointSpectralBoundaryValueOffdiagCLM_apply`; do not unfold the four
   diagonal spectral measures unless Lean specifically exposes them after this
   rewrite.

Implementation-readiness addendum for the replacement transform surface:

Correction, 2026-04-14: the following two descended one-variable quotient
statements are not live production targets on the old `hφf`/`hψg` surface.
They name the former supplier roles that must eventually be revived only after
the explicit `(4.19)-(4.20)` transform has been implemented:

```lean
private theorem
    lemma84_bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport

private theorem
    section43_timeShift_descendedPsiZ_eq_osSchwingerValue_of_section43Transport
```

The integral-facing statements would be formal consequences of true supplier
theorems, but the old supplier hypotheses were too weak: by
`os1TransportComponent_apply`, they are satisfied by the same-test
specialization `φ := f.1`, `ψ := g.1`.  The first implementation step is
therefore not "prove the real-line integral equality" and not "fill the old
two sorry bodies."  The actual mathematical task is to implement the OS I
Section-4.3 transform surface from `(4.19)-(4.20)` and then restate the
common OS I p. 96 `(4.23) -> (4.24)` normal-form comparison on that surface.
No part of this step uses OS I Lemma 8.8 or any many-variable
separate-continuation principle; analytic continuation remains on the OS-II
`E0'` route already represented by `OSLinearGrowthCondition`, `bvt_F`, and
`bvt_W`.

The following local-data contract is retained as a checklist for the eventual
common normal form after the transform packet exists.  It is not permission to
reopen the quarantined supplier packet with only `hφf`/`hψg`.

Common local data for the expansion:

1. Right block:

```lean
let rψ : Fin m := headSliceIndex hm
let tψ : NPointDomain d m -> Fin m -> ℝ :=
  fun xψ => orderedHeadGapTimes (d := d) hm xψ
```

For every `hxψ : xψ ∈ OrderedPositiveTimeRegion d m`, the nonnegative
background-time hypothesis is

```lean
have htψ :
    ∀ i : Fin m, i ≠ rψ -> 0 ≤ tψ xψ i :=
  orderedHeadGapTimes_nonneg_of_orderedPositive
    (d := d) hm hxψ
```

2. Left block, positive-degree branch:

```lean
have hn : 0 < n := ...
let rφ : Fin n := headSliceIndex hn
let tφ : NPointDomain d n -> Fin n -> ℝ :=
  fun xφ => orderedHeadGapTimes (d := d) hn xφ
```

For every `hxφ : xφ ∈ OrderedPositiveTimeRegion d n`, use

```lean
have htφ :
    ∀ i : Fin n, i ≠ rφ -> 0 ≤ tφ xφ i :=
  orderedHeadGapTimes_nonneg_of_orderedPositive
    (d := d) hn hxφ
```

If the left factor is exposed through `SchwartzMap.conjTensorProduct_apply`,
the raw variable appears as `splitFirst n m y (Fin.rev i)`.  The
implementation must first reindex this back to the positive-time representative
before applying the Section-4.3 slice bridge.  Do not prove a new theorem that
requires the reversed ambient slice itself to be in the positive-time region
unless the reindexing lemma has been stated and proved.

3. Left block, zero-degree branch:

If `n = 0`, do not introduce a fake `Fin 0` slice and do not add a `0 < n`
hypothesis to either live theorem.  Use

```lean
section43_zero_left_repr_eq_transport_pointwise
  (d := d) hφf
```

to replace the zero-left ambient representative by the positive-time preimage
before the remaining right-block one-variable calculation.  In this branch the
only real slice variables are the right-block `rψ`, `tψ`, `htψ`, and `ξψ`.

4. Slice abbreviations in the positive-degree branch:

```lean
let φSlice : SchwartzMap ℝ ℂ :=
  partialFourierSpatial_timeSliceSchwartz
    (d := d) (n := n) φ rφ (tφ xφ) ξφ
let ψSlice : SchwartzMap ℝ ℂ :=
  partialFourierSpatial_timeSliceSchwartz
    (d := d) (n := m) ψ rψ (tψ xψ) ξψ
let fSlice : SchwartzMap ℝ ℂ :=
  partialFourierSpatial_timeSliceSchwartz
    (d := d) (n := n)
    (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ (tφ xφ) ξφ
let gSlice : SchwartzMap ℝ ℂ :=
  partialFourierSpatial_timeSliceSchwartz
    (d := d) (n := m)
    (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ (tψ xψ) ξψ
```

The permitted replacements are exactly the already-proved scalar slice
bridges:

```lean
fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
```

The one-variable support input for either `fSlice` or `gSlice` is always

```lean
fourierInvPairing_hasOneSidedFourierSupport _
  (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
    ...)
```

and the one-variable Lemma-8.4 atom is already implemented as

```lean
lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
```

No proof in this packet may unfold the Section-4.3 quotient construction after
the slice has been exposed.  The quotient/submodule interface is consumed only
through the four scalar slice bridges above.

Required normal-form theorem slots:

Production API audit for this contract:

The following pieces are already available and should be consumed directly.

1. Real-line descended-pairing expansion:
   `OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply`
   and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
2. One-variable support and Lemma-8.4 atom:
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport`,
   `fourierInvPairing_hasOneSidedFourierSupport`,
   `tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`,
   and `lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ`.
3. Section-4.3 one-variable slice replacement:
   the four `fourierInvPairingCLM_*_of_repr_eq_transport` lemmas listed
   above.
4. Head-gap nonnegativity:
   `headSliceIndex`, `orderedHeadGapTimes`, and
   `orderedHeadGapTimes_nonneg_of_orderedPositive`.
5. Zero-left representative replacement:
   `section43_zero_left_repr_eq_transport_pointwise`.
6. Diagnostic full-flat Wightman/Fubini infrastructure:
   `exists_timeShiftKernel_pairing_fourierTest`,
   `timeShiftFlatOrbit_apply_phase`,
   `exists_horizontalKernel_pairing_iteratedFourierLaplace`, and the
   canonical shell `Tflat` packet.

The sixth item is not the missing theorem.  It is finite-height/full-flat
diagnostic infrastructure and cannot be used to revive the quarantined
descended `ψ_Z` supplier packet.  What is missing from production is first the
explicit Section-4.3 Fourier-Laplace transform API, and then the
non-finite-height OS I `(4.23) -> (4.24)` expansion API that rewrites the
pointwise Wightman value, the descended `ψ_Z` pairing, and the OS Schwinger
scalar to one common partial-spatial/time-slice scalar.  If implementation
starts and the first unsolved goal is still a global `bvt_W`, global
`fourierPairingDescendsToSection43PositiveEnergy1D`, or global `OS.S` equality
rather than the local transform/slice goals above, the expansion API has not
yet been built.

Outer API theorem for the common normal form:

The final proved support theorem may have the following compact outer
statement, but it must **not** be introduced as a new unresolved production
`sorry`.  Its proof is the full partial-spatial/time-slice expansion specified
in this subsection.  The existential scalar `N` is acceptable only in the
proved theorem because the proof must construct it as the concrete common
iterated local scalar; it is not acceptable as a way to hide the normal form.

```lean
private theorem
    section43_common_descendedPsiZ_normalForms_of_fourierLaplaceTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m -> ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n -> ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m -> ℂ))
    (hφ_transform :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f)
    (hψ_transform :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        section43FourierLaplaceTransformComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ N : ℂ,
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) = N ∧
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D ψZ) = N ∧
      OS.S (n + m)
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) = N
```

Proof transcript for this outer theorem:

1. Define `ψZ` with the exact positivity proof shown in the statement.
2. Split on `n = 0`.
3. In the positive-degree branch, introduce the local data
   `rφ`, `tφ`, `htφ`, `rψ`, `tψ`, `htψ`, `φSlice`, `ψSlice`,
   `fSlice`, and `gSlice` exactly as above.
4. Construct `N` as the concrete iterated local scalar produced by the
   spatial-Fourier expansion.  This construction must be visible in the proof;
   it cannot be `classical exact ?_` or a choice from the three target
   equalities.
5. Prove `hW_point_nf : bvt_W ... = N` by the Wightman side of OS I `(4.23)`,
   applying `lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ` to
   the concrete one-variable functional exposed by the expansion.
6. Prove `hDesc_nf : descended ψZ pairing = N` by
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply`,
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`, and the same
   expansion as Step 5.
7. Prove `hOS_nf : OS.S ... = N` by the Euclidean side of `(4.24)`, using the
   Section-4.3 slice bridges to replace ambient slices by `fSlice`/`gSlice`.
8. Return `⟨N, hW_point_nf, hDesc_nf, hOS_nf⟩`.
9. In the zero-left branch, first rewrite by
   `section43_zero_left_repr_eq_transport_pointwise`; then repeat Steps 4-8
   with only right-block slice data.

After this theorem is proved on the explicit transform surface, the former
supplier lemmas can be restated and proved without additional mathematical
proof:

```lean
  let ψZ : SchwartzMap ℝ ℂ := ...
  obtain ⟨N, hW, hDesc, hOS⟩ :=
    section43_common_descendedPsiZ_normalForms_of_fourierLaplaceTransform
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact)
      (f := f) (g := g) (hf_compact := hf_compact)
      (hg_compact := hg_compact) hφ_transform hψ_transform ht
  exact hW.trans hDesc.symm
```

and

```lean
  let ψZ : SchwartzMap ℝ ℂ := ...
  obtain ⟨N, hW, hDesc, hOS⟩ :=
    section43_common_descendedPsiZ_normalForms_of_fourierLaplaceTransform
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact)
      (f := f) (g := g) (hf_compact := hf_compact)
      (hg_compact := hg_compact) hφ_transform hψ_transform ht
  exact hDesc.trans hOS.symm
```

The next production or scratch theorem must expose either the explicit
Fourier-Laplace transform apply theorem or the common scalar normal form before
the quarantined supplier packet is revived.  It is not enough to write
"expand by partial Fourier transform" in prose.  The theorem must provide the
following three named outputs, with the same local variables and the same
integration order on both sides.

1. `hW_point_nf`: the pointwise Wightman time-shift value

```lean
bvt_W OS lgc (n + m)
  (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))
```

is rewritten, after the spatial Fourier bookkeeping and the one-variable
Lemma-8.4 atom, as the iterated local scalar whose surviving one-variable
factor is

```lean
OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
  (fourierInvPairingCLM fSlice)
  (fourierInvPairing_hasOneSidedFourierSupport fSlice
    (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
      (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f) rφ (tφ xφ) ξφ))
  (section43PositiveEnergyQuotientMap1D ψZ)
```

or, if the opposite orientation is exposed first, the mathematically identical
`fourierInvPairingCLM gSlice` version followed by
`fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`.
The theorem statement must record which orientation the expansion actually
produces; do not leave this as an implementation choice inside the proof.

2. `hDesc_nf`: the descended global pairing

```lean
OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
  (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
    (d := d) OS lgc φ ψ hψ_compact)
  (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
    (d := d) OS lgc hm φ ψ hψ_compact)
  (section43PositiveEnergyQuotientMap1D ψZ)
```

is rewritten to the same iterated local scalar as `hW_point_nf`.  This output
starts by applying
`OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply`
and `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`, but it must
not stop at the real-line `τ` integral.  It must continue through the
partial-spatial/time-slice expansion until the shifted representative has
disappeared and the only remaining one-variable test class is
`section43PositiveEnergyQuotientMap1D ψZ`.

3. `hOS_nf`: the Euclidean Schwinger scalar

```lean
OS.S (n + m)
  (ZeroDiagonalSchwartz.ofClassical
    (f.1.osConjTensorProduct
      (timeShiftSchwartzNPoint (d := d) t g.1)))
```

is rewritten to that same iterated local scalar.  This is the OS side of the
same `(4.23) -> (4.24)` computation.  Its final recognition must use the
semigroup/Schwinger package already on the route, ending at
`OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single` in the outer formal
theorem if necessary.  It must not be obtained by Wightman-side diagonal
polarization, by a same-shell `W = S` assertion, or by a direct rewrite of
`timeShiftSchwartzNPoint t ψ` using `hψg`.

Once these three outputs are available on the explicit transform surface, the
former supplier lemmas become mechanical:

1. `lemma84_bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport` is
   `hW_point_nf.trans hDesc_nf.symm`, with only local `simpa [ψZ, ...]`
   cleanup.
2. `section43_timeShift_descendedPsiZ_eq_osSchwingerValue_of_section43Transport`
   is `hDesc_nf.trans hOS_nf.symm`, with only local `simpa [ψZ, ...]`
   cleanup.

Implementation order for the normal-form contract:

1. Completed 2026-04-14: the replacement transform support file from §5.9.1a
   now provides `section43DiffCoordRealCLE` as an alias of
   `BHW.realDiffCoordCLE`, `section43DiffPullbackCLM`,
   `tsupport_section43DiffPullback_subset_positiveOrthant`,
   `section43FourierLaplaceIntegral`, and the expanded theorem
   `section43FourierLaplaceIntegral_eq_time_spatial_integral`.  It also
   provides `section43TimeSplitCLE` and its apply/symm simp lemmas.  The exact
   check
   `lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean`
   terminated with exit code `0`.
2. Then decide whether the next formal target is Option A
   `section43FourierLaplaceTransformComponent` or Option B
   `section43FourierLaplaceIntegral_slice_normalForm`.  Do not touch
   `OSToWightmanPositivity.lean` until one of these transform surfaces has a
   precise apply theorem whose hypotheses are not discharged by
   `simp [os1TransportComponent_apply]`.
3. Only after the transform surface exists, rehearse the positive-degree local
   slice equality using the exact four scalar slice bridges listed above.
   Because `fourierInvPairingCLM` and several slice helpers are currently
   private to `OSToWightmanPositivity.lean`, an external `test/` file cannot
   state this theorem verbatim unless those helpers are first moved to a small
   support module or made public deliberately.  Until that split is done, the
   exact rehearsal theorem belongs in the same file, directly above the global
   normal-form theorem.  It should quantify over `rφ`, `tφ`, `htφ`, `ξφ`,
   `rψ`, `tψ`, `htψ`, and `ξψ`; it should not mention global shells.
4. Add the zero-left branch separately by using
   `section43_zero_left_repr_eq_transport_pointwise`.  This branch should have
   no `Fin 0` slice variables.
5. Only after both branches compile, add the global expansion theorem that
   produces `hW_point_nf`, `hDesc_nf`, and `hOS_nf`.  If the partial-spatial
   expansion API does not currently expose the needed integration order, build
   that API first in the smallest relevant companion file; do not replace this
   theorem by a wrapper around the quarantined false surfaces.
6. After the global expansion theorem compiles either in same-file rehearsal
   form or in a genuine scratch file with the required helpers exported, port
   it to its final location, then restate/revive the former supplier lemmas by
   the transitivity proofs above.
7. Exact verification after any production Lean edit remains
   `lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`.

Legacy quotient-slice support theorem, not the replacement transform:

The following theorem shape is retained only as support for quotient equality
after the transform component has been established.  It is not a
blocker-facing theorem and cannot revive the quarantined supplier packet,
because its hypotheses are exactly the old quotient-image hypotheses
`hφf`/`hψg`.

It is not global and should compile without mentioning `bvt_W`, `bvt_F`,
`OS.S`, canonical witnesses, shell limits, or `ψZ`.  Its content is the exact
positive-degree local slice replacement on the current quotient-image surface:

```lean
private theorem
    section43_local_positiveDegree_slice_pairing_eq_of_transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n} {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n) (tφ : Fin n -> ℝ)
    (htφ : ∀ i : Fin n, i ≠ rφ -> 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m -> ℝ)
    (htψ : ∀ i : Fin m, i ≠ rψ -> 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz
            (d := d) (n := n) φ rφ tφ ξφ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz
            (d := d) (n := m) ψ rψ tψ ξψ))
```

Proof transcript:

```lean
  exact
    fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
      (d := d) (n := n) (m := m)
      (φ := φ) (ψ := ψ) (f := f) (g := g)
      hφf hψg rφ tφ htφ ξφ rψ tψ htψ ξψ
```

This theorem is already present in production under the longer name above.
Do not add a shorter forwarding theorem merely to rename it.  It remains useful
only after the new transform theorem has supplied representatives whose
quotient classes genuinely arise from `(4.19)-(4.20)` rather than from the
same-test specialization.

Legacy zero-left quotient support theorem:

The zero-left branch of any eventual transformed normal form may use the
already-proved pointwise replacement below, but this theorem is also only a
quotient-support fact on the old surface, not a transform theorem.  It must not
be used to bypass the `(4.19)-(4.20)` packet.

```lean
private theorem
    section43_local_zeroLeft_repr_eq_transport
    {φ : SchwartzNPoint d 0}
    {f : euclideanPositiveTimeSubmodule (d := d) 0}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        os1TransportComponent d 0 f) :
    φ = (EuclideanPositiveTimeComponent.ofSubmodule f).1
```

Proof transcript:

```lean
  exact section43_zero_left_repr_eq_transport_pointwise
    (d := d) hφf
```

The global zero-left normal form may then use ordinary rewriting by this
equality before the right-block `ψZ` calculation.  Any attempted proof that
creates a term of type `Fin 0` after this branch split is off the intended
surface.

Readiness checklist:

1. The replacement transform file exists and compiles, including
   `section43DiffPullbackCLM`, `section43FourierLaplaceIntegral`, and the
   ordered-support theorem for the difference-coordinate pullback.
2. The chosen Option A or Option B transform apply theorem is stated with
   hypotheses that cannot be discharged by `simp [os1TransportComponent_apply]`.
3. There is a compiled same-file rehearsal theorem or production theorem for
   the local positive-degree slice replacement using `htφ` and `htψ`.
4. The `n = 0` branch is compiled and does not add a `0 < n` hypothesis.
5. The global normal-form theorem records the actual orientation of
   `fourierInvPairingCLM`, rather than saying "use symmetry if needed."
6. The shifted right factor is gone before any quotient-representative
   hypothesis is used.
7. The final scalar on the OS side is the Schwinger scalar above, not
   `bvtSingleSplitXiShiftScalar`, `KShell`, `KHorizontal`, or a finite-height
   residual.
8. No theorem in the packet requires
   `HasCompactSupport (φ : NPointDomain d n -> ℂ)`.
9. No theorem in the packet contains `set_option maxHeartbeats 0`.

If any item in this checklist is missing, the docs are still not 100%
implementation-ready for reviving the quarantined supplier packet, and the
next step is to fill that exact missing theorem slot rather than editing old
`sorry` bodies.

Current readiness audit for the common normal form, 2026-04-14:

0. The proof is **not** implementation-ready for reviving the quarantined
   supplier packet, but the first production object is now complete:
   `Section43FourierLaplaceTransform.lean` compiles and defines the
   difference-coordinate pullback plus the scalar `(4.20)` integral, including
   the expanded time-Laplace/spatial-Fourier integral theorem, the algebraic
   one-coordinate time split, and the `integral_section43TimeSplit`
   Fubini/change-of-variables bridge.  Its coordinate map is correctly an alias
   of the already existing `BHW.realDiffCoordCLE n d`, not a new
   difference-coordinate construction.  The integrability/factorization packet
   for `section43FourierLaplaceIntegral_eq_iterated_oneCoordinateLaplace` is
   also now complete on the positive-energy surface.  The next missing
   production object is the coordinate bridge from
   `MeasurableEquiv.piFinSuccAbove.symm (s, τbg)` to the existing
   `Function.update t r s` one-variable slice API, followed by extraction of
   the pure one-variable slice/Laplace helpers out of the positivity frontier.

1. The local positive-degree slice replacement is already available in
   production, in the exact orientation expected by the current blueprint:

```lean
fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
```

   Therefore the next implementation step must not add a shorter forwarding
   theorem merely to rename this result.  If a same-file rehearsal theorem is
   introduced, it must be because the global expansion proof needs a local
   theorem with exactly that statement for elaboration, not because the
   mathematical route is unclear.

2. The zero-left branch is already available in production as

```lean
section43_zero_left_repr_eq_transport_pointwise
```

   The global proof must split on `n = 0` before any left slice is introduced.
   Any branch that manufactures `rφ : Fin 0` is off route.

3. The real-line descended-pairing expansion is already formal from

```lean
fourierPairingDescendsToSection43PositiveEnergy1D_apply
bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D
```

   The hPsi integral-to-descended step should therefore remain a short
   transitivity proof.  If a future Lean attempt is proving integrability or
   unfolding the chosen tempered functional at this level, it has started one
   layer too high.

4. The OS-side positive-real semigroup rewrite is already formal from

```lean
OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
bvt_F_osConjTensorProduct_timeShift_eq_xiShift
```

   This may be used only to recognize the Euclidean Schwinger side for the
   positive-time preimages `f` and `g`.  It is not a Wightman-side comparison
   theorem.

5. Current-code convention map for Section 4.3 transport:

```lean
os1TransportComponent d n f =
  section43PositiveEnergyQuotientMap (d := d) n f.1
```

   This is `os1TransportComponent_apply` in
   `Section43Codomain.lean`.  Thus the hypotheses `hφf` and `hψg` mean that
   the ambient representatives `φ`, `ψ` agree with the positive-time
   representatives `f.1`, `g.1` after quotienting by functions vanishing on
   the positive-energy region.  They do **not** contain a hidden multivariate
   Fourier-Laplace transform that can be unfolded later.

   Consequence: all Fourier/Laplace content in the proof must enter through
   the explicit partial-spatial/time-slice API

```lean
partialFourierSpatial_fun_eq_integral
partialFourierSpatial_timeSliceSchwartz
lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
```

   together with the scalar slice bridges listed above.  A proof step that
   says "unfold `os1TransportComponent` to get the Section-4.3 transform" is
   wrong on the current code surface.

   Sanity gate before Lean implementation: the paper's notation
   `f_n -> \check f_n` must be accounted for by an explicit theorem in the
   global expansion proof, not by this definition.  On the current code
   surface, either the ambient representative `φ` is already the transformed
   representative and `hφf` records only its half-space quotient class, or the
   theorem statement is missing the real transport map.  The next proof-doc
   pass must make this convention explicit in the construction of `N`.  If it
   cannot, the theorem surface must be corrected before any production sorry is
   closed.

   Correction, 2026-04-14: this is not merely a documentation nicety.  On the
   current production definition, the transported hypotheses are satisfied by
   the same-test specialization

```lean
φ := f.1
ψ := g.1
```

   because `os1TransportComponent_apply` reduces them to `rfl`.  Therefore any
   theorem that assumes only `hφf` and `hψg` and concludes, for every `t > 0`,

```lean
bvt_W OS lgc (n + m)
  (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))
=
OS.S (n + m)
  (ZeroDiagonalSchwartz.ofClassical
    (f.1.osConjTensorProduct
      (timeShiftSchwartzNPoint (d := d) t g.1)))
```

   specializes to the withdrawn Package-C/`hschw` comparison on identical test
   data.  That theorem surface is unsafe unless it contains an explicit
   Section-4.3 transform/normal-form hypothesis strong enough to prevent the
   `φ = f.1`, `ψ = g.1` collapse, or unless the production map is changed to
   the actual paper transform rather than the current quotient inclusion.

   Production consequence: the transported-descended `ψ_Z` packet with only
   `hφf`/`hψg` should remain quarantined.  The next live theorem surface must
   be the common-normal-form expansion theorem itself, or a smaller explicit
   Section-4.3 transform theorem that constructs the same scalar `N`.

   OS I formula check, 2026-04-14: the missing transform is the paper's
   `(4.19)-(4.20)` construction, not the current quotient-inclusion map.  In
   paper notation, first pass from ordered variables to difference variables:

```text
f^+(x_1, x_2 - x_1, ..., x_n - x_{n-1}) = f(x_1, ..., x_n).
```

   Then the Section-4.3 transformed representative is obtained by spatial
   Fourier transform and time Laplace transform on the half-space
   `q_k^0 >= 0`:

```text
tilde f_n(q_1, ..., q_n)
  = ∫ f_n^+(ξ_1, ..., ξ_n)
      exp(-Σ_k (ξ_k^0 q_k^0 - i ξ_k^sp · q_k^sp)) dξ.
```

   This is the transform that prevents the same-test collapse.  Therefore the
   next production theorem cannot be phrased as

```lean
section43PositiveEnergyQuotientMap (d := d) n φ =
  os1TransportComponent d n f
```

   unless `os1TransportComponent` itself is replaced by the `(4.19)-(4.20)`
   transform.  As the code stands, the correct replacement surface is one of
   the following, in decreasing order of desirability:

   A. define a new component map, e.g. `section43FourierLaplaceTransformComponent`,
   from positive-time Euclidean data to `Section43PositiveEnergyComponent`,
   with an apply theorem whose right hand side is the `(4.19)-(4.20)` integral
   and not `section43PositiveEnergyQuotientMap f.1`;

   B. if the full map is too large for the immediate frontier, prove the exact
   slice-level apply theorem for the local scalar expansion, again unfolding
   to the `(4.19)-(4.20)` spatial-Fourier/time-Laplace integral rather than to
   quotient equality on `f.1`;

   C. only as a temporary proof-doc device, state the common-normal-form theorem
   with an explicit `hTransform_apply` hypothesis containing that integral
   formula.  This is not acceptable as a production wrapper unless the
   hypothesis is immediately discharged by A or B.

   Lean-readiness gate for the replacement theorem:

   1. Its hypotheses must not be provable by `rfl` after
      `simp [os1TransportComponent_apply]`.
   2. The proof must mention the difference-coordinate conversion corresponding
      to `(4.19)`.  In current code this should be connected to the existing
      `BHW.realDiffCoordCLE n d` infrastructure rather than invented as a new
      unrelated coordinate system.
   3. The proof must mention the spatial Fourier/time Laplace integral
      corresponding to `(4.20)`.  In current code this should connect to
      `partialFourierSpatial_fun_eq_integral`,
      `partialFourierSpatial_timeSliceSchwartz`,
      `complexLaplaceTransform`, and
      `lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ`.
   4. The first output theorem should be one-component/slice-local if needed;
      do not reopen the quarantined two-pair scalar comparison until this
   transform apply theorem exists.

   OS-II correction guard: this use of OS I is only the explicit Section-4.3
   test-function transform and the formal `(4.23) -> (4.24)` integration
   pattern.  It is **not** a license to use OS I Lemma 8.8.  OS II explicitly
   says Lemma 8.8 in OS I is wrong, and the production route must continue to
   take analytic continuation and boundary-value existence from the repaired
   OS-II/E0' path already represented by `OSLinearGrowthCondition` and the
   existing `bvt_F`/`bvt_W` construction.  Any new theorem that invokes a
   many-variable OS I Whitney-extension or Lemma-8.8-style continuation is off
   route.

6. The unresolved item is narrower and more precise than before.  Production
   now has the explicit Section-4.3 Fourier-Laplace transform **apply**
   surface:

```lean
section43FourierLaplaceRepresentative
section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_posCoord
section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_height
```

   This is not yet a full Schwartz-valued component map, but it is enough to
   prevent the same-test collapse in any theorem that assumes an ambient
   representative has the actual `(4.19)-(4.20)` transform values.  What
   production still lacks is the global non-finite-height spatial-Fourier
   expansion theorem that constructs the common scalar `N`.  The current
   blueprint is not 100% Lean-implementation-ready for reviving the
   quarantined descended-`ψ_Z` supplier packet until that construction of `N`
   is specified at Lean level.

Packet I proof-doc target after the explicit transform-apply surface:

The next theorem is not the old supplier
`lemma84_bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport`.  The next
theorem is the Wightman descended-pairing expansion to the **same iterated
one-variable scalar** already produced by Packet H.

The theorem should be component-local before it is pair-global.  In prose, for
a positive component degree `N + 1`, transformed representative `Φ`, positive
time preimage `F`, positive-energy momentum point `q`, distinguished coordinate
`r`, and height relation `q_r^0 = 2π η`, Packet H gives

```lean
Φ q =
  ∫ τbg : Fin N → ℝ,
    exp(background q τbg) *
      fourierPairingDescendsToSection43PositiveEnergy1D
        (section43FourierInvPairingCLM
          (section43PartialFourierSpatialTimeSliceSchwartz
            (section43DiffPullbackCLM d (N + 1) F)
            r ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
            (section43QSpatial d (N + 1) q)))
        ...
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ (((q_r^0 : ℂ) * Complex.I)) ...)).
```

The missing Wightman-side expansion must prove that the descended canonical
time-shift functional gives exactly that right hand side:

```lean
private theorem
    section43_descendedWightmanPsiZ_eq_iterated_transformSliceScalar
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    -- explicit transformed representative data for the relevant component
    (F : euclideanPositiveTimeSubmodule (d := d) (N + 1))
    (Φ : SchwartzNPoint d (N + 1))
    (hΦ : section43FourierLaplaceRepresentative d (N + 1) F Φ)
    (q : NPointDomain d (N + 1)) (r : Fin (N + 1))
    (hq : q ∈ section43PositiveEnergyRegion d (N + 1))
    (η : ℝ) (hη : 0 < η)
    (hqr : section43QTime (d := d) (n := N + 1) q r =
      2 * Real.pi * η)
    -- bookkeeping tying the pair `(φ, ψ)` to this transformed component
    (hPairTransform :
      -- not a wrapper: this must be the explicit spatial-Fourier/time-Laplace
      -- expansion identifying the pair data with `F`, `Φ`, `q`, and `r`
      section43PairTransformBookkeeping OS lgc hm φ ψ F Φ q r) :
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact)
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
        (d := d) OS lgc hm φ ψ hψ_compact)
      (section43PositiveEnergyQuotientMap1D
        (SCV.schwartzPsiZ
          (((section43QTime (d := d) (n := N + 1) q r : ℂ) *
            Complex.I)) ...)) =
    ∫ τbg : Fin N → ℝ,
      exp(background q τbg) *
        fourierPairingDescendsToSection43PositiveEnergy1D
          (section43FourierInvPairingCLM
            (section43PartialFourierSpatialTimeSliceSchwartz
              (section43DiffPullbackCLM d (N + 1) F)
              r ((section43TimeSplitMeasurableEquiv r).symm (0, τbg))
              (section43QSpatial d (N + 1) q)))
          ...
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((section43QTime (d := d) (n := N + 1) q r : ℂ) *
                Complex.I)) ...))
```

The placeholder `section43PairTransformBookkeeping` is **not** acceptable as a
production hypothesis.  It marks the remaining proof-doc gap: before Lean
implementation, replace it with explicit equalities/reindexing lemmas that
state how the two-block Wightman time-shift expansion supplies the component
data `F`, `Φ`, `q`, and `r`.  Those equalities must expose:

1. the degree conversion from `n + m` with `hm : 0 < m` to `N + 1`;
2. the distinguished time coordinate satisfying `q_r^0 = 2π η`;
3. the background time coordinates used by `section43TimeSplitMeasurableEquiv`;
4. the exact orientation of the surviving one-variable pairing functional;
5. the scalar normalization lemmas
   `section43QTime_complexPsiArg_eq_of_height` and
   `section43_realHeight_complexPsiArg_eq` only at the final syntactic
   matching point.

Concrete replacement for `section43PairTransformBookkeeping`, 2026-04-14:

The placeholder must not be replaced by one large hypothesis.  The local code
audit shows that the pair bookkeeping has three independent pieces, and each
piece needs its own theorem before any global consumer is implementation-ready.

First, isolate the **right-tail time-shift coordinate API**.  The existing
pointwise theorem

```lean
osConjTensorProduct_timeShift_eq_tailShift
```

already proves that shifting the right factor by `t` is the same as evaluating
the unshifted tensor product on the combined configuration whose last `m`
points are translated by `-timeShiftVec d t`.  The next support file should
name this map, because the same expression is now needed at the Section-4.3
difference-coordinate level:

```lean
def section43RightTailShift (d n m : ℕ) [NeZero d] (t : ℝ)
    (x : NPointDomain d (n + m)) : NPointDomain d (n + m) :=
  fun i μ => if n <= i.val ∧ μ = 0 then x i μ - t else x i μ
```

This is the coordinate-level version of subtracting `timeShiftVec d t` on the
tail.  Keeping it in this form avoids importing the Semigroup layer into the
pure Section-4.3 Fourier-Laplace support file; a later Semigroup bridge can
rewrite the existing `timeShiftVec` tail-shift expression to this map.

For `hm : 0 < m`, define the boundary/tail-gap coordinate

```lean
def section43TailGapIndex {n m : ℕ} (hm : 0 < m) : Fin (n + m) :=
  ⟨n, Nat.lt_add_of_pos_right hm⟩

def section43TailGapSplitIndex {n m : ℕ} (hm : 0 < m) :
    Fin (n + m - 1 + 1) :=
  ⟨n, by omega⟩
```

The required coordinate theorem is then the following pure algebra statement:
after applying `section43DiffCoordRealCLE d (n + m)`, the map
`section43RightTailShift d n m t` changes exactly the one tail-gap time
coordinate and leaves every other difference coordinate fixed.

```lean
theorem section43DiffCoordRealCLE_rightTailShift_time
    (d n m : ℕ) [NeZero d] (hm : 0 < m)
    (t : ℝ) (x : NPointDomain d (n + m)) :
    let r := section43TailGapIndex (n := n) (m := m) hm
    section43QTime (d := d) (n := n + m)
        (section43DiffCoordRealCLE d (n + m)
          (section43RightTailShift d n m t x))
      =
    Function.update
      (section43QTime (d := d) (n := n + m)
        (section43DiffCoordRealCLE d (n + m) x))
      r
      (section43QTime (d := d) (n := n + m)
        (section43DiffCoordRealCLE d (n + m) x) r - t)
```

and the spatial companion:

```lean
theorem section43DiffCoordRealCLE_rightTailShift_spatial
    (d n m : ℕ) [NeZero d]
    (t : ℝ) (x : NPointDomain d (n + m)) :
    section43QSpatial (d := d) (n := n + m)
        (section43DiffCoordRealCLE d (n + m)
          (section43RightTailShift d n m t x))
      =
    section43QSpatial (d := d) (n := n + m)
      (section43DiffCoordRealCLE d (n + m) x)
```

This is the precise Lean form of the "tail gap" sentence in the paper.  The
case `n = 0` is included: then the distinguished coordinate is `0`, and the
same update statement says the first absolute time coordinate is shifted by
`-t`.  The spatial theorem is more general than the time theorem and does not
need `hm`, because the coordinate-wise tail shift leaves all spatial
coordinates untouched for every `m`.

Second, isolate the **time-split bookkeeping API**.  Once the right-tail shift
has been rewritten as a single-coordinate update, the existing
`section43TimeSplitMeasurableEquiv r` must be connected to that update:

```lean
theorem section43TimeSplitMeasurableEquiv_tailGap_update
    {N : ℕ} (r : Fin (N + 1)) (tau : Fin (N + 1) -> ℝ) (t : ℝ) :
    section43TimeSplitMeasurableEquiv r
        (Function.update tau r (tau r - t))
      =
    (tau r - t, fun i : Fin N => tau (r.succAbove i))
```

This is the exact `MeasurableEquiv.piFinSuccAbove` orientation already used by
`section43TimeSplitMeasurableEquiv`.  What matters for readiness is
non-negotiable: the theorem must expose that the one real integration variable
in the Wightman time-shift functional is the same variable as the distinguished
Section-4.3 time coordinate.

Production status, 2026-04-14: this tail-gap packet is now implemented in
`Section43FourierLaplaceTransform.lean` and exact-checked.  The coordinate
definition is the pure coordinate-level tail shift, not a Semigroup import.

Third, isolate the **tail-gap background index API**.  The global consumer must
not hide the degree conversion from `n + m` to `(n + m - 1) + 1` behind
implicit casts.  After removing the distinguished gap coordinate
`section43TailGapIndex hm`, the background variables split into:

```lean
def section43TailBgLeftIndex {n m : ℕ} (hm : 0 < m)
    (i : Fin n) : Fin (n + m - 1) :=
  ⟨i.val, by omega⟩

def section43TailBgRightIndex {n m : ℕ} (hm : 0 < m)
    (j : Fin (m - 1)) : Fin (n + m - 1) :=
  ⟨n + j.val, by omega⟩

def section43TailBgLeftRevIndex {n m : ℕ} (hm : 0 < m)
    (i : Fin n) : Fin (n + m - 1) :=
  section43TailBgLeftIndex hm (Fin.rev i)
```

The required orientation lemmas are:

```lean
theorem section43TailGap_succAbove_left
    {n m : ℕ} (hm : 0 < m) (i : Fin n) :
    (section43TailGapSplitIndex (n := n) (m := m) hm).succAbove
        (section43TailBgLeftIndex (n := n) (m := m) hm i) =
      (⟨i.val, by omega⟩ : Fin (n + m - 1 + 1))

theorem section43TailGap_succAbove_leftRev
    {n m : ℕ} (hm : 0 < m) (i : Fin n) :
    (section43TailGapSplitIndex (n := n) (m := m) hm).succAbove
        (section43TailBgLeftRevIndex (n := n) (m := m) hm i) =
      (⟨(Fin.rev i).val, by omega⟩ : Fin (n + m - 1 + 1))

theorem section43TailGap_succAbove_right
    {n m : ℕ} (hm : 0 < m) (j : Fin (m - 1)) :
    (section43TailGapSplitIndex (n := n) (m := m) hm).succAbove
        (section43TailBgRightIndex (n := n) (m := m) hm j) =
      (⟨n + 1 + j.val, by omega⟩ : Fin (n + m - 1 + 1))
```

and the corresponding `section43TimeSplitMeasurableEquiv` background-coordinate
readout lemmas:

```lean
theorem section43TimeSplit_tailGap_background_left
    {n m : ℕ} (hm : 0 < m)
    (tau : Fin (n + m - 1 + 1) -> ℝ) (i : Fin n) :
    (section43TimeSplitMeasurableEquiv
        (section43TailGapSplitIndex (n := n) (m := m) hm) tau).2
        (section43TailBgLeftIndex (n := n) (m := m) hm i) =
      tau (⟨i.val, by omega⟩ : Fin (n + m - 1 + 1))

theorem section43TimeSplit_tailGap_background_leftRev
    {n m : ℕ} (hm : 0 < m)
    (tau : Fin (n + m - 1 + 1) -> ℝ) (i : Fin n) :
    (section43TimeSplitMeasurableEquiv
        (section43TailGapSplitIndex (n := n) (m := m) hm) tau).2
        (section43TailBgLeftRevIndex (n := n) (m := m) hm i) =
      tau (⟨(Fin.rev i).val, by omega⟩ : Fin (n + m - 1 + 1))

theorem section43TimeSplit_tailGap_background_right
    {n m : ℕ} (hm : 0 < m)
    (tau : Fin (n + m - 1 + 1) -> ℝ)
    (j : Fin (m - 1)) :
    (section43TimeSplitMeasurableEquiv
        (section43TailGapSplitIndex (n := n) (m := m) hm) tau).2
        (section43TailBgRightIndex (n := n) (m := m) hm j) =
      tau (⟨n + 1 + j.val, by omega⟩ : Fin (n + m - 1 + 1))
```

These are not cosmetic.  They name the exact coordinates that Eq. `(4.23) ->
(4.24)` calls the left reversed block, the central one-variable gap, and the
right internal block.  They also prevent a silent return to the old same-test
surface: every later scalar normal form must show whether its background
functional is reading `Fin.castAdd m i`, `Fin.castAdd m (Fin.rev i)`, or the
right-internal index `n + 1 + j`.

Production status, 2026-04-14: this background-index packet is now implemented
and exact-checked.  The extra `section43TailGapSplitIndex` is deliberate: the
tail-shift theorem lives on `Fin (n + m)`, while
`section43TimeSplitMeasurableEquiv` needs the same coordinate written as
`Fin (n + m - 1 + 1)`.

Fourth, isolate the **component projection API** for a full positive-energy
point.  The separate-representative route needs concrete maps from a full
`q : NPointDomain d (n + m)` to the left, Borchers-reversed-left, and right
component variables:

```lean
def section43LeftBlock (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) : NPointDomain d n :=
  fun i => q (Fin.castAdd m i)

def section43LeftRevBlock (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) : NPointDomain d n :=
  fun i => q (Fin.castAdd m (Fin.rev i))

def section43RightTailBlock (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) : NPointDomain d m :=
  fun j => q (Fin.natAdd n j)
```

The required support and time-coordinate lemmas are:

```lean
theorem section43LeftBlock_mem_positiveEnergy
theorem section43LeftRevBlock_mem_positiveEnergy
theorem section43RightTailBlock_mem_positiveEnergy

theorem section43QTime_leftBlock
theorem section43QTime_leftRevBlock
theorem section43QTime_rightTailBlock
theorem section43QTime_rightTailBlock_zero
theorem section43QSpatial_apply
theorem section43QSpatial_leftBlock_apply
theorem section43QSpatial_leftRevBlock_apply
theorem section43QSpatial_rightTailBlock_apply
```

These lemmas are the component-level chronological bookkeeping for `(4.23)`.
They are still useful for proving which raw block is reversed before
Borchers conjugation and which right block begins at the gap.  They are **not**
the final flat-frequency left factor in the scalar Fourier product: after
physics Fourier transform, Borchers conjugation introduces a negative reversed
left flat frequency, and the implementation must use the shifted
`section43LeftBorchersBlock` from §5.9.2c together with total-momentum support.
The `QSpatial` readout lemmas are needed because the normal form is expressed through
`partialFourierSpatial_timeSliceSchwartz`, whose frozen spatial argument is
the Euclidean-space block `section43QSpatial`.  They are still pure coordinate
lemmas, so they are safe production support.

Production status, 2026-04-14: this component projection packet is now
implemented and exact-checked.  The proof obligations discharged so far are
coordinate/support facts only; no global Wightman-to-OS scalar comparison has
been introduced.

The first implementation-ready scalar consumer of this coordinate package is
the right-tail specialization of Packet H.  It is allowed because it does not
compare Wightman and OS values; it only rewrites an already transformed right
representative on the component map `section43RightTailBlock`.

```lean
theorem
    section43FourierLaplaceRepresentative_rightTailBlock_eq_iterated_descendedPsiZ_of_height
    (d n m : ℕ) [NeZero d]
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (ψ : SchwartzNPoint d (m + 1))
    (hψ : section43FourierLaplaceRepresentative d (m + 1) g ψ)
    (q : NPointDomain d (n + (m + 1)))
    (η : ℝ)
    (hq : q ∈ section43PositiveEnergyRegion d (n + (m + 1)))
    (hη : 0 < η)
    (hgap :
      section43QTime (d := d) (n := n + (m + 1)) q
        (section43TailGapIndex (n := n) (m := m + 1) (Nat.succ_pos m)) =
          2 * Real.pi * η) :
    let qR : NPointDomain d (m + 1) := section43RightTailBlock d n (m + 1) q
    ψ qR =
      -- exactly the RHS of
      -- `section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_height`
      -- with degree `m + 1`, distinguished coordinate `0`,
      -- point `qR`, and height `η`.
      ...
```

Proof transcript:

1. Set
   `qR : NPointDomain d (m + 1) := section43RightTailBlock d n (m + 1) q`.
2. Set
   `hqR := section43RightTailBlock_mem_positiveEnergy (d := d) (n := n) (m := m + 1) hq`.
3. Prove
   `hgapR :
      section43QTime (d := d) (n := m + 1) qR 0 =
          2 * Real.pi * η`
   by rewriting with `section43QTime_rightTailBlock_zero` and `hgap`.
4. Apply
   `section43FourierLaplaceRepresentative_eq_iterated_descendedPsiZ_of_mem_positiveEnergy_of_height`
   with `n := m`, `r := 0`, `q := qR`, `hq := hqR`, and `hqr := hgapR`.
5. Close by `change ψ qR = _; exact ...`, not by broad `simp [qR]`; the
   fully expanded RHS is large enough that broad simplification can hit
   recursion/heartbeat limits.

Production status, 2026-04-14: this right-tail scalar specialization is now
implemented in `Section43OneVariableSlice.lean` and exact-checked.  The
implementation keeps the theorem in the natural `(m + 1)` degree shape to
avoid casts between `m` and `(m - 1) + 1`.

The analogous left-side theorem should not be added yet unless the consumer
actually needs it.  The left side is not the `ψ_Z` gap side; premature
left-side wrappers would add surface area without closing the current seam.

Next non-wrapper theorem after this packet:

```lean
private theorem
    integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_frequencyProjection_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d (m + 1) → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f)
    (hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g) :
    ∀ t : ℝ, 0 < t →
      -- Wightman time-shift functional paired with `𝓕 ψ_{2πit}`
      -- equals the OS off-diagonal spectral Laplace scalar for
      -- `PositiveTimeBorchersSequence.single n f.1 f.2` and
      -- `PositiveTimeBorchersSequence.single (m + 1) g.1 g.2`.
      ...
```

This theorem is the corrected replacement for the old

```lean
integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport
descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport
descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport
```

surface.  The old theorem surface is not acceptable because its `hφf`/`hψg`
hypotheses are only quotient-inclusion hypotheses for the current
`os1TransportComponent`; they do not assert the OS I `(4.19)-(4.20)` transform.

Readiness transcript for the successor-right theorem:

1. Use the successor-right degree `m + 1` in the first implementation.  Only
   after that theorem is proved should an `{m} (hm : 0 < m)` adapter be added,
   by `cases m` and eliminating the zero case.
2. The theorem must construct a concrete normal form `N : ℂ`, not define `N`
   to be either side of the desired equality.  The normal form must be the
   scalar obtained by expanding the Wightman time-shift integral and the OS
   spectral Laplace expression through the same Section-4.3 time/spatial slice
   variables.
3. The right factor of `N` must use
   `section43FourierLaplaceRepresentative_rightTailBlock_eq_iterated_descendedPsiZ_of_height`.
   This supplies the `ψ_Z`/tail-gap side with the central coordinate already
   identified.
4. The left factor of `N` must read the Wightman Borchers reversal through the
   shifted frequency block `section43LeftBorchersBlock`, not through
   `section43LeftBlock` and not through the unshifted
   `section43LeftRevBlock`.
5. The proof may use the coordinate lemmas
   `section43TailGap_succAbove_leftRev`,
   `section43TailGap_succAbove_right`,
   `section43QTime_leftRevBlock`,
   `section43QTime_rightTailBlock_zero`,
   `section43QSpatial_leftRevBlock_apply`, and
   `section43QSpatial_rightTailBlock_apply` to prove the chronological
   reversal algebra, but the final frequency representative argument is the
   total-momentum-shifted `section43LeftBorchersBlock`.
6. No step may rewrite `φ` to `f.1` or `ψ` to `g.1` on
   `section43PositiveEnergyRegion`.  The only allowed use of `hφ_freq` and
   `hψ_freq` is to derive representative predicates for
   `section43FrequencyRepresentative d n φ` and
   `section43FrequencyRepresentative d (m + 1) ψ`, then use
   `section43FourierLaplaceRepresentative_apply` and the Packet-H
   transformed-representative normal forms on those deterministic
   representatives.
7. If the expansion of the Wightman time-shift integral is not exposed by the
   current API, the next production theorem must be the smallest expansion
   lemma for `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` needed
   to produce this concrete `N`.  Do not reintroduce a quotient-slice
   `repr_eq_transport` bridge on the old surface.

Successor-right normal-form refinement, 2026-04-14:

The concrete scalar `N` in the successor-right theorem should not be an
unexplained existential and should not be either side of the target equality.
The current production API already supplies the correct Fourier-side container
for `N`: choose the full flattened Wightman Fourier representative `Tflat`
from the existing boundary-value Fourier-support package, then use

```lean
exists_timeShiftKernel_pairing_fourierTest
```

with

```lean
χ :=
  (SchwartzMap.fourierTransformCLM ℂ)
    (SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I))) ...)
```

to obtain a Schwartz kernel `KψZ_t` satisfying

```lean
(∫ τ : ℝ,
  bvt_W OS lgc (n + (m + 1))
    (φ.conjTensorProduct
      (timeShiftSchwartzNPoint (d := d) τ ψ)) *
  (SchwartzMap.fourierTransformCLM ℂ ψZ_t) τ)
= Tflat KψZ_t
```

and

```lean
∀ ξ,
  KψZ_t ξ =
    ∫ τ : ℝ,
      timeShiftFlatOrbit (d := d) φ ψ τ ξ *
        (SchwartzMap.fourierTransformCLM ℂ ψZ_t) τ.
```

Thus the Lean normal form should be

```lean
let N : ℂ := Tflat KψZ_t
```

but only after the proof has introduced `Tflat`, `hTflat_bv`, `KψZ_t`,
`hKψZ_eval`, and `hKψZ_pair` explicitly.  This is not a wrapper: `KψZ_t` has
the displayed pointwise formula and is the actual OS I `(4.23)` Fourier-side
kernel after the time-shift/Fubini expansion.

The remaining non-formal theorem is then a pointwise comparison on the full
Wightman spectral region, not a direct scalar comparison and not merely a
dual-cone comparison:

```lean
private theorem
    section43_timeShiftKernel_psiZ_eq_os24Kernel_on_spectralRegion_of_frequencyProjection_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f)
    (hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g)
    {t : ℝ} (ht : 0 < t)
    (KψZ_t : SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ)
    (hKψZ_eval :
      ∀ ξ,
        KψZ_t ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ *
              (SchwartzMap.fourierTransformCLM ℂ
                (SCV.schwartzPsiZ
                  (((2 * Real.pi : ℂ) * (t * Complex.I))) ...)) τ) :
    Set.EqOn
      (fun ξ => KψZ_t ξ)
      (fun ξ =>
        -- OS I `(4.24)` product kernel in Lean coordinates:
        -- left factor:
        --   star ((section43FrequencyRepresentative d n φ)
        --     (section43LeftBorchersBlock ... qξ))
        -- right factor:
        --   (section43FrequencyRepresentative d (m + 1) ψ)
        --     (section43RightTailBlock ... qξ)
        -- with tail-gap spectral height `ηξ`, while the external `t`
        -- appears only as the Laplace damping from `ψZ_t`.
        section43OS24Kernel_succRight d n m φ ψ f g t ξ)
      (section43WightmanSpectralRegion d (n + (m + 1)))
```

The displayed `section43OS24Kernel_succRight` is not allowed to be a production
placeholder.  Before this theorem is implemented, the proof docs must replace
it by a visible expression.  That expression has three required factors:

1. A left Borchers-reversed frequency factor
   `star ((section43FrequencyRepresentative (d := d) n φ)
      (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q))`.
   The allowed route to the OS I transform of `f` is first
   `section43FrequencyRepresentative_is_fourierLaplaceRepresentative`
   from `hφ_freq`, then `section43FourierLaplaceRepresentative_apply` at
   the shifted `section43LeftBorchersBlock`.  The proof must use total
   momentum to identify this shifted block with the negative reversed left
   flat frequency.
2. A right-tail transformed factor
   `(section43FrequencyRepresentative (d := d) (m + 1) ψ)
      (section43RightTailBlock d n (m + 1) q)`, rewritten by first deriving
   the representative predicate from `hψ_freq`.  For the scalar OS I
   `(4.24)` theorem this factor is rewritten by the basic
   `section43FourierLaplaceRepresentative_apply` theorem, as made explicit in
   §5.9.2d.  The stronger
   `section43FourierLaplaceRepresentative_rightTailBlock_eq_iterated_descendedPsiZ_of_height`
   theorem belongs only to the later descended-`ψ_Z`/hPsi consumer.
   The height is **not** the external positive time `t`.  It is the spectral
   tail-gap height read from the flattened dual-cone frequency.  Define the
   phase coefficient

```lean
let lamξ : ℝ :=
  ∑ i,
    (((OSReconstruction.castFinCLE
        (Nat.add_mul n (m + 1) (d + 1)).symm)
      (OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := (m + 1) * (d + 1))
        (flatTimeShiftDirection d (m + 1)))) i) * ξ i
let ηξ : ℝ := -lamξ / (2 * Real.pi)
```

   On the dual cone, `0 ≤ ηξ` is supplied by the same sign theorem shape as
   `horizontalPaley_frequency_nonneg_of_mem_dualCone`, specialized to right
   degree `m + 1`.  If Packet H needs strict positivity, split the zero-height
   case separately: when `ηξ = 0`, the one-sided `ψ_Z` factor is the boundary
   value at the edge and must be handled by the quotient/support vanishing
   theorem, not by pretending `0 < ηξ`.

   In the positive-height branch the Packet-H height proof is

```lean
section43QTime (d := d) (n := n + (m + 1)) q
  (section43TailGapIndex (n := n) (m := m + 1) (Nat.succ_pos m))
    = 2 * Real.pi * ηξ
```

   and the final `ψ_Z` argument normalization is exactly
   `section43QTime_complexPsiArg_eq_of_height` followed by
   `section43_realHeight_complexPsiArg_eq`.  The external `t` enters later,
   after `hKψZ_eval` and `timeShiftFlatOrbit_apply_phase`, through

```lean
SCV.psiZ_eq_exp_of_nonneg
  -- gives
  ψZ_t ηξ = Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ))
```

   This correction is essential: identifying the tail-gap spectral height with
   the external semigroup time `t` would reintroduce the old oscillatory-vs-
   Laplace mismatch under a new name.
3. The full flattened Wightman Fourier variable `ξ` converted to the Section
   4.3 positive-energy coordinate `q`.  This conversion must be written as a
   named coordinate theorem before the scalar proof is attempted; it is the
   only remaining bridge between the `timeShiftFlatOrbit` flat kernel and the
   `section43LeftBorchersBlock`/`section43RightTailBlock` coordinate API.

Concrete flat-frequency to Section-4.3 coordinate conversion:

The conversion is **not** raw unflattening of `ξ`.  The cone
`ForwardConeAbs d N` is written in absolute coordinates, while OS I `(4.24)`
uses cumulative tail momenta dual to the difference variables.  Therefore the
Section-4.3 momentum point associated to a flat frequency is the same
cumulative-tail equivalence used in the frequency-projection packet:

```lean
abbrev section43CumulativeTailMomentum
    (d N : ℕ) [NeZero d]
    (ξ : Fin (N * (d + 1)) → ℝ) : NPointDomain d N :=
  section43CumulativeTailMomentumCLE d N ξ
```

The first support theorem for this definition is:

```lean
theorem section43CumulativeTailMomentum_mem_positiveEnergy_of_mem_dualCone
    (d N : ℕ) [NeZero d]
    {ξ : Fin (N * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)) :
    section43CumulativeTailMomentum d N ξ ∈
      section43PositiveEnergyRegion d N
```

Proof transcript: unfold the abbreviation and use
`section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone`.
The full triangular summation-by-parts proof belongs to that theorem; do not
duplicate it with a separate `flatTailTimeShiftDirection` route.

The second support theorem identifies the exact spectral height used by the
right-tail Packet-H theorem:

```lean
theorem section43CumulativeTailMomentum_tailGap_height
    (d n m : ℕ) [NeZero d]
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) :
    let qξ :=
      section43CumulativeTailMomentum d (n + (m + 1)) ξ
    let lamξ : ℝ :=
      ∑ i,
        (((OSReconstruction.castFinCLE
            (Nat.add_mul n (m + 1) (d + 1)).symm)
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := (m + 1) * (d + 1))
            (flatTimeShiftDirection d (m + 1)))) i) * ξ i
    section43QTime (d := d) (n := n + (m + 1)) qξ
        (section43TailGapIndex (n := n) (m := m + 1) (Nat.succ_pos m))
      =
    -lamξ
```

Then, with `ηξ := -lamξ / (2 * Real.pi)`, the Packet-H height equation is a
one-line normalization:

```lean
section43QTime ... qξ (section43TailGapIndex ...) = 2 * Real.pi * ηξ
```

using `field_simp [Real.two_pi_ne_zero]` or the existing `Real.two_pi_pos`
nonzero proof.  This theorem is the precise replacement for the earlier
ambiguous phrase "the tail-gap coordinate has height `2πt`"; the height is
frequency-dependent, while `t` is the external Laplace time.

The visible OS I `(4.24)` product kernel should be stated using this `qξ`,
but only as the **target scalar normal form after the OS I interchange has
been proved**.  It is not a pointwise simplification of the flattened
Wightman Fourier base.  A first draft may be kept locally in the proof docs:

```lean
def section43OS24Kernel_succRight_visible
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (t : ℝ)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) : ℂ :=
  let qξ := section43CumulativeTailMomentum d (n + (m + 1)) ξ
  let lamξ : ℝ := -- the `timeShiftFlatOrbit_apply_phase` coefficient
    ∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n (m + 1) (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := (m + 1) * (d + 1))
          (flatTimeShiftDirection d (m + 1)))) i) * ξ i
  let ηξ : ℝ := -lamξ / (2 * Real.pi)
  Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) *
    -- the OS I `(4.24)` product of transformed representatives,
    -- after the spatial Fourier/product expansion has been proved:
    (star
        ((section43FrequencyRepresentative (d := d) n φ)
          (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
      (section43FrequencyRepresentative (d := d) (m + 1) ψ)
        (section43RightTailBlock d n (m + 1) qξ))
```

Important correction, 2026-04-14: the following pointwise theorem shape is
**not** a valid Lean target under the current hypotheses:

```lean
theorem timeShiftFlatOrbit_psiZ_kernel_eq_section43OS24Kernel_succRight_visible
    ...
```

Reason: after `timeShiftFlatOrbit_apply_phase`, the remaining factor is

```lean
let base : ℂ :=
  physicsFourierFlatCLM
    (OSReconstruction.reindexSchwartzFin
      (Nat.add_mul n (m + 1) (d + 1)).symm
      (((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
        (flattenSchwartzNPoint (d := d) ψ)))) ξ
```

The predicate

```lean
section43FourierLaplaceRepresentative d n f φ
```

only says that `φ q` agrees with the OS I `(4.19)-(4.20)` integral when
`q ∈ section43PositiveEnergyRegion d n`.  It does not determine
`physicsFourierFlatCLM φ` at a dual-cone frequency, because the flat Fourier
integral depends on the full ambient Schwartz extension of `φ`, not only on
its positive-energy restriction.  Therefore no proof may replace the displayed
`base` by

```lean
star
  ((section43FrequencyRepresentative (d := d) n φ)
    (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
  (section43FrequencyRepresentative (d := d) (m + 1) ψ)
    (section43RightTailBlock d n (m + 1) qξ)
```

by `simp`, by `section43FourierLaplaceRepresentative_apply`, or by the
half-space quotient `section43PositiveEnergyQuotientMap`.  The support theorem
for `Tflat` only says that `Tflat` cannot distinguish two **frequency-side**
kernels that agree on its Fourier-support set.  In the old dual-cone-only
packet this was `tflat_pairing_eq_of_eqOn_dualCone`; in the corrected scalar
packet it must be the general `HasFourierSupportIn` EqOn theorem on
`section43WightmanSpectralRegion`.

It does not say that pointwise equality of ambient representatives on
`section43PositiveEnergyRegion` implies equality of their flat Fourier
transforms on `DualConeFlat` or on `section43WightmanSpectralRegion`.

There is a second, stronger consequence: the global scalar theorem is also
false if it assumes only `section43FourierLaplaceRepresentative`.  If
`δφ : SchwartzNPoint d n` vanishes on `section43PositiveEnergyRegion d n`,
then `φ + δφ` satisfies the same half-space apply predicate as `φ`, but the
Wightman scalar

```lean
bvt_W OS lgc (n + (m + 1))
  ((φ + δφ).conjTensorProduct
    (timeShiftSchwartzNPoint (d := d) τ ψ))
```

need not agree with the scalar for `φ`: the boundary-value distribution is
not known to factor through the half-space quotient of its ambient test
argument.  Thus Packet H's point-evaluation predicate is sufficient for the
right-tail transformed factor, but it is not sufficient for the global
Wightman/OS scalar comparison.

The global theorem must therefore avoid arbitrary ambient transformed
representatives.  There are only two legal ways forward:

1. prove a genuine full-Schwartz representative section for the paper's
   half-space transform, and state every scalar theorem for that fixed chosen
   section; or
2. stay on the Option-beta half-space quotient surface and prove the Wightman
   scalar descends through the **frequency-side** Section-4.3 quotient.

The current route must use the second option.  This is forced by the earlier
codomain decision in §5.9.0 and by the paper's Lemma 8.2: Lemma 8.2 gives a
Laplace transform into the half-line/half-space Schwartz target with dense
range and zero kernel.  It does not provide a canonical full ambient Schwartz
extension.  Therefore the following object is **not** an endorsed next
production target:

```lean
noncomputable def section43FourierLaplaceTransformAmbientCLM
    (d n : ℕ) [NeZero d] :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ] SchwartzNPoint d n
```

Such an ambient CLM may only be introduced later as an auxiliary section if
the implementation also supplies:

```lean
noncomputable def section43HalfSpaceRepresentativeSection
    (d n : ℕ) [NeZero d] :
    Section43PositiveEnergyComponent (d := d) n →L[ℂ] SchwartzNPoint d n

theorem section43HalfSpaceRepresentativeSection_right_inverse
    (d n : ℕ) [NeZero d] (u : Section43PositiveEnergyComponent (d := d) n) :
    section43PositiveEnergyQuotientMap (d := d) n
      (section43HalfSpaceRepresentativeSection d n u) = u
```

and every later scalar theorem must prove independence from that section, or
use it only behind a theorem whose statement is quotient-valued.  Until those
facts exist, the ambient-CLM route is a proof-doc regression to the retracted
full-Schwartz/Seeley-extension branch.

The corrected production object is the frequency-side quotient projection of a
Wightman test:

```lean
noncomputable def section43CumulativeTailMomentumCLE
    (d n : ℕ) [NeZero d] :
    (Fin (n * (d + 1)) → ℝ) ≃L[ℝ] NPointDomain d n

noncomputable def section43FrequencyRepresentative
    (d n : ℕ) [NeZero d] :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43CumulativeTailMomentumCLE d n).symm).comp
    ((physicsFourierFlatCLM : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ).comp
      (flattenSchwartzNPoint (d := d)))

noncomputable def section43FrequencyProjection
    (d n : ℕ) [NeZero d] :
    SchwartzNPoint d n →L[ℂ] Section43PositiveEnergyComponent (d := d) n :=
  (section43PositiveEnergyQuotientMap (d := d) n).comp
    (section43FrequencyRepresentative (d := d) n)
```

The deterministic representative is the object that may be evaluated in
scalar kernels.  The quotient projection supplies a pointwise transformed
representative only through the following apply theorem:

```lean
theorem section43FrequencyRepresentative_is_fourierLaplaceRepresentative
    (d n : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f) :
    section43FourierLaplaceRepresentative d n f
      (section43FrequencyRepresentative (d := d) n φ)
```

Proof transcript:

1. Unfold `section43FrequencyProjection`.
2. Use the defining theorem for
   `section43FourierLaplaceTransformComponent`, namely that it is the
   positive-energy quotient class of the OS I `(4.19)-(4.20)` transform
   representative.
3. Convert quotient equality to `EqOn section43PositiveEnergyRegion` using
   `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`.
4. Repackage exactly as `section43FourierLaplaceRepresentative`.

The descent theorem that makes this projection legitimate is:

```lean
private theorem bvt_W_eq_of_section43FrequencyProjection_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {N : ℕ}
    (φ ψ : SchwartzNPoint d N)
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportInDualCone
        ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) Tflat)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc N (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat))
    (hproj :
      section43FrequencyProjection (d := d) N φ =
        section43FrequencyProjection (d := d) N ψ) :
    bvt_W OS lgc N φ = bvt_W OS lgc N ψ
```

Proof transcript:

1. Rewrite the two `bvt_W` values using `hTflat_bv` at
   `flattenSchwartzNPoint φ` and `flattenSchwartzNPoint ψ`.
2. Convert `hproj` through
   `eqOn_region_of_section43PositiveEnergyQuotientMap_eq` to equality of the
   two physics-Fourier-side tests on `section43PositiveEnergyRegion`.
3. Use the cumulative-tail cone-support theorem

```lean
@[simp] theorem section43CumulativeTailMomentumCLE_apply
    (ξ : Fin (N * (d + 1)) → ℝ) (j : Fin N) (μ : Fin (d + 1)) :
    section43CumulativeTailMomentumCLE d N ξ j μ =
      if μ = 0 then
        ∑ k : Fin N,
          if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0
      else
        -(1 / (2 * Real.pi)) *
          ∑ k : Fin N,
            if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0

@[simp] theorem section43CumulativeTailMomentumCLE_symm_apply
    (q : NPointDomain d N) (k : Fin N) (μ : Fin (d + 1)) :
    (section43CumulativeTailMomentumCLE d N).symm q (finProdFinEquiv (k, μ)) =
      if μ = 0 then
        q k μ -
          if h : k.val + 1 < N then q ⟨k.val + 1, h⟩ μ else 0
      else
        -(2 * Real.pi) *
          (q k μ -
            if h : k.val + 1 < N then q ⟨k.val + 1, h⟩ μ else 0)

theorem section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone
    {ξ : Fin (N * (d + 1)) → ℝ}
    (hξ : ξ ∈
      DualConeFlat ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)) :
    section43CumulativeTailMomentumCLE d N ξ ∈
      section43PositiveEnergyRegion d N

private theorem physicsFourierFlat_eqOn_dualCone_of_section43FrequencyProjection_eq
    {N : ℕ}
    (φ ψ : SchwartzNPoint d N)
    (hproj :
      section43FrequencyProjection (d := d) N φ =
        section43FrequencyProjection (d := d) N ψ) :
    Set.EqOn
      (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) φ) :
        (Fin (N * (d + 1)) → ℝ) → ℂ)
      (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) ψ) :
        (Fin (N * (d + 1)) → ℝ) → ℂ)
      (DualConeFlat ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
```

   The spatial scaling in the cumulative-tail map is intentional.  Time
   coordinates are Laplace variables, so no `2π` appears in the time exponent.
   Spatial coordinates are Mathlib Fourier variables inside
   `partialFourierSpatial_fun`, whose kernel is `𝐞 (-(inner ℝ _ _))`.
   Matching the physics phase
   `Complex.exp (Complex.I * ∑ xᵢ ξᵢ)` requires
   `q_spatial = -ξ_spatial / (2 * Real.pi)` after cumulative-tail summation.
   Do not implement the unscaled all-components cumulative map; it would make
   the one-factor bridge in S5 false in spatial directions.

   Together with the definition of `section43FrequencyProjection`, this turns
   quotient equality of cumulative-tail Fourier-side tests into `EqOn` of the
   flat tests on `DualConeFlat`.  The mathematical content is that the
   cumulative tail momenta of every spectral-support frequency lie in the
   Section-4.3 positive-energy half-space.
4. Apply `tflat_pairing_eq_of_eqOn_dualCone`.
5. Close by the two `hTflat_bv` rewrites.

Proof transcript for
`section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone`:

1. Introduce

```lean
let qξ : NPointDomain d N := section43CumulativeTailMomentumCLE d N ξ
```

and prove the summation-by-parts identity

```lean
have hpair_diff :
    ∀ δ : NPointDomain d N,
      (∑ i : Fin (N * (d + 1)),
          flattenCLEquivReal N (d + 1)
            ((section43DiffCoordRealCLE d N).symm δ) i * ξ i)
        =
      (∑ k : Fin N, δ k 0 * qξ k 0) -
        (2 * Real.pi) *
          ∑ k : Fin N, ∑ μ : Fin d,
            δ k (Fin.succ μ) * qξ k (Fin.succ μ)
```

This is the triangular identity behind cumulative tail momenta:
`y_k = Σ_{l≤k} δ_l`, so
`Σ_k y_k ξ_k = Σ_l δ_l (Σ_{k≥l} ξ_k)`.  The time coordinates use the raw
tail sum; spatial coordinates use the scaled convention
`q_spatial = -tail_spatial / (2 * Real.pi)`, hence the displayed
`-(2 * Real.pi)` factor.

2. To prove `0 ≤ qξ j 0`, argue by contradiction.  Assume `hqneg :
   qξ j 0 < 0`.
3. Let `e0 : Fin (d + 1) → ℝ` be the time-axis vector
   `fun μ => if μ = 0 then 1 else 0`.  It lies in the open forward cone after
   multiplying by any positive scalar.
4. For `R > 0`, define a difference-coordinate point

```lean
def δR (R : ℝ) : NPointDomain d N :=
  fun k μ =>
    (if k = j then R else 1) * e0 μ
```

Every `δR k` lies in `InOpenForwardCone d` when `0 < R`, hence
`yR := (section43DiffCoordRealCLE d N).symm δR ∈ ForwardConeAbs d N`.
5. Apply `hξ` to `flattenCLEquivReal N (d + 1) yR`.  Via `hpair_diff`, obtain

```lean
0 ≤ R * qξ j 0 + ∑ k : Fin N, if k = j then 0 else qξ k 0
```

6. Since `qξ j 0 < 0`, choose `R` larger than
   `((∑ k, if k = j then 0 else qξ k 0) + 1) / (-qξ j 0)`.  Linear
   arithmetic contradicts the displayed inequality.
7. Therefore `0 ≤ qξ j 0`.  Since `j` was arbitrary, this is exactly
   `qξ ∈ section43PositiveEnergyRegion d N`.

Proof transcript for
`physicsFourierFlat_eqOn_dualCone_of_section43FrequencyProjection_eq`:

1. Convert `hproj` to an equality of ordinary quotient maps:

```lean
have hq :
    section43PositiveEnergyQuotientMap (d := d) N
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (section43CumulativeTailMomentumCLE d N).symm
          (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) φ))) =
      section43PositiveEnergyQuotientMap (d := d) N
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (section43CumulativeTailMomentumCLE d N).symm
          (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) ψ))) := by
  simpa [section43FrequencyProjection] using hproj
```

2. Set

```lean
have hEqRegion :=
  eqOn_region_of_section43PositiveEnergyQuotientMap_eq (d := d) (n := N) hq
```

3. For `ξ` in the dual cone, put
   `qξ := section43CumulativeTailMomentumCLE d N ξ`.  The theorem
   `section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone`
   gives `qξ ∈ section43PositiveEnergyRegion d N`.
4. The desired pointwise equality is exactly `hEqRegion` at this `qξ`, after
   unfolding `SchwartzMap.compCLMOfContinuousLinearEquiv_apply`,
   `section43CumulativeTailMomentumCLE_apply`, and the inverse theorem
   `section43CumulativeTailMomentumCLE_symm_apply`.
5. The only algebraic fact needed at the last line is
   `(section43CumulativeTailMomentumCLE d N).symm
      (section43CumulativeTailMomentumCLE d N ξ) = ξ`, supplied by the
   continuous-linear equivalence.

Proof transcript for `bvt_W_eq_of_section43FrequencyProjection_eq`:

```lean
have hEqDual :=
  physicsFourierFlat_eqOn_dualCone_of_section43FrequencyProjection_eq
    (d := d) (N := N) φ ψ hproj
have hφ_flat :
    unflattenSchwartzNPoint (d := d)
        (flattenSchwartzNPoint (d := d) φ) = φ := by
  ext x
  simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
have hψ_flat :
    unflattenSchwartzNPoint (d := d)
        (flattenSchwartzNPoint (d := d) ψ) = ψ := by
  ext x
  simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
calc
  bvt_W OS lgc N φ
      = bvt_W OS lgc N
          (unflattenSchwartzNPoint (d := d)
            (flattenSchwartzNPoint (d := d) φ)) := by
        rw [hφ_flat]
  _ = Tflat (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) φ)) := by
        simpa using hTflat_bv (flattenSchwartzNPoint (d := d) φ)
  _ = Tflat (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) ψ)) := by
        exact tflat_pairing_eq_of_eqOn_dualCone
          (S := (flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
          Tflat hTflat_supp
          (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) φ))
          (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) ψ))
          hEqDual
  _ = bvt_W OS lgc N
          (unflattenSchwartzNPoint (d := d)
            (flattenSchwartzNPoint (d := d) ψ)) := by
        simpa using (hTflat_bv (flattenSchwartzNPoint (d := d) ψ)).symm
  _ = bvt_W OS lgc N ψ := by
        rw [hψ_flat]
```

Immediate implementation order for this support packet:

1. Add `section43CumulativeTailMomentumCLE`,
   `section43CumulativeTailMomentumCLE_apply`,
   `section43CumulativeTailMomentumCLE_symm_apply`, and
   `section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone` to
   `Section43FourierLaplaceTransform.lean`.  These are pure coordinate/cone
   facts and must not import `OSToWightmanPositivity.lean`.

   Production status, 2026-04-14: the cumulative-tail equivalence, raw
   cumulative-tail equivalence, finite reversal sum helper, and raw/scaled
   apply/symm simp lemmas are implemented in
   `Section43FourierLaplaceTransform.lean` and exact-checked.  The cone-support
   theorem
   `section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone` is
   also implemented there and exact-checked.  The proof uses the documented
   time-axis large-`R` contradiction, supported by finite prefix/tail
   summation-by-parts lemmas and the time-axis `ForwardConeAbs` witness.
2. Add `section43FrequencyProjection` to the Section-4.3 codomain/transform
   layer after the cumulative-tail equivalence is available.

   Production status, 2026-04-14: `section43FrequencyRepresentative` and
   `section43FrequencyProjection` are implemented in
   `Section43FourierLaplaceTransform.lean` and exact-checked.
3. Add
   `physicsFourierFlat_eqOn_dualCone_of_section43FrequencyProjection_eq` next
   to the projection definition; it is the local bridge from quotient equality
   to `EqOn` on the spectral support cone.

   Production status, 2026-04-14:
   `physicsFourierFlat_eqOn_dualCone_of_section43FrequencyProjection_eq` is
   implemented in `Section43FourierLaplaceTransform.lean` and exact-checked.
   It uses
   `section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone` to
   evaluate quotient equality at cumulative-tail momenta coming from the
   spectral dual cone.
4. Add `bvt_W_eq_of_section43FrequencyProjection_eq` only in a file that
   already has access to `bvt_W`, `hTflat_bv`, and the support theorem
   `tflat_pairing_eq_of_eqOn_dualCone`; this is likely
   `OSToWightmanPositivity.lean` or a small imported support file.

   Production status, 2026-04-14:
   `bvt_W_eq_of_section43FrequencyProjection_eq` is implemented in the small
   support file `Section43WightmanDescent.lean` and exact-checked.  The proof
   consumes
   `physicsFourierFlat_eqOn_dualCone_of_section43FrequencyProjection_eq` and
   `tflat_pairing_eq_of_eqOn_dualCone`, then closes by the two
   `hTflat_bv` rewrites through `flattenSchwartzNPoint`/`unflattenSchwartzNPoint`.
5. Only after these four declarations compile should any active hPsi or
   Lemma-4.2 theorem surface be migrated from raw
   `section43PositiveEnergyQuotientMap` hypotheses to
   `section43FrequencyProjection` hypotheses.

### 5.9.2c. Left Borchers factor and total-momentum support

The frequency-projection descent packet above is enough to make a single
`bvt_W` value depend only on the transformed Section-4.3 quotient class.  It
is **not** by itself enough for the OS I scalar product in `(4.23) -> (4.24)`.
The scalar proof has an additional left-factor normalization coming from
Borchers conjugation and chronological reversal.

For

```lean
N := n + (m + 1)
qξ := section43CumulativeTailMomentumCLE d N ξ
```

the right component of the product is genuinely the right tail of `qξ`.
However the left Borchers-conjugate component is not
`section43LeftRevBlock ... qξ`.  The physics Fourier transform of a
chronologically reversed conjugate test evaluates the original left test at
the **negative reversed flat frequency**.  In cumulative-tail variables this
negative-reversed left frequency is recovered from `qξ` only after using
total-momentum conservation.

The one-particle-left/one-particle-right example shows the issue.  Dual-cone
support gives

```text
ξ₁ ≥ 0,     ξ₀ + ξ₁ ≥ 0,
```

but the left conjugate factor needs `-ξ₀ ≥ 0`.  This follows from
`ξ₀ + ξ₁ = 0`, not from the dual cone alone.  Therefore the scalar theorem
must carry the Wightman translation-invariance support as well as the spectral
dual-cone support.

The Lean support set must be explicit:

```lean
def section43TotalMomentumFlat
    (d N : ℕ) [NeZero d]
    (ξ : Fin (N * (d + 1)) → ℝ) : Fin (d + 1) → ℝ :=
  fun μ => ∑ k : Fin N, ξ (finProdFinEquiv (k, μ))

def section43TotalMomentumZeroFlat
    (d N : ℕ) [NeZero d] :
    Set (Fin (N * (d + 1)) → ℝ) :=
  {ξ | section43TotalMomentumFlat d N ξ = 0}

def section43WightmanSpectralRegion
    (d N : ℕ) [NeZero d] :
    Set (Fin (N * (d + 1)) → ℝ) :=
  DualConeFlat ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) ∩
    section43TotalMomentumZeroFlat d N
```

The distribution package used in the scalar theorem must provide support in
`section43WightmanSpectralRegion`, not only in the dual cone:

```lean
theorem bvt_W_flattened_distribution_hasFourierSupportIn_wightmanSpectralRegion
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (N : ℕ) :
    ∃ Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
      HasFourierSupportIn (section43WightmanSpectralRegion d N) Tflat ∧
      (∀ φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc N (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat))
```

This theorem is obtained by combining the existing spectral-condition flat
dual-cone support with translation invariance of `bvt_W` (the production
theorem surface includes `bvt_F_translationInvariant`).  If this combined
support theorem is not available, it is the next implementation target before
the scalar interchange theorem; it cannot be hidden behind an arbitrary
`hTflat_supp`.

The implementation of the combined support theorem should be factored as a
general Fourier-support lemma plus a Wightman specialization.

First define the diagonal translation direction and its pairing with total
momentum:

```lean
def section43DiagonalTranslationFlat
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ) : Fin (N * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i
    a p.2

theorem section43DiagonalTranslationFlat_pair_eq_totalMomentum
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    (∑ i : Fin (N * (d + 1)),
        section43DiagonalTranslationFlat d N a i * ξ i)
      =
    ∑ μ : Fin (d + 1),
      a μ * section43TotalMomentumFlat d N ξ μ
```

Proof transcript: unfold both definitions and rewrite the flat sum through
`finProdFinEquiv`; close with `Finset.sum_sigma'`/`Fintype.sum_prod_type` style
sum reindexing and commutativity of multiplication.

Production status, 2026-04-14: `section43TotalMomentumFlat`,
`section43TotalMomentumZeroFlat`, `section43WightmanSpectralRegion`,
`section43DiagonalTranslationFlat`, and
`section43DiagonalTranslationFlat_pair_eq_totalMomentum` are implemented in
`Section43FourierLaplaceTransform.lean` and exact-checked.

Production status, 2026-04-15: the total-momentum coordinate layer has been
extended with

```lean
section43TotalMomentumComponentCLM
section43TotalMomentumPairingCLM
section43DiagonalTranslationFlat_complex_pair_eq_totalMomentum
```

in `Section43FourierLaplaceTransform.lean`.  These are the CLM and complex
pairing forms used by the phase multiplier and exact-check with the support
file.

The real-space translation invariance of `bvt_W` gives a flat test theorem:

```lean
theorem bvt_W_flat_diagonalTranslate_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (N : ℕ)
    (a : Fin (d + 1) → ℝ)
    (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) :
    bvt_W OS lgc N
        (unflattenSchwartzNPoint (d := d)
          (SCV.translateSchwartz
            (section43DiagonalTranslationFlat d N a) φflat))
      =
    bvt_W OS lgc N
        (unflattenSchwartzNPoint (d := d) φflat)
```

Proof transcript:

1. Apply `bvt_translation_invariant (d := d) OS lgc`.
2. Use

```lean
unflattenSchwartzNPoint (d := d)
  (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat) x
  =
unflattenSchwartzNPoint (d := d) φflat (fun j μ => x j μ + a μ)
```

   by unfolding `unflattenSchwartzNPoint`, `SCV.translateSchwartz_apply`,
   `section43DiagonalTranslationFlat`, and `flattenCLEquivReal_apply`.
3. The sign matches `IsTranslationInvariantWeak`, whose hypothesis is exactly
   `g x = f (fun i => x i + a)`.

Production status, 2026-04-15: the coordinate bridge

```lean
unflattenSchwartzNPoint_translate_section43DiagonalTranslationFlat
```

and the theorem

```lean
bvt_W_flat_diagonalTranslate_eq
```

are implemented in `Section43WightmanDescent.lean` and exact-check.

The Fourier transform turns this diagonal translation into total-momentum
phase multiplication:

```lean
noncomputable def section43TotalMomentumPhaseCLM
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ) :
    SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun ξ =>
      Complex.exp
        (-(Complex.I *
          ∑ μ : Fin (d + 1),
            (a μ : ℂ) * (section43TotalMomentumFlat d N ξ μ : ℂ))))
    -- proof that the bounded smooth linear phase has temperate growth
    section43TotalMomentumPhase_hasTemperateGrowth

theorem physicsFourierFlatCLM_diagonalTranslate_apply
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    physicsFourierFlatCLM
        (SCV.translateSchwartz
          (section43DiagonalTranslationFlat d N a) φflat) ξ
      =
    section43TotalMomentumPhaseCLM d N a
      (physicsFourierFlatCLM φflat) ξ
```

Proof transcript: apply the existing
`physicsFourierFlatCLM_translateSchwartz_apply` theorem and rewrite its flat
pairing with `section43DiagonalTranslationFlat_pair_eq_totalMomentum`.

Production status, 2026-04-15: this layer is implemented as

```lean
section43_physicsFourierFlatCLM_translateSchwartz_apply
physicsFourierFlatCLM_diagonalTranslate_apply
section43_realOscillatoryPhase_hasTemperateGrowth
section43TotalMomentumPhase_hasTemperateGrowth
section43TotalMomentumPhaseCLM
physicsFourierFlatCLM_diagonalTranslate_eq_phaseCLM
```

in `Section43FourierLaplaceTransform.lean`.  The phase multiplier is packaged
as an honest `SchwartzMap.smulLeftCLM`; its temperate-growth proof composes
the one-variable bounded oscillatory phase with
`section43TotalMomentumPairingCLM`.

Next expose the Fourier transform as a continuous linear equivalence.  The
current production surface has `physicsFourierFlatCLM` as a CLM; the support
proof needs a range theorem:

```lean
noncomputable def physicsFourierFlatCLE (m : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ ≃L[ℂ] SchwartzMap (Fin m → ℝ) ℂ

@[simp] theorem physicsFourierFlatCLE_toContinuousLinearMap
    (m : ℕ) :
    (physicsFourierFlatCLE m).toContinuousLinearMap =
      (physicsFourierFlatCLM :
        SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
          SchwartzMap (Fin m → ℝ) ℂ)

theorem physicsFourierFlatCLM_surjective (m : ℕ) :
    Function.Surjective
      (physicsFourierFlatCLM :
        SchwartzMap (Fin m → ℝ) ℂ →
          SchwartzMap (Fin m → ℝ) ℂ)
```

Proof transcript: package Mathlib's Schwartz Fourier-transform equivalence,
the transported `inverseFourierFlatCLM`, and the scaling equivalence already
used in `physicsFourierFlatCLM`.  This is pure Fourier-analysis
infrastructure and should live near `physicsFourierFlatCLM`, not in the
Wightman files.

Production status, 2026-04-15: the needed theorem

```lean
physicsFourierFlatCLM_surjective
```

is implemented in `Section43FourierLaplaceTransform.lean`.  The proof names
the inverse scaling, Euclidean transport, and Mathlib Fourier-inversion steps
explicitly, avoiding reliance on a fragile terminal `simp`.

Now derive phase invariance of the chosen `Tflat`:

```lean
theorem tflat_totalMomentumPhase_invariant_of_bvt_W_translationInvariant
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (N : ℕ)
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc N (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∀ (a : Fin (d + 1) → ℝ)
      (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
      Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K
```

Proof transcript:

1. Use `physicsFourierFlatCLM_surjective` to choose `φflat` with
   `physicsFourierFlatCLM φflat = K`.
2. Rewrite the left side using
   `physicsFourierFlatCLM_diagonalTranslate_apply` in reverse.
3. Rewrite both sides with `hTflat_bv`.
4. Apply `bvt_W_flat_diagonalTranslate_eq`.

Production status, 2026-04-15:

```lean
tflat_totalMomentumPhase_invariant_of_bvt_W_translationInvariant
```

is implemented in `Section43WightmanDescent.lean` and exact-checks after a
narrow rebuild of `Section43FourierLaplaceTransform` to refresh the local
`.olean`.

Finally separate total-momentum support into two steps:

1. Coordinate annihilation from phase invariance.  This is implemented in
   production as

```lean
theorem tflat_totalMomentumCoordMultiplier_eq_zero_of_phaseInvariant
    (d : ℕ) [NeZero d] {N : ℕ}
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hphase :
      ∀ (a : Fin (d + 1) → ℝ)
        (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
        Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K) :
    (μ : Fin (d + 1))
    (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) :
    Tflat (section43TotalMomentumCoordMultiplierCLM d N μ K) = 0
```

2. Compact hyperplane division plus truncation.  This has now been implemented
   in production and produces

```lean
theorem hasFourierSupportIn_totalMomentumZero_of_phase_invariant
    (d N : ℕ) [NeZero d]
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hphase :
      ∀ (a : Fin (d + 1) → ℝ)
        (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
        Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K) :
    HasFourierSupportIn (section43TotalMomentumZeroFlat d N) Tflat
```

Do **not** revive the older direct phase-differentiation route
`tflat_annihilates_totalMomentumCoord_of_phase_invariant`.  That sketch asked
Lean for an unstructured Frechet derivative of the CLM-valued map
`a ↦ section43TotalMomentumPhaseCLM d N a`; the production proof deliberately
avoids it by transporting the already-proved real-translation difference
quotient through the physics Fourier transform.

For fixed `μ`, define the one-parameter phase multiplier

```lean
noncomputable def section43TotalMomentumBasisPhaseCLM
    (d N : ℕ) [NeZero d] (μ : Fin (d + 1)) (t : ℝ) :
    SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ :=
  section43TotalMomentumPhaseCLM d N (fun ν => if ν = μ then t else 0)

noncomputable def section43TotalMomentumCoordMultiplierCLM
    (d N : ℕ) [NeZero d] (μ : Fin (d + 1)) :
    SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun ξ => (section43TotalMomentumFlat d N ξ μ : ℂ))
```

Production status, 2026-04-15: the small API

```lean
section43TotalMomentumCoord_hasTemperateGrowth
section43TotalMomentumCoordMultiplierCLM
section43TotalMomentumCoordMultiplierCLM_apply
section43TotalMomentumBasis
section43TotalMomentumBasis_apply_self
section43TotalMomentumBasis_apply_ne
section43TotalMomentumBasisPhaseCLM
section43TotalMomentumBasisPhaseCLM_apply
section43DiagonalTranslationFlat_smul
physicsFourierFlatCLM_diagonalBasisTranslate_eq_basisPhaseCLM
```

is implemented in `Section43FourierLaplaceTransform.lean` and exact-checks.

Sharper implementation refinement, 2026-04-15: the coordinate-annihilation
step does **not** need a new direct seminorm estimate for phase multipliers.
Use the already-proved real-translation difference quotient instead.

For the basis vector

```lean
def section43TotalMomentumBasis
    (d : ℕ) [NeZero d] (μ : Fin (d + 1)) : Fin (d + 1) → ℝ :=
  fun ν => if ν = μ then 1 else 0
```

the diagonal real-space translation direction is

```lean
vμ := section43DiagonalTranslationFlat d N (section43TotalMomentumBasis d μ)
```

The key Fourier derivative identity should be implemented as

```lean
theorem physicsFourierFlatCLM_lineDeriv_eq_pairingMultiplier
    {m : ℕ}
    (v : Fin m → ℝ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    physicsFourierFlatCLM (∂_{v} φ)
      =
    (-Complex.I) •
      SchwartzMap.smulLeftCLM ℂ
        (fun ξ : Fin m → ℝ =>
          ∑ i : Fin m, (v i : ℂ) * (ξ i : ℂ))
        (physicsFourierFlatCLM φ)
```

Proof transcript for the general theorem:

1. Unfold `physicsFourierFlatCLM` as
   `compCLMOfContinuousLinearEquiv scaleNeg ∘ inverseFourierFlatCLM`, where
   `scaleNeg ξ = -(1 / (2 * Real.pi)) • ξ`.
2. Unfold `inverseFourierFlatCLM` as Euclidean transport, Mathlib Fourier
   transform, and transport back.
3. Use `SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv` to move
   `∂_v` through the Euclidean transport.  The transported direction is
   `(EuclideanSpace.equiv (Fin m) ℝ).symm v`.
4. Apply Mathlib's `SchwartzMap.fourier_lineDerivOp_eq`, which gives the
   multiplier `2 * Real.pi * Complex.I * inner η vE`.
5. Apply the final scaling `η = -(1 / (2 * Real.pi)) • ξ`; the scalar factor
   simplifies to `-Complex.I * ∑ i, (v i : ℂ) * (ξ i : ℂ)`.
6. Finish by extensionality and the `SchwartzMap.smulLeftCLM_apply_apply`
   theorem.  The multiplier has temperate growth because it is a finite sum
   of products of constants and coordinate projections.

The diagonal total-momentum specialization is then

```lean
theorem physicsFourierFlatCLM_lineDeriv_diagonalTranslation_eq_coordMultiplier
    (d N : ℕ) [NeZero d]
    (μ : Fin (d + 1))
    (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) :
    physicsFourierFlatCLM
        (∂_{section43DiagonalTranslationFlat d N
            (section43TotalMomentumBasis d μ)} φflat)
      =
    (-Complex.I) •
      section43TotalMomentumCoordMultiplierCLM d N μ
        (physicsFourierFlatCLM φflat)
```

Proof transcript for the specialization:

1. Apply `physicsFourierFlatCLM_lineDeriv_eq_pairingMultiplier` with

```lean
v := section43DiagonalTranslationFlat d N
       (section43TotalMomentumBasis d μ)
```

2. Rewrite the pairing multiplier with
   `section43DiagonalTranslationFlat_complex_pair_eq_totalMomentum` and the
   basis-vector finite-sum identity, giving exactly
   `section43TotalMomentumFlat d N ξ μ`.
3. Finish with
   `section43TotalMomentumCoordMultiplierCLM_apply`.

Production status, 2026-04-15: the helper

```lean
flatComplexPairing_hasTemperateGrowth
```

and the theorem surfaces

```lean
physicsFourierFlatCLM_lineDeriv_eq_pairingMultiplier
physicsFourierFlatCLM_lineDeriv_diagonalTranslation_eq_coordMultiplier
```

are implemented in `Section43FourierLaplaceTransform.lean` and exact-check
without warnings.  The transported-scaling simplification after applying
`SchwartzMap.fourier_lineDerivOp_eq` is now closed in production.

Only after this identity is available, use the existing translation
difference quotient to prove coordinate annihilation.  For each `ξ`, the
same identity can also be justified by scalar limit uniqueness:

```lean
physicsFourierFlatCLM
  (t⁻¹ • (SCV.translateSchwartz (t • vμ) φflat - φflat)) ξ
```

has limit both `physicsFourierFlatCLM (∂_{vμ} φflat) ξ` and
`((-Complex.I) • section43TotalMomentumCoordMultiplierCLM d N μ
  (physicsFourierFlatCLM φflat)) ξ`, but the direct Fourier-derivative theorem
above is the preferred production proof.

In the annihilation proof, rewrite the translated quotient using linearity of
`physicsFourierFlatCLM` and
`physicsFourierFlatCLM_diagonalBasisTranslate_eq_basisPhaseCLM`:

```lean
t⁻¹ •
  (section43TotalMomentumBasisPhaseCLM d N μ t
      (physicsFourierFlatCLM φflat)
    - physicsFourierFlatCLM φflat)
```

Then prove coordinate annihilation without a direct phase-difference theorem:

```lean
theorem tflat_totalMomentumCoordMultiplier_eq_zero_of_phaseInvariant
    (d : ℕ) [NeZero d] {N : ℕ}
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hphase :
      ∀ (a : Fin (d + 1) → ℝ)
        (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
        Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K) :
    (μ : Fin (d + 1))
    (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) :
    Tflat (section43TotalMomentumCoordMultiplierCLM d N μ K) = 0
```

Proof transcript:

1. Use `physicsFourierFlatCLM_surjective` to write
   `K = physicsFourierFlatCLM φflat`.
2. Apply `Tflat.continuous` to the translated difference quotient theorem:

```lean
Filter.Tendsto
  (fun t : ℝ =>
    Tflat (physicsFourierFlatCLM
      (t⁻¹ • (SCV.translateSchwartz (t • vμ) φflat - φflat))))
  (nhdsWithin 0 ({0}ᶜ))
  (𝓝 (Tflat (physicsFourierFlatCLM (∂_{vμ} φflat))))
```

3. For every `t ≠ 0`, rewrite the source term by linearity and
   `physicsFourierFlatCLM_diagonalTranslate_eq_phaseCLM`; `hphase` makes it
   equal to `0`.
4. Limit uniqueness gives
   `Tflat (physicsFourierFlatCLM (∂_{vμ} φflat)) = 0`.
5. Rewrite this with
   `physicsFourierFlatCLM_lineDeriv_diagonalTranslation_eq_coordMultiplier`
   and divide by `-Complex.I`.

Production status, 2026-04-15: this theorem is implemented in
`Section43WightmanDescent.lean` and exact-checks without warnings.  The proof
uses `L := Tflat.comp physicsFourierFlatCLM`; the only Lean subtlety is that
the real scalar action in the difference quotient is rewritten pointwise to
the corresponding complex scalar action before applying complex linearity of
`L`.

Lean proof transcript for
`hasFourierSupportIn_totalMomentumZero_of_phase_invariant`:

1. Use `tflat_totalMomentumCoordMultiplier_eq_zero_of_phaseInvariant` to obtain,
   for each `μ : Fin (d + 1)`,

```lean
Tflat
  (SchwartzMap.smulLeftCLM ℂ
    (fun ξ => (section43TotalMomentumFlat d N ξ μ : ℂ)) K)
  = 0
```

2. If `K` has support disjoint from
   `section43TotalMomentumZeroFlat d N`, then `K` vanishes on the zero set:

```lean
have hK_zero :
    ∀ ξ, section43TotalMomentumFlat d N ξ = 0 → K ξ = 0 := by
  intro ξ hξ
  by_contra hne
  exact hK ξ (Function.mem_support.mpr hne) hξ
```

3. Prove the compact-support decomposition for functions that vanish on the
   total-momentum hyperplane.  This cannot be replaced by a neighborhood
   reciprocal-cutoff argument: `HasFourierSupportIn` uses
   `Function.support`, not closed support, so a Schwartz test may vanish on
   the hyperplane while being nonzero arbitrarily close to it.  The exact
   hyperplane-division theorem is therefore necessary.

```lean
theorem exists_eq_sum_totalMomentum_smul_of_vanishes_totalMomentumZero_of_hasCompactSupport
    (d N : ℕ) [NeZero d]
    (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ)
    (hK_compact : HasCompactSupport (K : (Fin (N * (d + 1)) → ℝ) → ℂ))
    (hK_zero :
      ∀ ξ, section43TotalMomentumFlat d N ξ = 0 → K ξ = 0) :
    ∃ H : Fin (d + 1) →
        SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
      K =
        ∑ μ : Fin (d + 1),
          SchwartzMap.smulLeftCLM ℂ
            (fun ξ => (section43TotalMomentumFlat d N ξ μ : ℂ)) (H μ)
```

   Proof transcript for this compact decomposition:

   1. For `N = 0`, `section43TotalMomentumZeroFlat d 0 = Set.univ`, so
      `hK_zero` gives `K = 0`; choose all `H μ = 0`.
   2. For `N = N' + 1`, build the direct total-momentum/head-tail continuous
      linear equivalence

```lean
noncomputable def section43TotalMomentumHeadTailCLE
    (d N' : ℕ) [NeZero d] :
    (Fin ((N' + 1) * (d + 1)) → ℝ) ≃L[ℝ]
      (Fin ((d + 1) + (N' * (d + 1))) → ℝ)
```

      whose first `d + 1` coordinates are
      `section43TotalMomentumFlat d (N' + 1) ξ`, and whose tail coordinates
      are the original particle coordinates with particle `0` removed:

```lean
splitFirst (d + 1) (N' * (d + 1))
  (section43TotalMomentumHeadTailCLE d N' ξ)
    = section43TotalMomentumFlat d (N' + 1) ξ

splitLast (d + 1) (N' * (d + 1))
  (section43TotalMomentumHeadTailCLE d N' ξ)
    = fun j => ξ (finProdFinEquiv (j.1.succ, j.2))
```

      Its inverse sends `(p, ηtail)` to the flat vector whose nonzero-tail
      particles are `ηtail`, and whose particle `0` coordinate is

```lean
p μ - ∑ j : Fin N', ηtail (finProdFinEquiv (j, μ)).
```

      The left/right inverse proofs are coordinate extensionality plus the
      finite-sum identity

```lean
∑ k : Fin (N' + 1), ξ (finProdFinEquiv (k, μ))
  =
ξ (finProdFinEquiv (0, μ)) +
  ∑ j : Fin N', ξ (finProdFinEquiv (j.succ, μ)).
```

      This direct equivalence is preferable to a cumulative-tail equivalence:
      it exposes the total-momentum hyperplane as the literal zero-head
      section needed by the compact head-block division theorem.

      Production status, 2026-04-15: this equivalence is implemented in
      `Section43TotalMomentumSupport.lean` as
      `section43TotalMomentumHeadTailCLE`, with exact head/tail and inverse
      coordinate lemmas.  The file exact-checks without warnings.
   3. Pull `K` back along `section43TotalMomentumHeadTailCLE.symm`.  The pulled
      function has zero head-section for every tail value.
   4. Prove the compact head-block decomposition theorem, using the existing
      `headCoordCoeff` and cutoff machinery from
      `TranslationInvariantSchwartz.lean`:

```lean
theorem exists_eq_sum_headBlock_coord_smul_of_zeroHeadSection_of_hasCompactSupport
    {p q : ℕ}
    (F : SchwartzMap (Fin (p + q) → ℝ) ℂ)
    (hF_compact : HasCompactSupport (F : (Fin (p + q) → ℝ) → ℂ))
    (hF :
      ∀ y : Fin q → ℝ,
        F (zeroHeadBlockShift (m := p) (n := q) y) = 0) :
    ∃ G : Fin p → SchwartzMap (Fin (p + q) → ℝ) ℂ,
      F =
        ∑ μ : Fin p,
          SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin (p + q) → ℝ => x (Fin.castAdd q μ))
            (G μ)
```

      Implement it by induction on `p`.

      Base `p = 0`: `zeroHeadBlockShift` is the identity on
      `Fin (0 + q) → ℝ`, so the zero-head-section hypothesis gives `F = 0`;
      choose the empty family.

      Successor step `p = p' + 1`: after the usual `Nat.succ_add` reindexing,
      set

```lean
h := headSectionCLM (p' + q) F
R := F - unitBumpSchwartz.prependField h
```

      Then `h` has compact support and satisfies the zero-head-section
      hypothesis for the remaining `p'` head coordinates; `R` has compact
      support and zero first head-section.  Factor `R` by the first coordinate
      using
      `exists_eq_coord_smul_of_headSection_zero_of_hasCompactSupport`; factor
      `h` by the induction hypothesis; prepend those tail coefficients back
      with `unitBumpSchwartz.prependField`.  Compact support is preserved by
      `headSectionCLM`, `prependField`, and subtraction, exactly as in
      `exists_eq_sum_coord_smul_of_zero_of_hasCompactSupport`.

      Production status, 2026-04-15: this theorem is implemented in the small
      companion file `HeadBlockDecomposition.lean` and exact-checks without
      warnings.  The theorem intentionally uses real coordinate multipliers,
      matching `exists_eq_coord_smul_of_headSection_zero_of_hasCompactSupport`;
      the later total-momentum pushforward is responsible for rewriting real
      scalar multiplication as complex multiplication where it meets
      `section43TotalMomentumCoordMultiplierCLM`.
   5. Push the resulting `G μ` forward through
      `section43TotalMomentumHeadTailCLE` to obtain the desired `H μ`.  The
      coordinate identity above rewrites the head-coordinate multipliers to
      real scalar multiplication by the total-momentum coordinate, and then
      `Complex.real_smul`/`smul_eq_mul` identifies this with
      `section43TotalMomentumCoordMultiplierCLM d (N' + 1) μ`.

   Production status, 2026-04-15: this compact total-momentum division theorem
   is implemented in `Section43TotalMomentumSupport.lean` as
   `exists_eq_sum_totalMomentum_smul_of_vanishes_totalMomentumZero_of_hasCompactSupport`.
   The proof follows the transcript above: the `N = 0` case is zero, and the
   successor case pulls back through `section43TotalMomentumHeadTailCLE`,
   applies the generic compact head-block theorem, then pushes the coefficients
   forward and rewrites the real head-coordinate multiplier to
   `section43TotalMomentumCoordMultiplierCLM`.

4. Apply the derivative equations from step 1 to every summand in the compact
   decomposition and sum the results.  This gives `Tflat Kc = 0` for every
   compactly supported Schwartz `Kc` that vanishes on the total-momentum zero
   set.
5. For a general Schwartz `K` satisfying the support-disjoint hypothesis,
   define compact truncations

```lean
Kc R := bumpTruncationRadius K R
```

   from `SchwartzDensity.lean`.  Each `Kc R` is compactly supported and still
   vanishes on the total-momentum zero set because it is a pointwise
   multiplier of `K`.
6. Use `SchwartzMap.tendsto_bump_truncation_nhds K` and continuity of `Tflat`
   to pass from `Tflat (Kc R) = 0` for all `R` to `Tflat K = 0`.  This is
   exactly the `HasFourierSupportIn` condition for
   `section43TotalMomentumZeroFlat`.

Production status, 2026-04-15: this support theorem is implemented in
`Section43WightmanDescent.lean` as
`hasFourierSupportIn_totalMomentumZero_of_phase_invariant` and exact-checks
without warnings.  Its proof uses the compact bump truncations from
`SchwartzDensity.lean`; each truncation is compactly supported, still vanishes
on the total-momentum zero set pointwise, decomposes through the compact
total-momentum division theorem, is killed by coordinate annihilation, and
then converges back to the original Schwartz test by continuity of `Tflat`.

Implemented theorem split for the total-momentum support step:

```lean
theorem exists_eq_sum_headBlock_coord_smul_of_zeroHeadSection_of_hasCompactSupport
    {p q : ℕ}
    (F : SchwartzMap (Fin (p + q) → ℝ) ℂ)
    (hF_compact : HasCompactSupport (F : (Fin (p + q) → ℝ) → ℂ))
    (hF_zero :
      ∀ y : Fin q → ℝ,
        F (zeroHeadBlockShift (m := p) (n := q) y) = 0) :
    ∃ G : Fin p → SchwartzMap (Fin (p + q) → ℝ) ℂ,
      F =
        ∑ μ : Fin p,
          SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin (p + q) → ℝ => x (Fin.castAdd q μ))
            (G μ)

noncomputable def section43TotalMomentumHeadTailCLE
    (d N' : ℕ) [NeZero d] :
    (Fin ((N' + 1) * (d + 1)) → ℝ) ≃L[ℝ]
      (Fin ((d + 1) + (N' * (d + 1))) → ℝ)

theorem exists_eq_sum_totalMomentum_smul_of_vanishes_totalMomentumZero_of_hasCompactSupport
    (d N : ℕ) [NeZero d]
    (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ)
    (hK_compact : HasCompactSupport (K : (Fin (N * (d + 1)) → ℝ) → ℂ))
    (hK_zero :
      ∀ ξ, section43TotalMomentumFlat d N ξ = 0 → K ξ = 0) :
    ∃ H : Fin (d + 1) →
        SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
      K =
        ∑ μ : Fin (d + 1),
          section43TotalMomentumCoordMultiplierCLM d N μ (H μ)

theorem hasFourierSupportIn_totalMomentumZero_of_phase_invariant
    (d N : ℕ) [NeZero d]
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hphase :
      ∀ (a : Fin (d + 1) → ℝ)
        (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
        Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K) :
    HasFourierSupportIn (section43TotalMomentumZeroFlat d N) Tflat
```

Lean implementation notes for this split:

1. The generic head-block theorem lives outside the Section 4.3 OS-specific
   file, in `HeadBlockDecomposition.lean`, importing `BlockIntegral.lean` and
   `TranslationInvariantSchwartz.lean`.  It depends on the existing
   `headSectionCLM`, `unitBumpSchwartz.prependField`,
   `hasCompactSupport_prependField`,
   `exists_eq_coord_smul_of_headSection_zero_of_hasCompactSupport`, and the
   `zeroHeadBlockShift`/`castFinCLE` reindexing API.
2. The successor case for the generic theorem should first reindex
   `Fin ((p + 1) + q)` to `Fin ((p + q) + 1)` using
   `castFinCLE (Nat.succ_add p q)` so that `headSectionCLM (p + q)` applies
   to the first head coordinate.  After the decomposition is proved in the
   reindexed coordinates, push it back through
   `SchwartzMap.compCLMOfContinuousLinearEquiv`.
3. The base case `p = 0` is not a compactness argument: use
   `splitLast_zeroHeadBlockShift_eq`/subsingleton extensionality to show every
   `x : Fin (0 + q) → ℝ` is the zero-head insertion of its tail, hence
   `F x = 0`; choose the empty coefficient family.
4. The total-momentum/head-tail CLE is implemented in
   `Section43TotalMomentumSupport.lean`.  Its forward map is by cases on
   `Fin ((d + 1) + (N' * (d + 1)))`: head indices
   `Fin.castAdd (N' * (d + 1)) μ` map to
   `section43TotalMomentumFlat d (N' + 1) ξ μ`; tail indices
   `Fin.natAdd (d + 1) j` map to
   `ξ (finProdFinEquiv (j.1.succ, j.2))` after identifying
   `j : Fin (N' * (d + 1))` with `Fin N' × Fin (d + 1)` by
   `finProdFinEquiv.symm`.
5. Define the inverse by setting particle `0` equal to head momentum minus the
   sum of the tail particles, and particles `j.succ` equal to the tail block.
   This is now production code.  The left/right inverse proofs reduce to
   extensionality over
   `finProdFinEquiv (k, μ)` and the finite-sum split over `Fin (N' + 1)`.
6. After pulling `K` back through the CLE, the zero-head-section hypothesis is
   exactly `hK_zero`, because the head block is
   `section43TotalMomentumFlat`.  Pushing the generic head-block decomposition
   forward rewrites each real head-coordinate multiplier to the corresponding
   total-momentum coordinate multiplier; finish the type-level scalar
   conversion pointwise with `Complex.real_smul` and `smul_eq_mul`.

The next honest frontier is now the combined support theorem.  Important
correction, 2026-04-15: this cannot be a generic closed-set intersection lemma
for the current `HasFourierSupportIn` predicate.

Reason: `HasFourierSupportIn` is intentionally a pointwise
`Function.support` predicate, so it proves an `EqOn` principle, not merely
ordinary distributional closed-support containment.  For this strong predicate
the naive theorem

```lean
theorem hasFourierSupportIn_inter_of_closed
    {S : Set (Fin (N * (d + 1)) → ℝ)}
    {H : Set (Fin (N * (d + 1)) → ℝ)}
    {Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ}
    (hS_closed : IsClosed S)
    (hH_closed : IsClosed H)
    (hdual : HasFourierSupportIn S Tflat)
    (htotal : HasFourierSupportIn H Tflat) :
    HasFourierSupportIn (S ∩ H) Tflat
```

is false for arbitrary closed `S` and `H`.  A model obstruction is in `ℝ²`:
let `S` be the `x`-axis, let `H` be the parabola `y = x^2`, and let
`T φ = ∂ₓ φ (0,0)`.  If a smooth test vanishes pointwise on `S`, then its
restriction to the `x`-axis is identically zero, so `T φ = 0`; the same holds
for tests vanishing pointwise on `H`, because the tangent of `H` at the origin
is also the `x`-axis.  But `S ∩ H = {(0,0)}`, and `φ(x,y)=x` vanishes
pointwise on the intersection while `T φ = 1`.  Thus the old generic
intersection statement would be unsound for the exact support interface used
by production.

The corrected proof obligation is not a two-sided smooth partition.  The OS
geometry gives a more concrete projection/extension route.

For `N = N' + 1`, use the total-momentum/head-tail equivalence already
implemented as `section43TotalMomentumHeadTailCLE d N'`.  Its head block is
the total momentum, and its tail block consists of particles `1, ..., N'`.
Define the zero-total-momentum projection by setting the head block to zero
and keeping this tail block fixed:

```lean
noncomputable def section43TotalMomentumZeroProjection
    (d N' : ℕ) [NeZero d] :
    (Fin ((N' + 1) * (d + 1)) → ℝ) →L[ℝ]
      (Fin ((N' + 1) * (d + 1)) → ℝ)
```

with defining equation

```lean
section43TotalMomentumHeadTailCLE d N'
    (section43TotalMomentumZeroProjection d N' ξ)
  =
zeroHeadBlockShift
  (m := d + 1) (n := N' * (d + 1))
  (splitLast (d + 1) (N' * (d + 1))
    (section43TotalMomentumHeadTailCLE d N' ξ))
```

This projection is the concrete Section 4.3 substitute for a generic
closed-set intersection theorem.  It has three required properties:

```lean
theorem section43TotalMomentumZeroProjection_mem_totalMomentumZero
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    section43TotalMomentumZeroProjection d N' ξ ∈
      section43TotalMomentumZeroFlat d (N' + 1)

theorem section43TotalMomentumZeroProjection_eq_of_mem_totalMomentumZero
    (d N' : ℕ) [NeZero d]
    {ξ : Fin ((N' + 1) * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43TotalMomentumZeroFlat d (N' + 1)) :
    section43TotalMomentumZeroProjection d N' ξ = ξ

theorem section43TotalMomentumZeroProjection_mem_dualCone
    (d N' : ℕ) [NeZero d]
    {ξ : Fin ((N' + 1) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (N' + 1) (d + 1)) ''
          ForwardConeAbs d (N' + 1))) :
    section43TotalMomentumZeroProjection d N' ξ ∈
      DualConeFlat
        ((flattenCLEquivReal (N' + 1) (d + 1)) ''
          ForwardConeAbs d (N' + 1))
```

Proof transcript for the projection lemmas:

1. The first two lemmas are direct from
   `splitFirst_section43TotalMomentumHeadTailCLE`,
   `splitFirst_zeroHeadBlockShift_eq_zero`, and injectivity of the
   continuous linear equivalence.  The head block is
   `section43TotalMomentumFlat`, so zeroing the head is exactly the
   total-momentum-zero condition.
2. For dual-cone preservation, use the unscaled cumulative-tail coordinates
   `section43RawCumulativeTailMomentumCLE`, not the spatially rescaled
   `section43CumulativeTailMomentumCLE`.  Prove first:

```lean
theorem section43DiffCoord_pairing_eq_rawCumulativeTail
    (d n : ℕ) [NeZero d]
    (δ : NPointDomain d n)
    (ξ : Fin (n * (d + 1)) → ℝ) :
    (∑ i : Fin (n * (d + 1)),
        flattenCLEquivReal n (d + 1)
          ((section43DiffCoordRealCLE d n).symm δ) i * ξ i)
      =
    ∑ j : Fin n, ∑ μ : Fin (d + 1),
      δ j μ * section43RawCumulativeTailMomentumCLE d n ξ j μ
```

   This is the general version of the already implemented time-axis pairing
   computation.  The proof uses
   `section43DiffCoordRealCLE_symm_apply`,
   `section43RawCumulativeTailMomentumCLE_apply`, and a local public copy of
   the finite-sum rearrangement currently used privately in
   `Section43FourierLaplaceTransform.lean`:

```lean
theorem section43_fin_prefix_sum_eq_lower_sum_public
    {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → A) (k : Fin n) :
    (∑ l : Fin (k.val + 1), f ⟨l.val, by omega⟩) =
      ∑ j : Fin n, if j.val ≤ k.val then f j else 0

theorem section43_fin_prefix_mul_eq_sum_tail_public
    {n : ℕ} (a b : Fin n → ℝ) :
    (∑ k : Fin n, (∑ l : Fin (k.val + 1), a ⟨l.val, by omega⟩) * b k) =
      ∑ j : Fin n, a j * ∑ k : Fin n, if j.val ≤ k.val then b k else 0
```

   These are not new mathematics; copy the existing private proofs verbatim
   into `Section43SpectralSupport.lean` with public names so this support file
   does not depend on private declarations.
3. Show the projection zeroes only the first raw cumulative tail momentum:

```lean
theorem section43TotalMomentumZeroProjection_rawCumulative_zero
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) (μ : Fin (d + 1)) :
    section43RawCumulativeTailMomentumCLE d (N' + 1)
      (section43TotalMomentumZeroProjection d N' ξ)
      (0 : Fin (N' + 1)) μ = 0

theorem section43TotalMomentumZeroProjection_rawCumulative_succ
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ)
    (j : Fin N') (μ : Fin (d + 1)) :
    section43RawCumulativeTailMomentumCLE d (N' + 1)
      (section43TotalMomentumZeroProjection d N' ξ)
      (j.succ) μ =
    section43RawCumulativeTailMomentumCLE d (N' + 1) ξ (j.succ) μ
```

   Coordinate proof: in head-tail coordinates, the projection keeps particles
   `1, ..., N'` fixed and replaces particle `0` by the negative tail sum, so
   the total raw cumulative momentum is zero and every later cumulative tail
   is unchanged.
4. To prove dual-cone preservation, introduce arbitrary
   `y ∈ ForwardConeAbs d (N' + 1)`, write
   `δ := section43DiffCoordRealCLE d (N' + 1) y`, and use the pairing lemma.
   The target pairing with the projected point is the sum over `j.succ` only,
   because the `j=0` raw cumulative tail is zero.
5. If that target sum were negative, choose the first-difference perturbation

```lean
def section43FirstDiffTimeAxisPerturbation
    (d N' : ℕ) [NeZero d]
    (δ : NPointDomain d (N' + 1)) (ε : ℝ) :
    NPointDomain d (N' + 1) :=
  fun k μ =>
    if k = 0 then
      if μ = 0 then ε else 0
    else
      δ k μ
```

   The needed cone-membership helpers are public versions of private lemmas
   already used in `Section43FourierLaplaceTransform.lean`:

```lean
theorem section43_inOpenForwardCone_timeAxis_public
    (d : ℕ) [NeZero d] {a : ℝ} (ha : 0 < a) :
    InOpenForwardCone d
      (fun μ : Fin (d + 1) => if μ = 0 then a else 0)

theorem section43DiffCoordRealCLE_mem_openForwardCone_of_mem_forwardConeAbs
    (d n : ℕ) [NeZero d]
    {y : NPointDomain d n} (hy : y ∈ ForwardConeAbs d n) :
    ∀ k : Fin n, InOpenForwardCone d (section43DiffCoordRealCLE d n y k)

theorem section43DiffCoordRealCLE_symm_mem_forwardConeAbs_public
    (d n : ℕ) [NeZero d]
    {δ : NPointDomain d n}
    (hδ : ∀ k : Fin n, InOpenForwardCone d (δ k)) :
    (section43DiffCoordRealCLE d n).symm δ ∈ ForwardConeAbs d n

theorem section43FirstDiffTimeAxisPerturbation_mem_forwardConeAbs
    (d N' : ℕ) [NeZero d]
    {δ : NPointDomain d (N' + 1)} {ε : ℝ}
    (hε : 0 < ε)
    (hδ_tail : ∀ j : Fin N',
      InOpenForwardCone d (δ j.succ)) :
    (section43DiffCoordRealCLE d (N' + 1)).symm
      (section43FirstDiffTimeAxisPerturbation d N' δ ε)
      ∈ ForwardConeAbs d (N' + 1)
```

   The last proof is by
   `section43DiffCoordRealCLE_symm_mem_forwardConeAbs_public`; the `k = 0`
   case uses `section43_inOpenForwardCone_timeAxis_public hε`, and the
   successor cases use `hδ_tail`.

   Applying the original dual-cone hypothesis to this perturbed point gives

```lean
0 ≤ ε * c + targetSum
```

   where `c` is the finite first-tail pairing.  The only real-analysis helper
   needed for the contradiction is:

```lean
theorem exists_pos_mul_abs_lt_of_neg {c s : ℝ} (hs : s < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε * |c| < -s
```

   Prove it with `ε := (-s) / (2 * (|c| + 1))`; positivity is immediate from
   `hs`, and `nlinarith [abs_nonneg c]` closes the strict bound.  With
   `s = targetSum`, the inequalities
   `ε * c ≤ ε * |c|` and `ε * |c| < -targetSum` imply
   `ε * c + targetSum < 0`, contradicting `0 ≤ ε * c + targetSum`.  Hence the
   target pairing is nonnegative for every `y`, which is exactly membership of
   the projection in the dual cone.

Next build a Schwartz extension from the total-momentum-zero hyperplane that
agrees with a given test on that hyperplane and vanishes on the dual cone
whenever the original test vanishes on the spectral region:

```lean
theorem exists_section43TotalMomentumZeroExtension_vanishes_dualCone
    (d N : ℕ) [NeZero d]
    (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ)
    (hK :
      ∀ ξ, ξ ∈ section43WightmanSpectralRegion d N → K ξ = 0) :
    ∃ KE : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
      (∀ ξ, ξ ∈ section43TotalMomentumZeroFlat d N → KE ξ = K ξ) ∧
      (∀ ξ, ξ ∈
        DualConeFlat ((flattenCLEquivReal N (d + 1)) ''
          ForwardConeAbs d N) → KE ξ = 0)
```

Implementation-ready helper packet for this extension should live in a new
small file, for example
`OSReconstruction/Wightman/Reconstruction/WickRotation/Section43SpectralSupport.lean`,
importing `Section43TotalMomentumSupport`.  Do not reopen the large stable
Schwartz files for these route-specific helpers.

First expose the linear zero-head insertion.  The existing
`zeroHeadBlockShift` is the right pointwise map; the new CLM is only the
linear packaging needed to define the projection without hiding `sorry`s in a
definition:

```lean
noncomputable def zeroHeadBlockShiftCLM (m n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin (m + n) → ℝ)

@[simp] theorem zeroHeadBlockShiftCLM_apply (m n : ℕ)
    (y : Fin n → ℝ) :
    zeroHeadBlockShiftCLM m n y =
      zeroHeadBlockShift (m := m) (n := n) y
```

Proof transcript: define `toFun := zeroHeadBlockShift`; prove `map_add'` and
`map_smul'` by induction on `m`, using the recursive definition of
`zeroHeadBlockShift`, `castFinCLE`, `Fin.cons`, and extensionality.  The
`m = 0` case reduces by `castFinCLE (Nat.zero_add n)`.  The successor case
reduces to the induction hypothesis after applying `castFinCLE
(Nat.succ_add m n)` to both sides.

Then define the projection by CLM composition, not by a raw lambda:

```lean
noncomputable def section43TotalMomentumZeroProjection
    (d N' : ℕ) [NeZero d] :
    (Fin ((N' + 1) * (d + 1)) → ℝ) →L[ℝ]
      (Fin ((N' + 1) * (d + 1)) → ℝ) :=
  let e := section43TotalMomentumHeadTailCLE d N'
  e.symm.toContinuousLinearMap.comp
    ((zeroHeadBlockShiftCLM (d + 1) (N' * (d + 1))).comp
      ((splitLastCLM (d + 1) (N' * (d + 1))).comp
        e.toContinuousLinearMap))

@[simp] theorem section43TotalMomentumZeroProjection_headTail
    (d N' : ℕ) [NeZero d]
    (ξ : Fin ((N' + 1) * (d + 1)) → ℝ) :
    section43TotalMomentumHeadTailCLE d N'
        (section43TotalMomentumZeroProjection d N' ξ)
      =
    zeroHeadBlockShift
      (m := d + 1) (n := N' * (d + 1))
      (splitLast (d + 1) (N' * (d + 1))
        (section43TotalMomentumHeadTailCLE d N' ξ))
```

The proof of the head-tail equation is just `simp` with
`zeroHeadBlockShiftCLM_apply`, `splitLastCLM_apply`, and
`ContinuousLinearEquiv.apply_symm_apply`.

The extension itself needs two generic head-block Schwartz helpers.  Avoid the
tempting but insufficient shortcut "`G ∘ splitLast` is Schwartz": it is
constant in the head directions and has no head decay.  The correct
implementation is recursive and uses the already compiled
`unitBumpSchwartz.prependField`, which builds in the missing head decay.

```lean
noncomputable def zeroHeadSectionCLM :
    ∀ p q : ℕ,
      SchwartzMap (Fin (p + q) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin q → ℝ) ℂ
  | 0, q =>
      reindexSchwartzFin (Nat.zero_add q)
  | p + 1, q =>
      (zeroHeadSectionCLM p q).comp
        ((headSectionCLM (p + q)).comp
          (reindexSchwartzFin (Nat.succ_add p q)))

@[simp] theorem zeroHeadSectionCLM_apply
    (p q : ℕ) (F : SchwartzMap (Fin (p + q) → ℝ) ℂ)
    (y : Fin q → ℝ) :
    zeroHeadSectionCLM p q F y =
      F (zeroHeadBlockShift (m := p) (n := q) y)
```

Proof transcript: induction on `p`.  The base case uses
`reindexSchwartzFin_apply` and the definition of `zeroHeadBlockShift` at
`m = 0`.  The successor case uses `reindexSchwartzFin_apply`,
`headSectionCLM_apply`, the recursive equation for `zeroHeadBlockShift`, and
the induction hypothesis.

```lean
noncomputable def headBlockBumpExtension :
    ∀ p q : ℕ,
      SchwartzMap (Fin q → ℝ) ℂ →
        SchwartzMap (Fin (p + q) → ℝ) ℂ
  | 0, q, G =>
      reindexSchwartzFin (Nat.zero_add q).symm G
  | p + 1, q, G =>
      reindexSchwartzFin (Nat.succ_add p q).symm
        (unitBumpSchwartz.prependField
          (headBlockBumpExtension p q G))

@[simp] theorem headBlockBumpExtension_zeroHeadBlockShift
    (p q : ℕ) (G : SchwartzMap (Fin q → ℝ) ℂ)
    (y : Fin q → ℝ) :
    headBlockBumpExtension p q G
      (zeroHeadBlockShift (m := p) (n := q) y) =
      G y

theorem headBlockBumpExtension_eq_zero_of_tail_zero
    (p q : ℕ) (G : SchwartzMap (Fin q → ℝ) ℂ)
    (x : Fin (p + q) → ℝ)
    (hG : G (splitLast p q x) = 0) :
    headBlockBumpExtension p q G x = 0
```

Proof transcript for `headBlockBumpExtension_zeroHeadBlockShift`: induction on
`p`; the base case is `simp [headBlockBumpExtension, zeroHeadBlockShift]`; the
successor case rewrites the recursive `zeroHeadBlockShift` to
`Fin.cons 0 (zeroHeadBlockShift ...)`, unfolds `prependField`, uses
`unitBumpSchwartz_zero`, and applies the induction hypothesis.

Proof transcript for `headBlockBumpExtension_eq_zero_of_tail_zero`: induction
on `p`.  The base case follows from `splitLast 0 q` and
`reindexSchwartzFin_apply`.  In the successor case, set
`x' := castFinCLE (Nat.succ_add p q) x`; then

```lean
headBlockBumpExtension (p + 1) q G x =
  unitBumpSchwartz (x' 0) *
    headBlockBumpExtension p q G (fun i : Fin (p + q) => x' i.succ)
```

by `reindexSchwartzFin_apply` and `SchwartzMap.prependField_apply`.  The tail
of `fun i => x' i.succ` is `splitLast (p + 1) q x`, so the induction
hypothesis kills the second factor.  If Lean needs it, add this local helper
beside the proof:

```lean
theorem splitLast_castFinCLE_succ_add_tail
    {p q : ℕ} (x : Fin ((p + 1) + q) → ℝ) :
    splitLast p q
        (fun i : Fin (p + q) =>
          (castFinCLE (Nat.succ_add p q) x) i.succ)
      =
    splitLast (p + 1) q x
```

This helper is a one-line extensionality proof after unfolding `splitLast`,
`castFinCLE`, and `finCongr`; the index equality is `Fin.ext` plus `omega`.

Proof transcript for the extension theorem:

1. For `N = 0`, `section43TotalMomentumZeroFlat d 0 = Set.univ`; take
   `KE = K`.  The vanishing on the dual cone follows from `hK`, because the
   spectral region is the dual cone intersected with `Set.univ`.
2. For `N = N' + 1`, pull `K` to head-tail coordinates with
   `section43TotalMomentumHeadTailCLE d N'`.  Let

```lean
F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43TotalMomentumHeadTailCLE d N').symm K
```

3. Take the zero-head section using the helper:

```lean
G := zeroHeadSectionCLM (d + 1) (N' * (d + 1)) F
```

4. Extend `G` back to the full head-tail space with the recursive bump
   extension:

```lean
B := headBlockBumpExtension (d + 1) (N' * (d + 1)) G
```

   The only pointwise facts needed downstream are:

```lean
B (zeroHeadBlockShift y) = G y
G (splitLast ... x) = 0 → B x = 0
```

5. Push `B` back through `section43TotalMomentumHeadTailCLE d N'` to obtain
   `KE`:

```lean
KE := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
  (section43TotalMomentumHeadTailCLE d N') B
```

6. If `ξ ∈ section43TotalMomentumZeroFlat`, then
   `splitFirst (d + 1) (N' * (d + 1))
     (section43TotalMomentumHeadTailCLE d N' ξ) = 0`.  Use the generic
   reconstruction helper

```lean
theorem eq_zeroHeadBlockShift_of_splitFirst_eq_zero
    {p q : ℕ} {x : Fin (p + q) → ℝ}
    (hx : splitFirst p q x = 0) :
    x = zeroHeadBlockShift (m := p) (n := q) (splitLast p q x)
```

   proved by extensionality over `Fin.addCases`, `splitFirst`, `splitLast`,
   and `zeroHeadBlockShift`.  Then
   `headBlockBumpExtension_zeroHeadBlockShift` and
   `zeroHeadSectionCLM_apply` give
   `KE ξ = F (section43TotalMomentumHeadTailCLE d N' ξ) = K ξ`.
7. If `ξ` lies in the dual cone, let

```lean
η := section43TotalMomentumZeroProjection d N' ξ
```

   Then `η` is in the total-momentum-zero set and, by the projection lemma,
   still in the dual cone.  Thus `η ∈ section43WightmanSpectralRegion`, so
   `K η = 0` by `hK`.  The projection head-tail equation gives

```lean
zeroHeadBlockShift
  (m := d + 1) (n := N' * (d + 1))
  (splitLast (d + 1) (N' * (d + 1))
    (section43TotalMomentumHeadTailCLE d N' ξ))
=
section43TotalMomentumHeadTailCLE d N' η
```

   after symmetry.  Therefore
   `G (splitLast ... (section43TotalMomentumHeadTailCLE d N' ξ)) = K η = 0`,
   and `headBlockBumpExtension_eq_zero_of_tail_zero` gives `KE ξ = 0`.

This extension theorem is the exact support-combination content needed by the
strong `HasFourierSupportIn` interface.

Once the extension theorem is proved, the combined support theorem is short and
implementation-ready:

```lean
theorem hasFourierSupportIn_wightmanSpectralRegion_of_dualCone_and_totalMomentumZero
    (d N : ℕ) [NeZero d]
    {Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ}
    (hdual :
      HasFourierSupportIn
        (DualConeFlat ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
        Tflat)
    (htotal :
      HasFourierSupportIn (section43TotalMomentumZeroFlat d N) Tflat) :
    HasFourierSupportIn (section43WightmanSpectralRegion d N) Tflat
```

Proof transcript for the combined theorem:

1. Introduce `K` and `hKsupp`, where
   `hKsupp : ∀ ξ ∈ Function.support K, ξ ∉ section43WightmanSpectralRegion d N`.
2. Convert `hKsupp` into pointwise vanishing on the spectral region:

```lean
have hKzero :
    ∀ ξ, ξ ∈ section43WightmanSpectralRegion d N → K ξ = 0 := by
  intro ξ hξ
  by_contra hne
  exact hKsupp ξ (Function.mem_support.mpr hne) hξ
```

3. Apply
   `exists_section43TotalMomentumZeroExtension_vanishes_dualCone d N K hKzero`
   and obtain `KE`.
4. Since `K - KE` vanishes pointwise on the total-momentum-zero set, apply
   `htotal` to `K - KE` and use linearity to get `Tflat K = Tflat KE`.
5. Since `KE` vanishes pointwise on the dual cone, apply `hdual KE` to get
   `Tflat KE = 0`.
6. Conclude `Tflat K = 0`.

The remaining proof-doc work is therefore focused and local: implement the
zero-total-momentum projection, prove it preserves the dual cone, and build
the Schwartz extension from the zero-head section.

The OS-route helper is then:

```lean
theorem hasFourierSupportIn_inter_of_dualCone_and_totalMomentumZero
    {Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ}
    (hdual :
      HasFourierSupportIn
        (DualConeFlat ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
        Tflat)
    (htotal :
      HasFourierSupportIn (section43TotalMomentumZeroFlat d N) Tflat) :
    HasFourierSupportIn (section43WightmanSpectralRegion d N) Tflat
```

This name may be kept for downstream compatibility, but its proof must go
through
`exists_section43TotalMomentumZeroExtension_vanishes_dualCone`, not through
the false generic closed-set intersection lemma.

Production status, 2026-04-15: the projection/extension helper packet is
implemented in
`OSReconstruction/Wightman/Reconstruction/WickRotation/Section43SpectralSupport.lean`
and exact-checked.  The generic phase-invariance-to-total-momentum support
lemmas now live in that support module:

```lean
tflat_totalMomentumCoordMultiplier_eq_zero_of_phaseInvariant
hasFourierSupportIn_totalMomentumZero_of_phase_invariant
hasFourierSupportIn_wightmanSpectralRegion_of_dualCone_and_totalMomentumZero
hasFourierSupportIn_inter_of_dualCone_and_totalMomentumZero
```

Only after this OS-specific projection/extension helper exists does
`bvt_W_flattened_distribution_hasFourierSupportIn_wightmanSpectralRegion`
become a direct implementation:

1. Obtain `Tflat`, `hdual`, and `hTflat_bv` from the existing
   `exists_flattened_bvt_W_dualCone_distribution`.
2. Derive `hphase` from `hTflat_bv` and `bvt_W_flat_diagonalTranslate_eq`.
3. Derive `htotal` from
   `hasFourierSupportIn_totalMomentumZero_of_phase_invariant`.
4. Combine `hdual` and `htotal` with
   `hasFourierSupportIn_inter_of_dualCone_and_totalMomentumZero`.

Production status, 2026-04-15: this stronger flattened Wightman support
provider is implemented in
`OSToWightmanBoundaryValueLimits.lean` as

```lean
bvt_W_flattened_distribution_hasFourierSupportIn_wightmanSpectralRegion
```

It obtains the old private dual-cone witness, derives total-momentum-zero
support from local `bvt_W` translation invariance, and combines the two
supports using the Section-4.3 projection/extension theorem.  Fresh checks:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits
```

both terminate with exit code `0`.

Define the two frequency maps needed by the product expansion:

```lean
def section43RightTailBlock
    (d n r : ℕ) [NeZero d]
    (q : NPointDomain d (n + r)) : NPointDomain d r :=
  fun j μ => q ⟨n + j.val, by omega⟩ μ

def section43LeftBorchersBlock
    (d n r : ℕ) [NeZero d] (hr : 0 < r)
    (q : NPointDomain d (n + r)) : NPointDomain d n :=
  fun i μ => q ⟨n - i.val, by omega⟩ μ
```

The shifted index in `section43LeftBorchersBlock` is intentional.  It uses
`q_n, q_{n-1}, ..., q_1`; it includes the tail-gap cumulative momentum and
excludes `q_0`.  Under total momentum zero, this is exactly the cumulative
tail of the negative reversed left flat frequency.  With the corrected
cumulative-tail convention, this statement is componentwise: for `μ = 0` it is
the ordinary tail-energy identity, and for spatial `μ ≠ 0` the
`-(1 / (2 * Real.pi))` in `section43CumulativeTailMomentumCLE` cancels against
the `-(2 * Real.pi)` in the inverse apply theorem.

For the proof, also name the flat reversal:

```lean
def section43SplitLeftFlat
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    Fin (n * (d + 1)) → ℝ :=
  splitFirst (n * (d + 1)) (r * (d + 1))
    ((castFinCLE
      (by ring : n * (d + 1) + r * (d + 1) = (n + r) * (d + 1))).symm ξ)

def section43SplitRightFlat
    (d n r : ℕ) [NeZero d]
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    Fin (r * (d + 1)) → ℝ :=
  splitLast (n * (d + 1)) (r * (d + 1))
    ((castFinCLE
      (by ring : n * (d + 1) + r * (d + 1) = (n + r) * (d + 1))).symm ξ)

def section43NegRevFlat
    (d n : ℕ) [NeZero d]
    (ξL : Fin (n * (d + 1)) → ℝ) :
    Fin (n * (d + 1)) → ℝ :=
  fun a =>
    let p := finProdFinEquiv.symm a
    - ξL (finProdFinEquiv (Fin.rev p.1, p.2))
```

The required algebra theorem is:

```lean
theorem section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum
    {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hr : 0 < r)
    (hξ_total : section43TotalMomentumFlat d (n + r) ξ = 0) :
    let qξ := section43CumulativeTailMomentumCLE d (n + r) ξ
    let ξL := section43SplitLeftFlat d n r ξ
    (section43CumulativeTailMomentumCLE d n).symm
      (section43LeftBorchersBlock d n r hr qξ)
      =
    section43NegRevFlat d n ξL
```

Proof transcript:

1. For `i : Fin n`, let `ridx := n - 1 - i.val`.  The left flat frequency
   at chronological index `ridx` is the flat difference
   `ξL ridx = qξ ridx - qξ (ridx + 1)`.
2. The cumulative tail of `section43NegRevFlat d n ξL` at `i` is

```text
- ∑_{a = 0}^{ridx} ξL_a.
```

3. Telescope this finite sum to `qξ (ridx + 1) - qξ 0`.
4. Use `hξ_total` to rewrite `qξ 0 = 0`, because `qξ 0` is the total
   momentum.
5. Since `ridx + 1 = n - i.val`, the result is exactly
   `section43LeftBorchersBlock d n r hr qξ i`.
6. Apply the inverse cumulative-tail formula
   `section43CumulativeTailMomentumCLE_symm_apply` to convert equality of
   cumulative tails into equality of flat frequencies.

The positivity theorem for the shifted left block is then easy:

```lean
theorem section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
    {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hr : 0 < r)
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + r)) :
    let qξ := section43CumulativeTailMomentumCLE d (n + r) ξ
    section43LeftBorchersBlock d n r hr qξ ∈
      section43PositiveEnergyRegion d n
```

It uses only the dual-cone half of `hξ`, because
`section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone`
already gives positivity of every `qξ j`, and the left block is a sub-block of
those cumulative momenta.

Finally, the scalar theorem needs the Fourier factorization theorem in exactly
this shape:

```lean
theorem physicsFourier_tensor_borchersConj_eq_frequencyRepresentatives_on_spectralRegion
    {ξ : Fin ((n + r) * (d + 1)) → ℝ}
    (hr : 0 < r)
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + r))
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d r) :
    physicsFourierFlatCLM
      (flattenSchwartzNPoint (d := d)
        (φ.conjTensorProduct ψ)) ξ =
      star
        ((section43FrequencyRepresentative (d := d) n φ)
          (section43LeftBorchersBlock d n r hr
            (section43CumulativeTailMomentumCLE d (n + r) ξ))) *
        ((section43FrequencyRepresentative (d := d) r ψ)
          (section43RightTailBlock d n r
            (section43CumulativeTailMomentumCLE d (n + r) ξ)))
```

Proof transcript:

1. Use the flat Fourier theorem for tensor products after the existing
   left/right block reindex:

```lean
theorem physicsFourierFlatCLM_reindex_tensorProduct_apply
    (F : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
    (G : SchwartzMap (Fin (r * (d + 1)) → ℝ) ℂ)
    (ξ : Fin ((n + r) * (d + 1)) → ℝ) :
    physicsFourierFlatCLM
      (reindexSchwartzFin
        (by ring :
          n * (d + 1) + r * (d + 1) = (n + r) * (d + 1))
        (F.tensorProduct G)) ξ
      =
    physicsFourierFlatCLM F (section43SplitLeftFlat d n r ξ) *
      physicsFourierFlatCLM G (section43SplitRightFlat d n r ξ)
```

   Proof transcript: unfold `physicsFourierFlatCLM_integral`,
   `reindexSchwartzFin_apply`, and `SchwartzMap.tensorProduct_apply`; transport
   the integral through the finite-dimensional product equivalence
   `Fin (n*(d+1)+r*(d+1)) ≃ (Fin (n*(d+1)) → ℝ) ×
   (Fin (r*(d+1)) → ℝ)`; split the exponential with
   `Finset.sum_add_distrib`; apply Fubini and identify the two factor
   integrals with `physicsFourierFlatCLM_integral`.

2. Use this theorem with

```lean
F := flattenSchwartzNPoint (d := d) φ.borchersConj
G := flattenSchwartzNPoint (d := d) ψ
```

   and the pointwise identity

```lean
flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)
  =
reindexSchwartzFin
  (by ring : n * (d + 1) + r * (d + 1) = (n + r) * (d + 1))
  ((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
    (flattenSchwartzNPoint (d := d) ψ))
```

   proved by extensionality, `flattenSchwartzNPoint_apply`,
   `SchwartzMap.conjTensorProduct_apply`, and `SchwartzMap.tensorProduct_apply`.

3. Rewrite the right factor by cumulative-tail inversion:

```lean
section43SplitRightFlat d n r ξ =
  (section43CumulativeTailMomentumCLE d r).symm
    (section43RightTailBlock d n r qξ)
```

   Proof transcript: ext a; write `a` as `(j, μ)` through `finProdFinEquiv`;
   unfold `section43RightTailBlock`,
   `section43CumulativeTailMomentumCLE_symm_apply`, and
   `section43SplitRightFlat`; telescope the full cumulative tail from index
   `n + j`.

4. Rewrite the left factor by the Borchers-conjugation Fourier rule:

```lean
theorem physicsFourierFlatCLM_borchersConj_apply
    (φ : SchwartzNPoint d n)
    (ξL : Fin (n * (d + 1)) → ℝ) :
    physicsFourierFlatCLM
        (flattenSchwartzNPoint (d := d) φ.borchersConj) ξL =
      star
        (physicsFourierFlatCLM
          (flattenSchwartzNPoint (d := d) φ)
          (section43NegRevFlat d n ξL))
```

   Proof transcript: use `physicsFourierFlatCLM_integral`, change variables by
   the flat reversal equivalence induced by `Fin.rev` on the point block, and
   use `map_integral`/`integral_conj` to move `star` outside the integral.
   The exponent changes from `exp(i x·ξL)` to the conjugate of
   `exp(i y·(-rev ξL))`, which is exactly the sign in
   `section43NegRevFlat`.

5. Use
   `section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum` with the
   total-momentum half of `hξ` to identify the argument in step 4 with the
   deterministic representative argument.
6. Unfold `section43FrequencyRepresentative`.

This theorem is the first Lean point at which the product
`star (...) * (...)` is allowed to appear.  Any earlier pointwise product
theorem using `section43LeftRevBlock` instead of
`section43LeftBorchersBlock` is stale and must not be implemented.

Updated implementation order for the left-factor/spectral-support packet:

1. In the Fourier/SCV layer, expose `physicsFourierFlatCLE`,
   `physicsFourierFlatCLM_surjective`, and
   `physicsFourierFlatCLM_reindex_tensorProduct_apply`.
2. In the Section-4.3 transform layer, add
   `section43CumulativeTailMomentumCLE`, its apply/symm theorems,
   `section43FrequencyRepresentative`, and `section43FrequencyProjection`.
3. Add the total-momentum coordinate API:
   `section43TotalMomentumFlat`, `section43TotalMomentumZeroFlat`,
   `section43WightmanSpectralRegion`,
   `section43DiagonalTranslationFlat`,
   `section43DiagonalTranslationFlat_pair_eq_totalMomentum`,
   and `section43TotalMomentumPhaseCLM`.
4. Prove `bvt_W_flat_diagonalTranslate_eq` next to the existing
   `bvt_translation_invariant` bridge, then prove
   `tflat_totalMomentumPhase_invariant_of_bvt_W_translationInvariant` in the
   file that has both `hTflat_bv` and the Fourier translation theorem.
5. In the new Wick-rotation companion
   `Section43SpectralSupport.lean`, prove the OS-specific support-combination
   packet: `zeroHeadBlockShiftCLM`, `zeroHeadSectionCLM`,
   `headBlockBumpExtension`, `section43TotalMomentumZeroProjection`, dual-cone
   preservation for the projection, the zero-head extension theorem, and
   `hasFourierSupportIn_inter_of_dualCone_and_totalMomentumZero`.  Do not
   resurrect the false generic `hasFourierSupportIn_inter_of_closed` route.
6. Strengthen the existing
   `exists_flattened_bvt_W_dualCone_distribution` provider to
   `bvt_W_flattened_distribution_hasFourierSupportIn_wightmanSpectralRegion`.
   Do not replace the old theorem; add the stronger theorem and let consumers
   choose it.
7. Add `section43RightTailBlock`, `section43LeftBorchersBlock`,
   `section43NegRevFlat`, `section43SplitLeftFlat`,
   `section43SplitRightFlat`, and the right/left cumulative-tail inverse
   algebra theorems.
8. Prove `physicsFourierFlatCLM_borchersConj_apply`, then
   `physicsFourier_tensor_borchersConj_eq_frequencyRepresentatives_on_spectralRegion`.
9. Only after steps 1-8 compile should
   `section43_OS24_scalar_interchange_succRight` be implemented.  Its `EqOn`
   set is `section43WightmanSpectralRegion`; its transform hypotheses are
   `hφ_freq`/`hψ_freq`; and its left factor must use
   `section43LeftBorchersBlock`.

The global scalar theorem must then be stated with frequency-projection
transform hypotheses, not raw ambient quotient hypotheses and not canonical
ambient representative equalities:

```lean
section43FrequencyProjection (d := d) n φ =
  section43FourierLaplaceTransformComponent d n f
section43FrequencyProjection (d := d) (m + 1) ψ =
  section43FourierLaplaceTransformComponent d (m + 1) g
```

Here `section43FourierLaplaceTransformComponent` is the actual OS I
`(4.19)-(4.20)` Fourier-Laplace transform into
`Section43PositiveEnergyComponent`.  The current production
`os1TransportComponent` is still the interim quotient-inclusion map
`section43PositiveEnergyQuotientMap.comp subtypeL`; it must not appear as the
right-hand side of the transformed scalar theorem unless it is deliberately
refactored to this Fourier-Laplace meaning.

The corrected theorem slot is scalar/Fourier-side, not pointwise-product, and
its Wightman tests must lie in the transformed image through
`section43FrequencyProjection`:

```lean
private theorem
    section43_OS24_scalar_interchange_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d (m + 1) → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f)
    (hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g)
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat)
    (hTflat_bv :
      ∀ φflat : SchwartzMap
          (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + (m + 1))
          (unflattenSchwartzNPoint (d := d) φflat) =
            Tflat (physicsFourierFlatCLM φflat))
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (KψZ_t : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ)
    (hKψZ_eval :
      ∀ ξ,
        KψZ_t ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ *
              (SchwartzMap.fourierTransformCLM ℂ
                (section43PsiZTimeTest t ht)) τ) :
    Tflat KψZ_t =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1)))
```

This theorem is the Lean form of OS I p. 96 `(4.23) -> (4.24)`.  Its proof must
expand the scalar on both sides to a common integral and perform the order-of-
integration change.  The pointwise `section43OS24Kernel_succRight_visible`
expression is a diagnostic description of the post-interchange integrand, not
a replacement for the scalar theorem above.

Lean-readiness obligations for `section43_OS24_scalar_interchange_succRight`:

1. Start from `hKψZ_eval` and `timeShiftFlatOrbit_apply_phase` only to expose
   the Wightman-side scalar as `Tflat KψZ_t`; do not try to prove a pointwise
   product equality for the Fourier base.
2. Do not use `hTflat_supp` to replace ambient representative values on
   `section43PositiveEnergyRegion`.  Its safe uses are through the general
   `HasFourierSupportIn` EqOn theorem between two explicit
   **frequency-side Schwartz kernels** that agree on
   `section43WightmanSpectralRegion`, or through the existing
   Paley-Wiener/Vladimirov support theorems already used to obtain the
   representation hypothesis.  Any new support use must be written as its own
   lemma.
3. Use `hTflat_bv` for the only allowed bridge from the abstract frequency-side
   distribution `Tflat` back to the actual reconstructed Wightman boundary
   value `bvt_W`.  The theorem is false for an arbitrary supported `Tflat`
   without this representation hypothesis.
4. The second kernel must be built by the OS I `(4.23) -> (4.24)` Fubini
   calculation from the frequency-projection transform equalities `hφ_freq`
   and `hψ_freq`, together with the real
   `section43FourierLaplaceTransformComponent` apply theorem.  It may
   contain the visible factors
   `star ((section43FrequencyRepresentative d n φ)
      (section43LeftBorchersBlock ... qξ))` and
   `(section43FrequencyRepresentative d (m + 1) ψ)
      (section43RightTailBlock ... qξ)` only after the scalar interchange has
   supplied them.
5. The required OS I Fubini theorem must mention the cumulative-tail momentum
   map `section43CumulativeTailMomentum`, the spectral-support set
   `section43WightmanSpectralRegion`, the support theorem
   `section43CumulativeTailMomentum_mem_positiveEnergy_of_mem_dualCone`, and
   the global cutoff kernel `section43PsiZTimeTest`.  The naked exponential is
   only a spectral-region normal form, not the global Schwartz kernel.
6. Both visible frequency factors use the basic
   `section43FourierLaplaceRepresentative_apply` theorem.  The later
   descended-`ψ_Z` Packet-H theorem is not a dependency of the scalar OS I
   Fubini theorem.  The left factor must be evaluated at
   `section43LeftBorchersBlock ... qξ` after the total-momentum theorem has
   identified that shifted block with the negative reversed left flat
   frequency.  A proof using `section43LeftRevBlock ... qξ` is the stale
   OS-1 error and is not implementation-ready.
7. The scalar OS I Fubini theorem is decomposed in §5.9.2d into S1-S5.
   Packet S5 is the only place where the `Tflat` Fourier-Laplace witness is
   converted to the Euclidean `OS.S` scalar.  Production may start only with
   those named support packets; it must not revive the old pointwise supplier
   body.

After the scalar OS I interchange theorem is available, the hPsi proof has the
required non-wrapper shape:

```lean
obtain ⟨Tflat, hTflat_supp, hTflat_bv⟩ := ...
obtain ⟨KψZ_t, hKψZ_eval, hKψZ_pair⟩ :=
  exists_timeShiftKernel_pairing_fourierTest ... χ Tflat hTflat_bv
let N : ℂ := Tflat KψZ_t
have hW_nf : WightmanFourierTestedScalar = N := by
  simpa [N] using hKψZ_pair
have hOS_nf : N = OSSemigroupScalar := by
  simpa [N] using
    section43_OS24_scalar_interchange_succRight
      (d := d) OS lgc φ ψ hψ_compact f g hg_compact hφ_freq hψ_freq ht
      Tflat hTflat_supp hTflat_bv KψZ_t hKψZ_eval
exact hW_nf.trans hOS_nf
```

The conversion from this `OS.S` scalar to the current semigroup/spectral
consumer is then the already-public real-axis bridge

```lean
OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
```

followed, when needed by the downstream theorem surface, by
`OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`.
This conversion is formal and should not be folded into the OS I Fubini
theorem.

There may still be an internal `EqOn` step inside
`section43_OS24_scalar_interchange_succRight`, but it must be between two
frequency-side Schwartz kernels constructed by the OS I scalar Fubini proof.
It must not be an external direct EqOn proof from `hφ`/`hψ` alone.

This changes the readiness status of the successor-right theorem: the
right-tail transformed factor and the flat-frequency-to-Section-4.3 `q`
conversion are implementation-ready as support packets, but the global hPsi
scalar is still not allowed to be implemented directly from this paragraph
alone.  The following subsection is the Lean-level scalar Fubini packet that
must be in place before the final theorem is touched.  Its job is to replace
the dangerous phrase "prove `(4.23) -> (4.24)` by Fubini" with named
frequency-side kernels, support-EqOn uses, and scalar normal forms.

### 5.9.2d. Lean-ready scalar OS I Fubini packet

The scalar interchange must be decomposed into five implementation packets.
This is the hard rule for avoiding the old rushed-production failure mode:
only Packet S5 is allowed to identify the frequency-side scalar with the
Euclidean OS scalar, and the final
`section43_OS24_scalar_interchange_succRight` is formal from S1-S5.
Each earlier packet exposes one genuine mathematical ingredient.

#### Packet S1: collapse the `ψ_Z` time-shift kernel at a frozen frequency

For `N := n + (m + 1)`, first expose the positive-imaginary-axis test as a
named definition so later theorem statements do not carry anonymous
`SCV.schwartzPsiZ ...` terms:

```lean
noncomputable def section43PsiZTimeTest (t : ℝ) (ht : 0 < t) :
    SchwartzMap ℝ ℂ :=
  SCV.schwartzPsiZ
    (((2 * Real.pi : ℂ) * (t * Complex.I)))
    (by
      simpa [Complex.mul_im, ht.ne']
        using mul_pos Real.two_pi_pos ht)
```

the first theorem is a pointwise statement about the already-constructed
kernel from `exists_timeShiftKernel_pairing_fourierTest`.  It does **not**
mention OS.S and it does **not** use `section43FrequencyProjection`.

```lean
private theorem
    section43_timeShiftKernel_psiZ_pointwise_eq_damped_base_succRight
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t)
    (KψZ_t : SchwartzMap
      (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ)
    (hKψZ_eval :
      ∀ ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ,
        KψZ_t ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ *
              (SchwartzMap.fourierTransformCLM ℂ
                (section43PsiZTimeTest t ht)) τ)
    {ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ}
    (hξ_dual :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
          ForwardConeAbs d (n + (m + 1)))) :
    let base : ℂ :=
      physicsFourierFlatCLM
        (OSReconstruction.reindexSchwartzFin
          (Nat.add_mul n (m + 1) (d + 1)).symm
          (((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
            (flattenSchwartzNPoint (d := d) ψ)))) ξ
    let lamξ : ℝ :=
      ∑ i,
        (((OSReconstruction.castFinCLE
            (Nat.add_mul n (m + 1) (d + 1)).symm)
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := (m + 1) * (d + 1))
            (flatTimeShiftDirection d (m + 1)))) i) * ξ i
    let ηξ : ℝ := -lamξ / (2 * Real.pi)
    KψZ_t ξ =
      base * Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ))
```

Proof transcript:

1. Set local names `base`, `lamξ`, and `ηξ`.
2. Rewrite `KψZ_t ξ` by `hKψZ_eval ξ`.
3. Rewrite the integrand with `timeShiftFlatOrbit_apply_phase`, then factor
   out `base` by `MeasureTheory.integral_const_mul`.
4. Use the fixed-frequency Fourier inversion lemma
   `horizontalPhasePairingCLM_fourierTransform` in the special case
   `χ := section43PsiZTimeTest t ht`.  If it is still private, move it
   unchanged to the smallest support file that already imports the Fourier
   transform facts; do not duplicate its proof in
   `OSToWightmanPositivity.lean`.
5. The result is
   `base * section43PsiZTimeTest t ht ηξ`.  Prove `0 ≤ ηξ` by
   `horizontalPaley_frequency_nonneg_of_mem_dualCone` specialized to right
   degree `m + 1`.
6. Rewrite `section43PsiZTimeTest t ht ηξ` using
   `SCV.schwartzPsiZ_apply` and `SCV.psiZ_eq_exp_of_nonneg`.
7. Close the scalar exponent by `ring_nf`/`ring`, keeping the definition of
   `ηξ` unfolded only at the final algebra step.

This packet is the only place where the external semigroup time `t` enters
the frequency-side normal form.  The spectral height is `ηξ`; it is **not**
the same variable as `t`.

#### Packet S2: factor the frozen full-flat base on the Wightman spectral region

The second theorem is the corrected replacement for every stale pointwise
Fourier-base-to-product draft.  It is permitted only on
`section43WightmanSpectralRegion`, because the left Borchers factor needs
total-momentum support.

```lean
private theorem
    physicsFourierFlatCLM_borchersTensor_eq_frequencyRepresentatives_on_spectralRegion
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    let qξ :=
      section43CumulativeTailMomentum d (n + (m + 1)) ξ
    physicsFourierFlatCLM
      (OSReconstruction.reindexSchwartzFin
        (Nat.add_mul n (m + 1) (d + 1)).symm
        (((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
          (flattenSchwartzNPoint (d := d) ψ)))) ξ =
      star
        ((section43FrequencyRepresentative (d := d) n φ)
          (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
        (section43FrequencyRepresentative (d := d) (m + 1) ψ)
          (section43RightTailBlock d n (m + 1) qξ)
```

Proof transcript:

1. Split `hξ` into `hξ_dual` and `hξ_total`.
2. Put `qξ := section43CumulativeTailMomentum d (n + (m + 1)) ξ`.
3. Use `physicsFourierFlatCLM_reindex_tensorProduct_apply` to factor the
   full flattened transform into left and right flat Fourier transforms.  The
   split variables must be named by `section43SplitLeftFlat` and
   `section43SplitRightFlat`.
4. Use `physicsFourierFlatCLM_borchersConj_apply` on the left factor.  The
   theorem must state the output as the complex conjugate of the original
   frequency representative evaluated at `section43NegRevFlat`.
5. Use
   `section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum` with
   `hξ_total` to rewrite `section43NegRevFlat` to
   `section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ`.
6. Use the right cumulative-tail inverse theorem to rewrite the right flat
   split variable to `section43RightTailBlock d n (m + 1) qξ`.
7. Unfold only `section43FrequencyRepresentative` at the end.  Do not unfold
   `section43FrequencyProjection`; this theorem is about deterministic
   representatives, not quotient classes.

Required coordinate helper slots before S2:

```lean
def section43SplitLeftFlat
def section43SplitRightFlat
def section43NegRevFlat
def section43LeftBorchersBlock

theorem section43SplitRightFlat_eq_cumulativeTail_rightTail
theorem section43NegRevFlat_eq_cumulativeTail_leftBorchers_of_totalMomentum
theorem section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum
theorem section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
theorem section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
```

The `section43RightTailBlock` positivity theorem may be a one-line wrapper
around the already implemented positive-energy block theorem plus
`section43CumulativeTailMomentum_mem_positiveEnergy_of_mem_dualCone`; it is
allowed because it packages the exact `section43WightmanSpectralRegion`
surface consumed by S2.

Production status, 2026-04-15: the first lightweight factorization coordinate
packet is implemented in the new file
`Section43SpectralFactorization.lean` and exact-checks:

```lean
section43SplitLeftFlat
section43SplitRightFlat
section43NegRevFlat
section43LeftBorchersBlock
section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion
section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion
```

The inverse cumulative-tail coordinate lemmas are **not** implementation-ready
as one-line `simp` proofs.  The next proof-doc gap is the finite-sum reindex
packet needed for:

```lean
section43CumulativeTailMomentumCLE_splitRightFlat
section43CumulativeTailMomentumCLE_negRevFlat_splitLeft_of_totalMomentum
section43SplitRightFlat_eq_cumulativeTail_rightTail
section43LeftBorchersBlock_symm_eq_negRevFlat_of_totalMomentum
```

The right helper reduces componentwise to the reindex identity

```text
∑ x : Fin r, if j ≤ x then ξ_{n+x,μ} else 0
=
∑ y : Fin (n+r), if n+j ≤ y then ξ_{y,μ} else 0.
```

The left helper reduces componentwise to

```text
∑ x : Fin n, if j ≤ x then -ξ_{n-1-x,μ} else 0
=
∑ y : Fin (n+r), if n ≤ y+j then ξ_{y,μ} else 0,
```

using total momentum zero to replace the missing prefix by the negative tail.
The Lean-ready next documentation task is to state and prove these two finite
`Fin` sum reindex lemmas explicitly, preferably in
`Section43SpectralFactorization.lean` before exposing the inverse CLE theorems.

#### Packet S3: derive representative normal forms from the transform hypotheses

The transform hypotheses in the scalar theorem are quotient-valued.  They
must be converted once, up front, into deterministic representative predicates:

```lean
have hφ_rep :
    section43FourierLaplaceRepresentative d n f
      (section43FrequencyRepresentative (d := d) n φ) :=
  section43FrequencyRepresentative_is_fourierLaplaceRepresentative
    (d := d) (n := n) φ f hφ_freq

have hψ_rep :
    section43FourierLaplaceRepresentative d (m + 1) g
      (section43FrequencyRepresentative (d := d) (m + 1) ψ) :=
  section43FrequencyRepresentative_is_fourierLaplaceRepresentative
    (d := d) (n := m + 1) ψ g hψ_freq
```

The left factor normal form is:

```lean
private theorem
    section43_leftBorchers_frequencyRepresentative_eq_fourierLaplaceIntegral
    {n m : ℕ}
    (φ : SchwartzNPoint d n)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    {q : NPointDomain d (n + (m + 1))}
    (hq :
      q ∈ section43PositiveEnergyRegion d (n + (m + 1)))
    (hq_left :
      section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q ∈
        section43PositiveEnergyRegion d n) :
    (section43FrequencyRepresentative (d := d) n φ)
      (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q) =
    section43FourierLaplaceIntegral d n f
      (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) q)
```

Proof: exact `section43FourierLaplaceRepresentative_apply` with `hq_left`.

The right factor normal form for the scalar OS I `(4.24)` theorem is the same
basic representative-apply theorem, not the descended-`ψ_Z` Packet-H theorem:

```lean
private theorem
    section43_rightTail_frequencyRepresentative_eq_fourierLaplaceIntegral
    {n m : ℕ}
    (ψ : SchwartzNPoint d (m + 1))
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {q : NPointDomain d (n + (m + 1))}
    (hq :
      q ∈ section43PositiveEnergyRegion d (n + (m + 1)))
    (hq_right :
      section43RightTailBlock d n (m + 1) q ∈
        section43PositiveEnergyRegion d (m + 1)) :
    (section43FrequencyRepresentative (d := d) (m + 1) ψ)
      (section43RightTailBlock d n (m + 1) q) =
    section43FourierLaplaceIntegral d (m + 1) g
      (section43RightTailBlock d n (m + 1) q)
```

Proof: exact `section43FourierLaplaceRepresentative_apply` with `hq_right`.

This correction removes a fake zero-height blocker from the scalar theorem.
The already implemented
`section43FourierLaplaceRepresentative_rightTailBlock_eq_iterated_descendedPsiZ_of_height`
is still valuable, but it belongs to the later descended-`ψ_Z`/hPsi consumer,
where a positive imaginary height is genuinely present.  It is not a
dependency of `section43OS24Kernel_pairing_eq_osScalar_succRight`.

#### Packet S4: global kernel and spectral-support EqOn

After S1-S3 are proved, first prove an existence theorem for the visible
kernel as a real `SchwartzMap`.  The pointwise formula alone is not enough:
the object passed to `Tflat` must live in the Schwartz space.

```lean
private theorem exists_section43OS24Kernel_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (t : ℝ) (ht : 0 < t) :
    ∃ KOS : SchwartzMap
      (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ,
      ∀ ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ,
        let qξ := section43CumulativeTailMomentum d (n + (m + 1)) ξ
        let lamξ : ℝ :=
          ∑ i,
            (((OSReconstruction.castFinCLE
                (Nat.add_mul n (m + 1) (d + 1)).symm)
              (OSReconstruction.zeroHeadBlockShift
                (m := n * (d + 1)) (n := (m + 1) * (d + 1))
                (flatTimeShiftDirection d (m + 1)))) i) * ξ i
        let ηξ : ℝ := -lamξ / (2 * Real.pi)
        KOS ξ =
          (section43PsiZTimeTest t ht) ηξ *
            (star
              ((section43FrequencyRepresentative (d := d) n φ)
                (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
              (section43FrequencyRepresentative (d := d) (m + 1) ψ)
                (section43RightTailBlock d n (m + 1) qξ))
```

Proof transcript for `exists_section43OS24Kernel_succRight`:

1. Build the scalar multiplier
   `ξ ↦ (section43PsiZTimeTest t ht) ηξ` by composing the Schwartz function
   `section43PsiZTimeTest t ht : SchwartzMap ℝ ℂ` with the continuous linear
   functional `ξ ↦ ηξ`.  Do **not** use the naked exponential globally: it has
   the right formula only on the spectral cone and may grow in off-cone
   directions.
2. The left and right factors are Schwartz because they are compositions of
   `section43FrequencyRepresentative` with continuous linear maps
   `section43LeftBorchersBlock ∘ section43CumulativeTailMomentum` and
   `section43RightTailBlock ∘ section43CumulativeTailMomentum`.
3. Multiply the three Schwartz factors using the existing Schwartz algebra
   product theorem.  If the product theorem is not exposed as a CLM, first add
   the smallest local theorem that turns pointwise products of two
   `SchwartzMap`s into a `SchwartzMap`.
4. Return the constructed `KOS` and close its pointwise formula by extensional
   unfolding only.  Do not use `Classical.choose` until this existence theorem
   has the visible formula in its conclusion.

Then define the kernel by choice and expose only the pointwise theorem:

```lean
noncomputable def section43OS24Kernel_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (t : ℝ) (ht : 0 < t) :
    SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ :=
  Classical.choose
    (exists_section43OS24Kernel_succRight d n m φ ψ t ht)
```

```lean
theorem section43OS24Kernel_succRight_apply
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) :
    let qξ := section43CumulativeTailMomentum d (n + (m + 1)) ξ
    let lamξ : ℝ :=
      ∑ i,
        (((OSReconstruction.castFinCLE
            (Nat.add_mul n (m + 1) (d + 1)).symm)
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := (m + 1) * (d + 1))
            (flatTimeShiftDirection d (m + 1)))) i) * ξ i
    let ηξ : ℝ := -lamξ / (2 * Real.pi)
    section43OS24Kernel_succRight d n m φ ψ t ht ξ =
      (section43PsiZTimeTest t ht) ηξ *
        (star
          ((section43FrequencyRepresentative (d := d) n φ)
            (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
          (section43FrequencyRepresentative (d := d) (m + 1) ψ)
            (section43RightTailBlock d n (m + 1) qξ))
```

Proof: this is `Classical.choose_spec
  (exists_section43OS24Kernel_succRight d n m φ ψ t ht) ξ`.

Then S1 and S2 give the support EqOn theorem:

```lean
private theorem
    section43_timeShiftKernel_psiZ_eq_OS24Kernel_on_spectralRegion_succRight
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {t : ℝ} (ht : 0 < t)
    (KψZ_t : SchwartzMap
      (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ)
    (hKψZ_eval :
      ∀ ξ,
        KψZ_t ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ *
              (SchwartzMap.fourierTransformCLM ℂ
                (section43PsiZTimeTest t ht)) τ) :
    Set.EqOn
      (fun ξ => KψZ_t ξ)
      (fun ξ => section43OS24Kernel_succRight d n m φ ψ t ht ξ)
      (section43WightmanSpectralRegion d (n + (m + 1)))
```

Proof transcript:

1. Introduce `ξ hξ`; split `hξ` into dual-cone and total-momentum parts.
2. Apply S1 using the dual-cone part.
3. Rewrite `base` by S2 using the full spectral-region hypothesis.
4. Rewrite the target with `section43OS24Kernel_succRight_apply`.
5. Use `horizontalPaley_frequency_nonneg_of_mem_dualCone` and
   `SCV.psiZ_eq_exp_of_nonneg` to replace
   `(section43PsiZTimeTest t ht) ηξ` by
   `Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ))` on the spectral region.
6. Close by associativity/commutativity of scalar multiplication only; do not
   unfold the definitions of the left/right blocks.

#### Packet S5: OS scalar recognition by the `bvt_F` Fourier-Laplace shell

The equality

```lean
Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) =
  OS.S (n + (m + 1))
    (ZeroDiagonalSchwartz.ofClassical
      (f.1.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t g.1)))
```

is not a definitional unfolding of `OS.S`.  `OS.S` is an abstract Schwinger
distribution; it can only be recognized through the already compiled Euclidean
restriction / `xiShift` bridge for the chosen continuation `bvt_F`.  Therefore
Packet S5 must consume a full Fourier-Laplace witness for the same flattened
distribution `Tflat`, not just the boundary-value equality `hTflat_bv`.

Use the following local structure to keep theorem statements readable without
hiding any data:

```lean
private structure section43TflatFourierLaplaceWitness
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (N : ℕ)
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ) where
  hCflat_open :
    IsOpen
      ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
  hCflat_conv :
    Convex ℝ
      ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
  hCflat_cone :
    IsCone
      ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
  hCflat_salient :
    IsSalientCone
      ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
  hFL :
    ∀ z : Fin N → Fin (d + 1) → ℂ,
      z ∈ TubeDomainSetPi (ForwardConeAbs d N) →
        bvt_F OS lgc N z =
          fourierLaplaceExtMultiDim
            ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            Tflat (flattenCLEquiv N (d + 1) z)
```

The implementation must obtain the `Tflat` data from the existing witness
packet, or first prove a uniqueness theorem deriving the same data from
`hTflat_bv` plus Fourier support:

```lean
obtain
  ⟨Tflat, hCflat_open, hCflat_conv, hCflat_cone, hCflat_salient,
    hTflat_dualSupp, hTflat_bv, hTflat_FL⟩ :=
  exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr
    (d := d) OS lgc (n + (m + 1))
```

Then set

```lean
let hTflat_FL :
    section43TflatFourierLaplaceWitness
      (d := d) OS lgc (n + (m + 1)) Tflat :=
  ⟨hCflat_open, hCflat_conv, hCflat_cone, hCflat_salient, hTflat_FL⟩
```

If a local theorem is already passed an arbitrary `Tflat`, its statement is
not implementation-ready unless it also receives this `hTflat_FL` datum or a
proved lemma

```lean
section43Tflat_fourierLaplaceRep_of_boundaryValue_unique
```

which recovers `hTflat_FL` from the boundary-value identity and support.
Do not prove S5 for an unconstrained `Tflat`; that would leave the OS scalar
unconnected to the actual analytic continuation.

S5 is split into four non-wrapper theorems.

Important correction, 2026-04-14: the tempting support lemma

```lean
xiShift ... (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I) ∈
  TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))
```

for `y ∈ support (f.1.osConjTensorProduct g.1)` is false when `n > 0`.
The OS-conjugated left block is supported at negative Euclidean times.  In the
one-left/one-right case, `y₀⁰ < 0`, so the first Wick-rotated imaginary time is
negative and no right-tail `xiShift` can put the raw configuration in the
forward tube.  Therefore the Fourier-Laplace witness `hTflat_FL.hFL` must
never be applied directly to the raw OS `xiShift` shell.

The correct route is:

1. Keep the raw `xiShift` shell only for the already compiled Schwinger scalar
   bridge `bvt_F_osConjTensorProduct_timeShift_eq_xiShift`.
2. Before using the Fourier-Laplace witness, replace the raw OS shell pointwise
   by a Borchers-ordered, globally translated forward-tube lift.  The
   replacement uses `bvt_F_perm` and `bvt_F_translationInvariant`, not support
   membership of the raw shell.
3. On the frequency side, the translated lift has the same exponential phase
   as the OS I `(4.24)` kernel on `section43WightmanSpectralRegion`; the
   global translation phase disappears exactly because this support set includes
   `section43TotalMomentumZeroFlat`.
4. Then `hTflat_FL.hFL` and `multiDimPsiZExt_apply_of_mem_dualCone` are applied
   only to honest forward-tube points.

The support subpacket is now:

```lean
private def section43RawXiShiftConfig_succRight
    {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)

private def section43LeftBlockReversePerm_succRight
    (n m : ℕ) :
    Equiv.Perm (Fin (n + (m + 1))) where
  toFun i :=
    if hi : i.val < n then
      Fin.castAdd (m + 1) (Fin.rev ⟨i.val, hi⟩)
    else i
  invFun i :=
    if hi : i.val < n then
      Fin.castAdd (m + 1) (Fin.rev ⟨i.val, hi⟩)
    else i
  left_inv := by
    intro i
    by_cases hi : i.val < n
    · simp [hi, Fin.rev_rev]
    · simp [hi]
  right_inv := by
    intro i
    by_cases hi : i.val < n
    · simp [hi, Fin.rev_rev]
    · simp [hi]

@[simp] theorem section43LeftBlockReversePerm_succRight_castAdd
    (n m : ℕ) (i : Fin n) :
    section43LeftBlockReversePerm_succRight n m
        (Fin.castAdd (m + 1) i) =
      Fin.castAdd (m + 1) (Fin.rev i)

@[simp] theorem section43LeftBlockReversePerm_succRight_natAdd
    (n m : ℕ) (j : Fin (m + 1)) :
    section43LeftBlockReversePerm_succRight n m
        (Fin.natAdd n j) =
      Fin.natAdd n j

private def section43OSBorchersTimeShiftConfig_succRight
    {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  fun i =>
    section43RawXiShiftConfig_succRight (d := d) t y
      (section43LeftBlockReversePerm_succRight n m i)

private def section43FirstIndex_succRight
    {n m : ℕ} : Fin (n + (m + 1)) :=
  ⟨0, by omega⟩

private def section43OSForwardTubeLiftTranslation_succRight
    {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (d + 1) → ℂ :=
  fun μ =>
    if μ = 0 then
      Complex.I *
        (((1 : ℝ) -
          (section43OSBorchersTimeShiftConfig_succRight (d := d) t y
            section43FirstIndex_succRight 0).im : ℝ) : ℂ)
    else 0

private def section43OSForwardTubeLift_succRight
    {n m : ℕ} (t : ℝ)
    (y : NPointDomain d (n + (m + 1))) :
    Fin (n + (m + 1)) → Fin (d + 1) → ℂ :=
  fun i =>
    section43OSBorchersTimeShiftConfig_succRight (d := d) t y i +
      section43OSForwardTubeLiftTranslation_succRight (d := d) t y
```

Implementation notes:

1. `section43LeftBlockReversePerm_succRight` fixes the right tail and maps the
   new left index `Fin.castAdd (m + 1) i` to
   `Fin.castAdd (m + 1) (Fin.rev i)`.  Its right-tail branch is the identity on
   `Fin.natAdd n j`.  Prove simp theorems for these two branches before using
   it in any analytic proof.
2. `section43OSBorchersTimeShiftConfig_succRight` is exactly the raw OS
   `xiShift` shell after that left-block reversal.  The tail shift by `t` is
   already part of `section43RawXiShiftConfig_succRight`.
3. `section43OSForwardTubeLiftTranslation_succRight` translates only the time
   coordinate, with time component
   `Complex.I * (1 - (section43OSBorchersTimeShiftConfig_succRight t y 0 0).im)`.
   After translation, the first imaginary time is exactly `1`, and all
   consecutive imaginary-time gaps are the same as in the Borchers-ordered raw
   configuration.
4. The compact hypotheses used by `lemma42_matrix_element_time_interchange`
   must be threaded into this packet.  With `hf_compact` and `hg_compact`, the
   scalar density has compact support; the translated lift has a uniform
   positive cone margin on that compact support, so the Bochner/Fubini kernel
   can be built with compact-support integrability rather than a fragile global
   near-boundary estimate.

The required geometry theorems are:

```lean
private theorem
    section43OSConjTensorProduct_support_left_reflected_ordered_succRight
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    timeReflectionN d (splitFirst n (m + 1) y) ∈
      OrderedPositiveTimeRegion d n

private theorem
    section43OSConjTensorProduct_support_right_ordered_succRight
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    splitLast n (m + 1) y ∈
      OrderedPositiveTimeRegion d (m + 1)

private theorem
    section43OSBorchersTimeShiftConfig_strictOrdered_of_osSupport_succRight
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    StrictMono
      (fun i : Fin (n + (m + 1)) =>
        (section43OSBorchersTimeShiftConfig_succRight
          (d := d) t y i 0).im)

private theorem
    section43OSForwardTubeLift_mem_forwardTube_of_osSupport_succRight
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    {y : NPointDomain d (n + (m + 1))}
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    section43OSForwardTubeLift_succRight (d := d) t y ∈
      TubeDomainSetPi (ForwardConeAbs d (n + (m + 1)))
```

Proof transcript:

1. For
   `section43OSConjTensorProduct_support_left_reflected_ordered_succRight`,
   unfold `SchwartzNPoint.osConjTensorProduct` and
   `SchwartzMap.tensorProduct_apply` at `y`.  From `hy : product ≠ 0`, derive
   `f.1.osConj (splitFirst n (m + 1) y) ≠ 0` by `mul_ne_zero`.  Unfold
   `SchwartzNPoint.osConj_apply`, remove `star` from the nonzero statement,
   and use
   `subset_tsupport _ (Function.mem_support.mpr ...)` plus `f.2` to obtain
   `timeReflectionN d (splitFirst n (m + 1) y) ∈ OrderedPositiveTimeRegion d n`.
2. The right ordered-support theorem is identical but uses the right factor
   `g.1 (splitLast n (m + 1) y) ≠ 0` and then `g.2`.
3. For the left block in
   `section43OSBorchersTimeShiftConfig_strictOrdered_of_osSupport_succRight`,
   the ordered reflected theorem gives, for `i : Fin n`,
   `0 < -(splitFirst n (m + 1) y i 0)` and hence
   `splitFirst n (m + 1) y i 0 < 0`.  If `i < j`, it also gives
   `splitFirst n (m + 1) y j 0 < splitFirst n (m + 1) y i 0`.
   Compose this with `Fin.rev`: `i < j` implies `Fin.rev j < Fin.rev i`, so
   the raw left times read in `Fin.rev` order are strictly increasing.
4. For the right block, the ordered-support theorem for `g` gives
   `0 < splitLast n (m + 1) y j 0` and strict increase in `j`; the `xiShift`
   adds the same imaginary time `t` to every right-tail point, so strict order
   within the right block is unchanged.
5. The boundary comparison is strict because the last reversed-left raw time
   is `splitFirst n (m + 1) y 0 0 < 0`, while the first right-tail shifted time
   is `splitLast n (m + 1) y 0 0 + t`, which is positive by right support and
   `ht`.
6. The global translation makes the first imaginary time `1` and preserves
   every consecutive gap.  Define the real configuration

```lean
let xs : NPointDomain d (n + (m + 1)) :=
  fun i μ =>
    if μ = 0 then
      (section43OSForwardTubeLift_succRight (d := d) t y i 0).im
    else
      (section43OSForwardTubeLift_succRight (d := d) t y i μ).re
```

   Prove
   `section43OSForwardTubeLift_succRight (d := d) t y =
      fun i => wickRotatePoint (xs i)` by extensionality, using that the lift
   translation is purely imaginary in the time coordinate and zero in spatial
   coordinates.  Then apply `euclidean_ordered_in_forwardTube xs` with
   `hpos` from the first-time normalization and strict-order preservation.

The frequency-side phase theorem is the following exact integral equality:

```lean
def section43ComplexDiagonalTranslationFlat
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℂ) : Fin (N * (d + 1)) → ℂ :=
  fun i =>
    let p := finProdFinEquiv.symm i
    a p.2

theorem section43ComplexDiagonalTranslationFlat_pair_eq_totalMomentum
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℂ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    (∑ i : Fin (N * (d + 1)),
        section43ComplexDiagonalTranslationFlat d N a i * (ξ i : ℂ))
      =
    ∑ μ : Fin (d + 1),
      a μ * (section43TotalMomentumFlat d N ξ μ : ℂ)

private theorem
    section43OSForwardTubeLift_phase_cancel_of_totalMomentumZero_succRight
    {n m : ℕ}
    (t : ℝ)
    (y : NPointDomain d (n + (m + 1)))
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ_zero :
      ξ ∈ section43TotalMomentumZeroFlat d (n + (m + 1))) :
    Complex.exp
      (Complex.I *
        ∑ i : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSForwardTubeLift_succRight (d := d) t y) i *
            (ξ i : ℂ)) =
    Complex.exp
      (Complex.I *
        ∑ i : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight (d := d) t y) i *
            (ξ i : ℂ))

private theorem
    section43OSForwardTubeLift_multiDimPsiZExt_apply_of_spectralRegion_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1)))
    (y : NPointDomain d (n + (m + 1)))
    (hy :
      y ∈ Function.support
        ((f.1.osConjTensorProduct g.1) :
          NPointDomain d (n + (m + 1)) → ℂ)) :
    multiDimPsiZExt
      ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
        ForwardConeAbs d (n + (m + 1)))
      hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
      hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
      (flattenCLEquiv (n + (m + 1)) (d + 1)
        (section43OSForwardTubeLift_succRight (d := d) t y)) ξ =
    Complex.exp
      (Complex.I *
        ∑ i : Fin ((n + (m + 1)) * (d + 1)),
          flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSBorchersTimeShiftConfig_succRight (d := d) t y) i *
            (ξ i : ℂ))

private theorem
    section43OSForwardTubeLiftKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    (∫ y : NPointDomain d (n + (m + 1)),
        multiDimPsiZExt
          ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
            ForwardConeAbs d (n + (m + 1)))
          hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
          hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
          (flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
        (f.1.osConjTensorProduct g.1) y) =
      section43OS24Kernel_succRight d n m φ ψ t ht ξ
```

Proof uses:

1. `multiDimPsiZExt_apply_of_mem_dualCone` with the dual-cone component of
   `hξ`.
2. `section43OSForwardTubeLift_phase_cancel_of_totalMomentumZero_succRight` to
   cancel the y-dependent global translation phase.  The cancellation proof is
   just `section43ComplexDiagonalTranslationFlat_pair_eq_totalMomentum` followed
   by the `section43TotalMomentumZeroFlat` component of `hξ`.
3. The left Borchers reversal theorem from §5.9.2c to rewrite the reflected
   left factor as the left `section43FrequencyRepresentative` block.
4. `section43_leftBorchers_frequencyRepresentative_eq_fourierLaplaceIntegral`
   for the left factor and
   `section43_rightTail_frequencyRepresentative_eq_fourierLaplaceIntegral`
   for the right tail.  Do not use the descended-`ψ_Z` Packet-H theorem in
   this scalar recognition step.
5. `section43OS24Kernel_succRight_apply` to close.

The preceding five-line proof outline is not detailed enough for production.
The implementation must expose the scalar expansion as a named theorem before
using it inside the `multiDimPsiZExt` proof:

```lean
private theorem
    section43TailShiftPhase_eq_psiZTimeTest_of_spectralRegion_succRight
    {n m : ℕ}
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    let lamξ : ℝ :=
      ∑ i,
        (((OSReconstruction.castFinCLE
            (Nat.add_mul n (m + 1) (d + 1)).symm)
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := (m + 1) * (d + 1))
            (flatTimeShiftDirection d (m + 1)))) i) * ξ i
    let ηξ : ℝ := -lamξ / (2 * Real.pi)
    Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) =
      section43PsiZTimeTest t ht ηξ
```

Proof transcript:

1. Obtain `hξ_dual := hξ.1`.
2. Prove `0 ≤ ηξ` using the same theorem as S1,
   `horizontalPaley_frequency_nonneg_of_mem_dualCone`, specialized to the
   right-tail shift functional
   `zeroHeadBlockShift (flatTimeShiftDirection d (m + 1))`.
3. Rewrite `section43PsiZTimeTest t ht ηξ` by `SCV.schwartzPsiZ_apply` and
   `SCV.psiZ_eq_exp_of_nonneg`.
4. Close by the algebra used in S1: unfold `section43PsiZTimeTest` and `ηξ`
   only at the final step, then `ring_nf`.

Then name the full scalar factorization of the Borchers-ordered phase:

```lean
private theorem
    section43OSBorchersPhaseKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    (∫ y : NPointDomain d (n + (m + 1)),
        Complex.exp
          (Complex.I *
            ∑ i : Fin ((n + (m + 1)) * (d + 1)),
              flattenCLEquiv (n + (m + 1)) (d + 1)
                (section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y) i *
                (ξ i : ℂ)) *
        (f.1.osConjTensorProduct g.1) y) =
      section43OS24Kernel_succRight d n m φ ψ t ht ξ
```

Proof transcript:

1. Set `N := n + (m + 1)` and
   `qξ := section43CumulativeTailMomentum d N ξ`.
2. Use the split equivalence
   `NPointDomain d N ≃ NPointDomain d n × NPointDomain d (m + 1)` to rewrite
   the `y`-integral as an iterated integral over left and right variables.
3. Unfold `SchwartzNPoint.osConjTensorProduct`: the density becomes
   `star (f.1 (timeReflectionN d yL)) * g.1 yR`.
4. Use the coordinate lemmas for `section43OSBorchersTimeShiftConfig_succRight`
   to split the exponential into three factors:
   the external tail-shift phase
   `Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ))`, the left reflected
   Fourier-Laplace kernel at
   `section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ`, and the right
   Fourier-Laplace kernel at
   `section43RightTailBlock d n (m + 1) qξ`.
5. Move the tail-shift phase outside the integral by
   `MeasureTheory.integral_const_mul`.
6. Factor the product integral using the product-measure/Fubini theorem for
   the split equivalence.  The left factor is conjugated because of
   `star (f.1 (timeReflectionN d yL))`; the right factor is unchanged.
7. Rewrite the left factor by
   `section43_leftBorchers_frequencyRepresentative_eq_fourierLaplaceIntegral`
   and the right factor by
   `section43_rightTail_frequencyRepresentative_eq_fourierLaplaceIntegral`.
   The required positive-energy hypotheses are
   `section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion` and
   `section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion`.
8. Rewrite the external phase with
   `section43TailShiftPhase_eq_psiZTimeTest_of_spectralRegion_succRight`.
9. Close by `section43OS24Kernel_succRight_apply`.

If step 4 is not a one-screen proof, split it into these coordinate theorem
slots before touching the scalar theorem:

```lean
private theorem
    section43OSBorchersPhase_tailShiftFactor_succRight
private theorem
    section43OSBorchersPhase_leftFactor_eq_fourierLaplaceKernel_succRight
private theorem
    section43OSBorchersPhase_rightFactor_eq_fourierLaplaceKernel_succRight
```

These are not wrappers: they expose the exact sign, `Fin.rev`, and tail-gap
bookkeeping that failed in the older raw-shell blueprint.

There is one more support layer that must exist before the phase integral
theorem is production-ready.  The integral in
`section43OSBorchersPhaseKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight`
is over absolute Euclidean variables `y`, while
`section43FourierLaplaceIntegral` is defined after the OS I difference
coordinate pullback.  The bridge must be explicit:

```lean
noncomputable def section43DiffCoordRealMeasurableEquiv
    (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃ᵐ NPointDomain d n :=
  (section43DiffCoordRealCLE d n).toHomeomorph.toMeasurableEquiv

theorem section43DiffCoordRealCLE_measurePreserving
    (d n : ℕ) [NeZero d] :
    MeasurePreserving
      (section43DiffCoordRealMeasurableEquiv d n)
      (MeasureTheory.volume : Measure (NPointDomain d n))
      (MeasureTheory.volume : Measure (NPointDomain d n))

theorem section43DiffCoordRealCLE_symm_measurePreserving
    (d n : ℕ) [NeZero d] :
    MeasurePreserving
      (section43DiffCoordRealMeasurableEquiv d n).symm
      (MeasureTheory.volume : Measure (NPointDomain d n))
      (MeasureTheory.volume : Measure (NPointDomain d n))
```

Proof transcript: `section43DiffCoordRealCLE` is `BHW.realDiffCoordCLE`, the
lower triangular map

```text
(x₀, x₁, ..., xₙ) ↦ (x₀, x₁ - x₀, ..., xₙ - xₙ₋₁)
```

applied independently in every spacetime coordinate.  Prove volume
preservation by induction on `n`, but do not leave this as a vague determinant
claim.  The implementable induction is:

```lean
private theorem section43HeadTail_updateZero_sub_head_measurePreserving
    (d n : ℕ) [NeZero d] :
    MeasurePreserving
      (fun p : SpacetimeDim d × (Fin (n + 1) → SpacetimeDim d) =>
        (p.1,
          Function.update p.2 0 (p.2 0 - p.1)))
      (MeasureTheory.volume : Measure
        (SpacetimeDim d × (Fin (n + 1) → SpacetimeDim d)))
      (MeasureTheory.volume : Measure
        (SpacetimeDim d × (Fin (n + 1) → SpacetimeDim d)))
```

Proof of the shear theorem:

1. Split the tail again with
   `MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => SpacetimeDim d) 0`.
2. Under this split, the map is
   `(u, v0, vtail) ↦ (u, v0 - u, vtail)`.
3. Use `MeasureTheory.measurePreserving_prod_neg_add` directly for
   `(u, v0) ↦ (u, -u + v0)`, then rewrite `-u + v0` to `v0 - u` by
   `sub_eq_add_neg`/`add_comm`.  The checked signature is:

```lean
MeasureTheory.measurePreserving_prod_neg_add
  (μ : Measure G) (ν : Measure G) :
  MeasurePreserving (fun z => (z.1, -z.1 + z.2)) (μ.prod ν) (μ.prod ν)
```

   If Lean exposes the update as `(u, v0 + -u)`, use
   `MeasureTheory.measurePreserving_prod_add_right` plus
   `MeasureTheory.Measure.measurePreserving_neg` for the sign; do not invent a
   new measure lemma.
4. Repack by the two `piFinSuccAbove` volume-preserving equivalences.

Then prove the main theorem by recursion:

1. Base `n = 0`: `NPointDomain d 0` is a unique finite product; close with
   `MeasureTheory.volume_preserving_funUnique` or by extensionality and
   `MeasureTheory.MeasurePreserving.id volume`.
2. Step from `n` to `n + 1`: split the source and target
   `NPointDomain d (n + 1)` as
   `SpacetimeDim d × (Fin n → SpacetimeDim d)` using
   `MeasurableEquiv.piFinSuccAbove ... 0`.
3. On the tail factor, apply the induction hypothesis to
   `section43DiffCoordRealCLE d n`; after the split this is the product
   measure-preserving map

```lean
(MeasureTheory.MeasurePreserving.id
    (MeasureTheory.volume : Measure (SpacetimeDim d))).prod ih
```

   where `ih` is the degree-`n` measure-preservation theorem on the tail.
4. Apply `section43HeadTail_updateZero_sub_head_measurePreserving` to replace
   the first tail cumulative point by its difference from the head.
5. Verify by extensionality that the resulting composite is
   `section43DiffCoordRealCLE d (n + 1)`.
6. The inverse theorem follows from the measurable-equivalence form:

```lean
simpa [section43DiffCoordRealMeasurableEquiv] using
  (section43DiffCoordRealCLE_measurePreserving d n).symm
```

   This is why the theorem statement is deliberately phrased through
   `section43DiffCoordRealMeasurableEquiv` rather than only through the bare
   function coercion of the continuous-linear equivalence.

If Mathlib exposes a determinant/Jacobian theorem for finite-dimensional
continuous linear equivalences, it may replace this shear induction, but the
theorem statement above must still be the local API and the proof must still
record that the determinant/scaling factor is exactly `1`.

With that measure theorem, add the one-factor absolute-phase bridge:

```lean
private theorem
    section43WickRotatePhase_after_diffCoord_symm_eq_fourierLaplacePhase
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n)
    (δ : NPointDomain d n) :
    Complex.I *
        ∑ i : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint
              (((section43DiffCoordRealCLE d n).symm δ) k)) i *
          (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)
      =
    -(∑ k : Fin n,
        (δ k 0 : ℂ) *
          (section43QTime (d := d) (n := n) q k : ℂ)) -
      (2 * Real.pi : ℂ) * Complex.I *
        ∑ p : Fin n × Fin d,
          (δ p.1 (Fin.succ p.2) : ℂ) *
            ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
              (section43QSpatial (d := d) (n := n) q)) p : ℂ)

private theorem
    integrable_section43WickRotatePhaseIntegral_of_mem_positiveEnergy
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    Integrable
      (fun x : NPointDomain d n =>
        Complex.exp
          (Complex.I *
            ∑ i : Fin (n * (d + 1)),
              flattenCLEquiv n (d + 1)
                (fun k => wickRotatePoint (x k)) i *
              (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)) *
        f.1 x)

theorem
    section43FourierLaplaceIntegral_eq_wickRotatePhaseIntegral_of_mem_positiveEnergy
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    section43FourierLaplaceIntegral d n f q =
      ∫ x : NPointDomain d n,
        Complex.exp
          (Complex.I *
            ∑ i : Fin (n * (d + 1)),
              flattenCLEquiv n (d + 1)
                (fun k => wickRotatePoint (x k)) i *
              (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)) *
        f.1 x
```

Proof transcript for the phase algebra lemma:

1. Rewrite `flattenCLEquiv` by `finProdFinEquiv`; split the finite sum over
   `Fin (n * (d + 1))` as a double sum over `Fin n × Fin (d + 1)`.
2. Split `Fin (d + 1)` into the time coordinate `0` and spatial coordinates
   `Fin.succ μ`.
3. For the time part, use
   `wickRotatePoint x 0 = Complex.I * (x 0 : ℂ)` and
   `section43CumulativeTailMomentumCLE_symm_apply` at `μ = 0`.  The external
   `Complex.I` gives `Complex.I * Complex.I = -1`, hence the Laplace factor
   `-∑ δ_time * q_time`.
4. For the spatial part, use
   `wickRotatePoint x (Fin.succ μ) = (x (Fin.succ μ) : ℂ)` and
   `section43CumulativeTailMomentumCLE_symm_apply` at `μ ≠ 0`.  The inverse
   cumulative map contributes `-(2 * Real.pi) * (q_k - q_{k+1})`; summation by
   parts over absolute coordinates gives the spatial difference-coordinate
   variables `δ k (Fin.succ μ)`, leaving
   `-(2 * Real.pi) * Complex.I * ∑ δ_spatial * q_spatial`.
5. Use `section43QTime` and `section43QSpatial_apply` to rewrite the `q`
   coordinates.  Finish by `ring_nf` only after all finite-sum reindexing has
   been discharged.

Proof transcript for the integrability lemma:

1. Change variables by `(section43DiffCoordRealCLE d n).symm`; it is enough to
   prove integrability of the difference-coordinate integrand because
   `section43DiffCoordRealCLE_symm_measurePreserving` preserves volume.
2. Rewrite the phase by
   `section43WickRotatePhase_after_diffCoord_symm_eq_fourierLaplacePhase`.
3. Split by `nPointTimeSpatialCLE`.  The spatial Fourier factor has norm `1`;
   prove this after rewriting it to the Fourier-character/Circle form used by
   `partialFourierSpatial_fun`:

```lean
‖((𝐞 (-(inner ℝ η ξ)) : Circle) : ℂ)‖ = 1
```

   The verified API names are `Circle.norm_coe` and `Circle.normSq_coe`.
   If the phase is still in exponential form, first rewrite with
   `Real.fourierChar_apply`; the direct exponential fallback is
   `Complex.norm_exp_ofReal_mul_I`, not a `normSq` lemma.
4. The remaining time factor is
   `Complex.exp (-(∑ k, τ k * q_time k))`.  Since `hq` gives
   `0 ≤ q_time k`, this is bounded by `1` on the support of
   `section43DiffPullbackCLM d n f`, because
   `tsupport_section43DiffPullback_subset_positiveOrthant` gives
   `0 ≤ τ k`.
5. The integrand is therefore bounded by the Schwartz function
   `‖section43DiffPullbackCLM d n f δ‖`, whose norm is integrable.  Use the
   existing Schwartz integrability theorem for `SchwartzMap` norms.

Proof transcript:

1. Rewrite the right side by changing variables with
   `(section43DiffCoordRealCLE d n).symm` and
   `section43DiffCoordRealCLE_symm_measurePreserving`, using
   `integrable_section43WickRotatePhaseIntegral_of_mem_positiveEnergy` to
   satisfy the Bochner integral change-of-variables side condition.
2. Rewrite the transformed `f.1` as `section43DiffPullbackCLM d n f`.
3. Apply
   `section43WickRotatePhase_after_diffCoord_symm_eq_fourierLaplacePhase`.
4. Split the difference-coordinate variable by `nPointTimeSpatialCLE`.  The
   time part is exactly the outer Laplace factor in
   `section43FourierLaplaceIntegral_eq_time_spatial_integral`.
5. For the spatial part, rewrite

```lean
Complex.exp
  (-(2 * Real.pi : ℂ) * Complex.I *
    ∑ p, (η p : ℂ) * (ξ p : ℂ))
```

   as

```lean
((𝐞 (-(inner ℝ η ξ)) : Circle) : ℂ)
```

   using `Real.fourierChar_apply`, `Circle.smul_def`, and the same algebra as
   `fourierTransformFlat_eval` / `physicsFourierFlatCLM_integral`.
6. Close with
   `section43FourierLaplaceIntegral_eq_time_spatial_integral`.

This theorem is the normalization guard.  If the displayed formula needs a
sign or `2 * Real.pi` correction when checked against
`physicsFourierFlatCLM`, fix it here and propagate that correction to S1/S4.
Do not compensate later in `section43OS24Kernel_succRight`.

After the one-factor bridge is available, the product factorization theorem
has the exact target:

```lean
private theorem
    section43OSBorchersPhaseIntegral_factorizes_succRight
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    let qξ := section43CumulativeTailMomentum d (n + (m + 1)) ξ
    let qL :=
      section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ
    let qR := section43RightTailBlock d n (m + 1) qξ
    let lamξ : ℝ :=
      ∑ i,
        (((OSReconstruction.castFinCLE
            (Nat.add_mul n (m + 1) (d + 1)).symm)
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := (m + 1) * (d + 1))
            (flatTimeShiftDirection d (m + 1)))) i) * ξ i
    let ηξ : ℝ := -lamξ / (2 * Real.pi)
    (∫ y : NPointDomain d (n + (m + 1)),
        Complex.exp
          (Complex.I *
            ∑ i : Fin ((n + (m + 1)) * (d + 1)),
              flattenCLEquiv (n + (m + 1)) (d + 1)
                (section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y) i *
                (ξ i : ℂ)) *
        (f.1.osConjTensorProduct g.1) y) =
      Complex.exp (-(2 * Real.pi * t : ℂ) * (ηξ : ℂ)) *
        (star (section43FourierLaplaceIntegral d n f qL) *
          section43FourierLaplaceIntegral d (m + 1) g qR)
```

Proof transcript: split `y` into left and right absolute variables; unfold
`osConjTensorProduct`; use the three coordinate phase lemmas to identify the
left integral with the conjugate of
`section43FourierLaplaceIntegral d n f qL` and the right integral with
`section43FourierLaplaceIntegral d (m + 1) g qR`; factor the product integral
by Fubini; move the external tail phase outside.  The positive-energy inputs
for the one-factor bridge are the left and right block positivity theorems
from S2/S3.

Fubini side conditions for this theorem must be proved explicitly:

```lean
private theorem
    integrable_section43OSBorchersPhaseIntegral_succRight
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ)
    (hξ :
      ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    Integrable
      (fun y : NPointDomain d (n + (m + 1)) =>
        Complex.exp
          (Complex.I *
            ∑ i : Fin ((n + (m + 1)) * (d + 1)),
              flattenCLEquiv (n + (m + 1)) (d + 1)
                (section43OSBorchersTimeShiftConfig_succRight
                  (d := d) t y) i *
                (ξ i : ℂ)) *
        (f.1.osConjTensorProduct g.1) y)
```

Proof: split by the product equivalence.  For the left factor, change
variables by `timeReflectionN d`; use `timeReflectionN_measurePreserving` to
reduce `star (f.1 (timeReflectionN d yL))` to the one-factor integrability
lemma for `qL := section43LeftBorchersBlock ... qξ`, using
`section43LeftBorchersBlock_mem_positiveEnergy_of_mem_spectralRegion`.
Complex conjugation preserves norms, so it does not affect integrability.  The
right factor is directly controlled by the one-factor integrability lemma for
`qR := section43RightTailBlock ... qξ`, using
`section43RightTailBlock_mem_positiveEnergy_of_mem_spectralRegion`.  The
external tail phase has norm `1`, so it does not affect integrability.  Then
use the standard product-integrability theorem already used in the
Section-4.3 Fubini packet.

Then
`section43OSBorchersPhaseKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight`
is short: rewrite by the factorization theorem, use
`section43TailShiftPhase_eq_psiZTimeTest_of_spectralRegion_succRight`, rewrite
the two Fourier-Laplace integrals back to frequency representatives using
`hφ_rep` and `hψ_rep`, and close with
`section43OS24Kernel_succRight_apply`.

The forward-tube lift kernel is then:

```lean
private def section43OSForwardTubeLiftKernelIntegrand_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (y : NPointDomain d (n + (m + 1))) :
    SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ :=
  ((f.1.osConjTensorProduct g.1) y) •
    multiDimPsiZExt
      ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
        ForwardConeAbs d (n + (m + 1)))
      hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
      hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
      (flattenCLEquiv (n + (m + 1)) (d + 1)
        (section43OSForwardTubeLift_succRight (d := d) t y))
```

and the integrability theorem must use the compact support assumptions:

```lean
private theorem hasCompactSupport_osConjTensorProduct
    {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    HasCompactSupport
      ((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
        NPointDomain d (n + m) → ℂ)

private theorem integrable_section43OSForwardTubeLiftKernelIntegrand_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ)) :
    Integrable
      (section43OSForwardTubeLiftKernelIntegrand_succRight
        (d := d) OS lgc f g ht Tflat hTflat_FL)
```

Proof: compact support of `f.osConjTensorProduct g` is not obtained from the
preimage of either projection alone.  Use the split equivalence
`NPointDomain d (n + m) ≃ NPointDomain d n × NPointDomain d m`: the support of
the tensor product is contained in the product of the compact supports of
`f.osConj` and `g`; compactness of `f.osConj` follows from `hf_compact` and
the time-reflection homeomorphism.  Transport the compact product back through
the split equivalence.

For integrability, restrict to this compact support.  The lift is continuous
there and remains in the open tube, hence its image is compact in the tube.
Use `continuous_multiDimPsiZExt_comp_of_mem_tube` for continuity and compact
boundedness of each Schwartz seminorm; then Bochner integrability follows from
the generic compactly supported continuous-map criterion.  If that criterion
is not already exposed, add it as a functional-analysis support lemma, not as
an OS-specific wrapper.

Now define the actual Bochner-integrated lift kernel.  This is the object that
can be paired with `Tflat`; do not try to pair `Tflat` directly with a
pointwise formula.

```lean
noncomputable def section43OSForwardTubeLiftKernel_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat) :
    SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ :=
  ∫ y : NPointDomain d (n + (m + 1)),
    section43OSForwardTubeLiftKernelIntegrand_succRight
      (d := d) OS lgc f g ht Tflat hTflat_FL y
```

The definition must be followed immediately by its evaluation theorem:

```lean
private theorem section43OSForwardTubeLiftKernel_succRight_apply
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ) :
    section43OSForwardTubeLiftKernel_succRight
        (d := d) OS lgc f g ht Tflat hTflat_FL ξ =
      ∫ y : NPointDomain d (n + (m + 1)),
        multiDimPsiZExt
          ((flattenCLEquivReal (n + (m + 1)) (d + 1)) ''
            ForwardConeAbs d (n + (m + 1)))
          hTflat_FL.hCflat_open hTflat_FL.hCflat_conv
          hTflat_FL.hCflat_cone hTflat_FL.hCflat_salient
          (flattenCLEquiv (n + (m + 1)) (d + 1)
            (section43OSForwardTubeLift_succRight (d := d) t y)) ξ *
        (f.1.osConjTensorProduct g.1) y
```

Proof: apply the continuous evaluation functional at `ξ` to the Bochner
integral.  The integrability input is
`integrable_section43OSForwardTubeLiftKernelIntegrand_succRight`.  Then unfold
`section43OSForwardTubeLiftKernelIntegrand_succRight` and use evaluation of
scalar multiplication in `SchwartzMap`.

This gives the kernel EqOn theorem actually consumed by `Tflat`:

```lean
private theorem
    section43OSForwardTubeLiftKernel_eq_OS24Kernel_on_spectralRegion_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat) :
    Set.EqOn
      (fun ξ =>
        section43OSForwardTubeLiftKernel_succRight
          (d := d) OS lgc f g ht Tflat hTflat_FL ξ)
      (fun ξ => section43OS24Kernel_succRight d n m φ ψ t ht ξ)
      (section43WightmanSpectralRegion d (n + (m + 1)))
```

Proof: intro `ξ hξ`; rewrite the left side by
`section43OSForwardTubeLiftKernel_succRight_apply`, then apply
`section43OSForwardTubeLiftKernelIntegral_eq_OS24Kernel_on_spectralRegion_succRight`.

The first scalar theorem is now:

```lean
private theorem
    section43OS24Kernel_pairing_eq_forwardTubeLiftIntegral_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat) :
    Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight (d := d) t y) *
        (f.1.osConjTensorProduct g.1) y
```

Proof transcript:

1. Set
   `Klift := section43OSForwardTubeLiftKernel_succRight
      (d := d) OS lgc f g ht Tflat hTflat_FL`.
2. Prove
   `hEqOn : Set.EqOn (fun ξ => Klift ξ)
      (fun ξ => section43OS24Kernel_succRight d n m φ ψ t ht ξ)
      (section43WightmanSpectralRegion d (n + (m + 1)))`
   by `section43OSForwardTubeLiftKernel_eq_OS24Kernel_on_spectralRegion_succRight`.
3. Use `hasFourierSupportIn_eqOn` with `hTflat_supp` and the symmetric
   orientation of `hEqOn` to get
   `Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) = Tflat Klift`.
4. Commute `Tflat` with the compactly supported Bochner integral defining
   `Klift`.
5. For each `y`, rewrite `Tflat` applied to the integrand:
   if `(f.1.osConjTensorProduct g.1) y = 0`, both sides are zero; otherwise
   `y` is in the support, so
   `section43OSForwardTubeLift_mem_forwardTube_of_osSupport_succRight` and
   `flattenCLEquiv_mem_tubeDomain_image` allow `hTflat_FL.hFL` to be applied.
6. Use `fourierLaplaceExtMultiDim_eq_ext` to replace the
   `fourierLaplaceExtMultiDim` value by `Tflat (multiDimPsiZExt ...)`.
7. Close by the previous transitivity chain.  The theorem should not unfold
   `section43OS24Kernel_succRight`; that work is isolated in the EqOn theorem.

Second, the forward-tube lift integral is the raw OS `xiShift` shell.  This is
formal from the global symmetries of the selected continuation; no
Fourier-Laplace witness is used here.

```lean
private theorem
    section43_forwardTubeLiftIntegral_eq_xiShiftShell_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    {t : ℝ} (ht : 0 < t) :
    (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (section43OSForwardTubeLift_succRight (d := d) t y) *
        (f.1.osConjTensorProduct g.1) y) =
      ∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
        (f.1.osConjTensorProduct g.1) y
```

Proof transcript: unfold the lift as left-block `Fin.rev` permutation plus a
y-dependent diagonal complex translation.  Use `bvt_F_perm` for the left
Borchers reversal and `bvt_F_translationInvariant` for the diagonal
translation, pointwise under the integral.  This step explains why the raw
shell need not itself lie in the forward tube.

Third, the raw `xiShift` shell is the Euclidean OS scalar.  This is not new
analysis; it is the existing Schwinger-side bridge specialized to the
positive-time factors `f.1` and `g.1`.

```lean
private theorem
    section43_xiShiftShell_eq_osScalar_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    {t : ℝ} (ht : 0 < t) :
    (∫ y : NPointDomain d (n + (m + 1)),
        bvt_F OS lgc (n + (m + 1))
          (xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
        (f.1.osConjTensorProduct g.1) y) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1)))
```

Proof: use
`bvt_F_osConjTensorProduct_timeShift_eq_xiShift` or the underlying
`schwinger_simpleTensor_timeShift_eq_xiShift`, with
`hf_ord := f.2`, `hg_ord := g.2`, `hm := Nat.succ_pos m`, and then orient the
result by symmetry.  This step is the only place in S5 where `OS.S` is
introduced.

Fourth, compose the three previous theorems:

```lean
private theorem
    section43OS24Kernel_pairing_eq_osScalar_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_rep :
      section43FourierLaplaceRepresentative d n f
        (section43FrequencyRepresentative (d := d) n φ))
    (hψ_rep :
      section43FourierLaplaceRepresentative d (m + 1) g
        (section43FrequencyRepresentative (d := d) (m + 1) ψ))
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat)
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat) :
    Tflat (section43OS24Kernel_succRight d n m φ ψ t ht) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  exact
    (section43OS24Kernel_pairing_eq_forwardTubeLiftIntegral_succRight
      (d := d) OS lgc φ ψ f g hf_compact hg_compact
      hφ_rep hψ_rep ht Tflat hTflat_supp hTflat_FL).trans <|
    (section43_forwardTubeLiftIntegral_eq_xiShiftShell_succRight
      (d := d) OS lgc f g ht).trans <|
    section43_xiShiftShell_eq_osScalar_succRight
      (d := d) OS lgc f g hg_compact ht
```

This packet is implementation-ready only after the `hTflat_FL` witness
structure is available in Lean.  The old proof idea
"unfold `OS.S` after inverse Fourier/Fubini" is retired: it hides the
analytic-continuation bridge and can regress to a same-test Wightman/Schwinger
comparison.

The final scalar theorem is then:

```lean
private theorem
    section43_OS24_scalar_interchange_succRight
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d (m + 1) → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d (m + 1) → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f)
    (hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g)
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat)
    (hTflat_bv :
      ∀ φflat : SchwartzMap
          (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + (m + 1))
          (unflattenSchwartzNPoint (d := d) φflat) =
            Tflat (physicsFourierFlatCLM φflat))
    (hTflat_FL :
      section43TflatFourierLaplaceWitness
        (d := d) OS lgc (n + (m + 1)) Tflat)
    (KψZ_t : SchwartzMap
        (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ)
    (hKψZ_eval :
      ∀ ξ,
        KψZ_t ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ *
              (SchwartzMap.fourierTransformCLM ℂ
                (section43PsiZTimeTest t ht)) τ) :
    Tflat KψZ_t =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1)))
```

Proof transcript:

1. Obtain `hφ_rep` and `hψ_rep` by S3.
2. Define `KOS := section43OS24Kernel_succRight d n m φ ψ t ht`.
3. Prove `hEqOn : Set.EqOn (fun ξ => KψZ_t ξ) (fun ξ => KOS ξ)
   (section43WightmanSpectralRegion d (n + (m + 1)))` by S4.
4. Use the support theorem exactly once in this outer proof to replace the
   actual time-shift kernel by `KOS`:

```lean
have hT_eq : Tflat KψZ_t = Tflat KOS :=
  hasFourierSupportIn_eqOn
    (S := section43WightmanSpectralRegion d (n + (m + 1)))
    (T := Tflat) hTflat_supp
    (fun ξ hξ => hEqOn hξ)
```

   The generic theorem already exists in `OSReconstruction/SCV/FourierSupportCone.lean`;
   do not introduce a wrapper unless the production proof needs a local
   readability alias.
5. Prove the OS-side scalar recognition

```lean
have hOS :
    Tflat KOS =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  exact
    section43OS24Kernel_pairing_eq_osScalar_succRight
      (d := d) OS lgc φ ψ f g hf_compact hg_compact
      hφ_rep hψ_rep ht Tflat hTflat_supp hTflat_FL
```

6. Close by `exact hT_eq.trans hOS`.

After S1-S5 compile with the explicit `hTflat_FL` witness, the proof docs are
ready for implementing `section43_OS24_scalar_interchange_succRight`.  Before
that point, the only permitted Lean work is the named support infrastructure
above; any direct edit of the final theorem would be another wrapper-shaped
rush into a blocking sorry.

Fifth, audit the **left-block chronological reversal**.  The Wightman tensor
product and the OS tensor product do not use the same left-block convention:

```lean
SchwartzMap.conjTensorProduct_apply
-- star (phi (fun i => splitFirst n m x (Fin.rev i))) * psi (splitLast n m x)

SchwartzNPoint.osConj_apply
SchwartzNPoint.osConjTensorProduct
-- star (f (timeReflectionN d (splitFirst n m x))) * g (splitLast n m x)
```

Thus the global pair theorem must not treat `f.osConjTensorProduct g` as a
literal positive-time Section-4.3 input of degree `n + m`.  For `n > 0`, its
left block is supported in `OrderedNegativeTimeRegion`; the positive
difference-coordinate chain is obtained only after the chronological reversal
of the reflected left block.

Route decision, 2026-04-14: use the separate-factor route from Packet S3/S4.
Do **not** build a single combined Section-4.3 input for
`f.osConjTensorProduct g` in the active theorem.  The scalar proof evaluates
the left and right transformed representatives separately, then reconstructs
the OS scalar by the chronological bookkeeping theorems and the OS scalar
recognition theorem
`section43OS24Kernel_pairing_eq_osScalar_succRight`.

The alternative combined-input route would require a new chronological-reindex
map, schematically:

```lean
def section43ChronologicalOSPairReindex (d n m : ℕ) [NeZero d] :
    NPointDomain d (n + m) ≃L[ℝ] NPointDomain d (n + m)
```

whose first block is `Fin.rev`-reordered after time reflection and whose
second block is unchanged.  Its support theorem must show that the reindexed
combined input lies in the positive Section-4.3 difference-coordinate domain.
Without this theorem, a statement with a single

```lean
F : euclideanPositiveTimeSubmodule (d := d) (N + 1)
```

is only schematic documentation, not Lean-ready mathematics.  This route is
not active and should not be implemented unless the separate-factor route
fails for a concrete Lean reason.

The bookkeeping packet required by the chosen separate-factor route is:

```lean
section43RightTailShift
section43TailGapIndex
section43DiffCoordRealCLE_rightTailShift_time
section43DiffCoordRealCLE_rightTailShift_spatial
section43TimeSplitMeasurableEquiv_tailGap_update
section43TailBgLeftIndex
section43TailBgLeftRevIndex
section43TailBgRightIndex
section43TailGap_succAbove_left
section43TailGap_succAbove_leftRev
section43TailGap_succAbove_right
section43TimeSplit_tailGap_background_left
section43TimeSplit_tailGap_background_leftRev
section43TimeSplit_tailGap_background_right
section43LeftBlock
section43LeftRevBlock
section43RightTailBlock
section43LeftBlock_mem_positiveEnergy
section43LeftRevBlock_mem_positiveEnergy
section43RightTailBlock_mem_positiveEnergy
section43QTime_leftBlock
section43QTime_leftRevBlock
section43QTime_rightTailBlock
section43QTime_rightTailBlock_zero
```

These theorems are allowed production support because they are not wrappers:
they expose the exact coordinate mechanism that prevents the old `hschw`
same-test collapse.  Together with the `section43LeftBorchersBlock` and
total-momentum theorems in S2, they resolve the chronological-reversal branch
for the active OS route.  The remaining proof-doc readiness gate is no longer
"choose a chronological option"; it is to expose the OS scalar recognition
theorem `section43OS24Kernel_pairing_eq_osScalar_succRight` with the proof
transcript in S4.

Once the theorem above is proved with explicit bookkeeping, the formal
canonical-witness consumer is short and safe:

```lean
private theorem
    bvt_W_canonicalWitness_imagAxis_eq_section43FourierLaplaceRepresentative
    ... :
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
      (d := d) OS lgc φ ψ hψ_compact (η * Complex.I) = Φ q := by
  -- Wightman canonical witness -> descended `ψ_Z`
  rw [bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ]
  -- normalize the `ψ_Z` scalar argument if needed
  -- apply `section43_descendedWightmanPsiZ_eq_iterated_transformSliceScalar`
  -- close by Packet H's transformed-representative normal form, reversed
```

Do not implement this formal consumer until
`section43_descendedWightmanPsiZ_eq_iterated_transformSliceScalar` has no
placeholder bookkeeping hypothesis.

The next theorem slot to finish in the proof docs is therefore not another
wrapper around

```lean
lemma84_bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport
section43_timeShift_descendedPsiZ_eq_osSchwingerValue_of_section43Transport
```

The next theorem slot is either the explicit transform apply theorem from
§5.9.1a or, after that support theorem exists, the global expansion theorem
whose proof begins by defining a concrete normal-form scalar from the
partial-spatial/time-slice expansion:

```lean
private theorem
    section43_common_descendedPsiZ_normalForms_of_fourierLaplaceTransform
    -- same statement displayed above
```

Lean-readiness requirement for this theorem:

1. The proof must first introduce `let N : ℂ := ...`, where the right side is
   the explicit scalar produced by expanding the Wightman distribution and the
   Section-4.3 transformed tests through
   `partialFourierSpatial_fun_eq_integral` /
   `partialFourierSpatial_timeSliceSchwartz`.
2. The proof may then establish `hW_point_nf`, `hDesc_nf`, and `hOS_nf`.
   It may not define `N` as the Wightman point value, the descended pairing,
   or the OS Schwinger scalar and then prove the other two equalities; that
   would hide the same blocker.
3. The theorem statement may return `∃ N : ℂ, ...` only after the proof body
   has constructed this concrete `N`.  The existential is an outer packaging
   convenience, not the normal form itself.
4. If the existing production API does not expose the required transform or
   the required expansion of `bvt_W` or `OS.S` down to this `N`, the next Lean
   theorem must be the smallest transform/slice theorem that exposes exactly
   that scalar.  Do not edit the quarantined supplier bodies until the
   transform and expansion theorems are proved or the proof docs state their
   full proof transcripts.

Guard against the old `hschw` regression:

1. The banned theorem surface was a same-test-function comparison

```lean
OS.S (n + m)
  (ZeroDiagonalSchwartz.ofClassical
    (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
=
bvt_W OS lgc (n + m)
  (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
```

   or any equivalent assertion that the Euclidean semigroup `e^{-tH}` equals
   a Wightman real-time unitary translation `e^{itH}` on the same test data.

2. The permitted future comparison is different: the Wightman-side tests must
   have physics-Fourier classes in the Section-4.3 transformed image, and the
   theorem statement must carry frequency-projection transform hypotheses such
   as

```lean
hφ_transform :
  section43FrequencyProjection (d := d) n φ =
    section43FourierLaplaceTransformComponent d n f
hψ_transform :
  section43FrequencyProjection (d := d) m ψ =
    section43FourierLaplaceTransformComponent d m g
```

   The old `hφf`/`hψg` quotient-image hypotheses are not enough, because they
   collapse by `rfl` to the same-test case.

3. Even the corrected transform hypotheses are not magic rewrite rules.  They
   may only be used after the spatial-Fourier/time-slice expansion has exposed
   the correct unshifted quotient classes and the nonnegative background-time
   hypotheses `htφ` and `htψ`.  In particular, do not rewrite
   `timeShiftSchwartzNPoint (d := d) t ψ` to
   `timeShiftSchwartzNPoint (d := d) t g.1` pointwise.

4. A theorem that proves the positive-real comparison must therefore display
   all three normal forms `hW_point_nf`, `hDesc_nf`, and `hOS_nf` through the
   same constructed `N`.  Without those three outputs, the theorem is either a
   wrapper or a possible return of the old false route.

Circularity guard for this theorem:

1. Do not use
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_ambient_descended_psiZ_boundaryValue_eq`
   or
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`.
   Those theorems consume the descended `ψ_Z`/hPsi equality that this theorem
   is meant to supply.
2. Do not use
   `bvt_W_conjTensorProduct_timeShift_boundaryValue_fourierTransform_eq_of_ambient_canonicalExtension_imag_eq_osHolomorphicValue`.
   It assumes the positive-imaginary-axis canonical-to-OS equality and then
   derives boundary-value Fourier-transform equality; using it here would be a
   proof loop.
3. Do not use `lemma42_matrix_element_time_interchange` or
   `lemma42_matrix_element_time_interchange_of_section43Transport`. These are
   consumers after the shell limit and hPsi are available.
4. Do not use
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_singleSplitXiShiftScalar_of_section43Transport`
   or any theorem with `bvtSingleSplitXiShiftScalar` in its statement. That
   route is optional downstream diagnostics only; it is no longer a live proof
   dependency.

After the explicit transform/common-normal-form supplier exists, the descended
off-diagonal theorem consumed by `hPsi` should be restated on that surface:

```lean
private theorem
    descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_fourierLaplaceTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφ_transform :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f)
    (hψ_transform :
      section43FrequencyProjection (d := d) m ψ =
        section43FourierLaplaceTransformComponent d m g) :
    let A : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
      osTimeShiftHilbert (d := d) OS lgc 1 one_pos
    let hA : IsSelfAdjoint A :=
      osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g.1 g.2⟧)) : OSHilbertSpace OS))
    ∀ t : ℝ, ∀ ht : 0 < t,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) =
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)
```

Proof transcript for the off-diagonal core theorem:

1. Introduce `ψZ`, `A`, `hA`, `xF`, and `xG`.
2. Expand the descended Wightman side only with
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
3. Apply
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_fourierLaplaceTransform`
   at the same `t ht`.
4. Close by `simpa [ψZ, A, hA, xF, xG]`.
5. Do not use `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`
   in this core theorem; that theorem belongs to the final one-line conversion
   from Laplace offdiag to spectral boundary offdiag.
6. Do not introduce any theorem whose statement needs
   `HasCompactSupport (φ : NPointDomain d n → ℂ)`. Such a theorem is on the
   wrong surface for the live consumer.

Implementation transcript for this `hPsi` theorem:

1. Introduce, for fixed `t ht`, the local names
   `ψZ`, `A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos`,
   `hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos`,
   `xF`, and `xG`.
2. Let `hLaplace` be
   `descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_fourierLaplaceTransform`
   specialized at `t ht`.
3. Rewrite the right side with `selfAdjointSpectralBoundaryValueOffdiagCLM_apply`.
4. Rewrite the resulting scalar with
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`
   using
   `spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos`.
5. Close by transitivity through the common scalar
   `ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)`,
   then `simpa [A, hA, xF, xG, ψZ]`.

Exact linearity helper slots for OS-side bookkeeping:

These helpers are still useful if Lean needs to simplify the OS Hilbert vectors
appearing in local semigroup rewrites, but they are **not** a license to
polarize the Wightman side. They should never introduce a compactness
hypothesis for `φ`.

On the old quotient-image surface, the two available maps are:

```lean
section43PositiveEnergyQuotientMap (d := d) n :
  SchwartzNPoint d n →L[ℂ] Section43PositiveEnergyComponent (d := d) n

os1TransportComponent d n :
  euclideanPositiveTimeSubmodule (d := d) n →L[ℂ]
    Section43PositiveEnergyComponent (d := d) n
```

This old component-linearity helper is valid quotient bookkeeping, but it is
not sufficient for the transformed route because it still mentions
`os1TransportComponent`.  If Option A is implemented, the transformed analogue
must use `section43FourierLaplaceTransformComponent` in the right-hand side;
then its proof is ordinary `map_add`/`map_smul` for the new CLM plus the
linearity of the OS Hilbert class.  If Option B is implemented first, postpone
this component-linearity helper entirely and work only with scalar slice
normal forms.

Legacy old-surface helper, retained only as a warning:

```lean
private theorem section43Transport_component_linear_comb_single_single
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (a b : ℂ) :
    let Φ : BorchersSequence d :=
      a • BorchersSequence.single n φ + b • BorchersSequence.single m ψ
    let F : PositiveTimeBorchersSequence d :=
      a • PositiveTimeBorchersSequence.single n f.1 f.2 +
      b • PositiveTimeBorchersSequence.single m g.1 g.2
    ∀ k : ℕ,
      section43PositiveEnergyQuotientMap (d := d) k (Φ.funcs k) =
        os1TransportComponent d k
          ⟨((F : BorchersSequence d).funcs k), F.ordered_tsupport k⟩
```

Proof transcript:

1. `intro k`.
2. `dsimp` the local `Φ` and `F`.
3. Close by `simp` with
   `BorchersSequence.add_funcs`, `BorchersSequence.smul_funcs`,
   `PositiveTimeBorchersSequence.add_toBorchersSequence`,
   `PositiveTimeBorchersSequence.smul_toBorchersSequence`,
   `PositiveTimeBorchersSequence.single_toBorchersSequence`,
   `os1TransportComponent_apply`, `map_add`, `map_smul`, `hφf`, and `hψg`.
4. The cases `k = n`, `k = m`, `n = m`, and the off-support zero cases are all
   componentwise `simp` cases of the same statement; do not split them into
   four separate theorem surfaces.

The exact helper theorem for the OS Hilbert vectors is the corresponding class
linearity in the OS quotient completion:

```lean
private theorem osHilbertClass_linear_comb_single_single
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (a b : ℂ) :
    let F₀ : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f.1 f.2
    let G₀ : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single m g.1 g.2
    (((show OSPreHilbertSpace OS from (⟦a • F₀ + b • G₀⟧)) :
        OSHilbertSpace OS)) =
      a • (((show OSPreHilbertSpace OS from (⟦F₀⟧)) :
        OSHilbertSpace OS)) +
      b • (((show OSPreHilbertSpace OS from (⟦G₀⟧)) :
        OSHilbertSpace OS))
```

Proof transcript:

1. `dsimp` the local `F₀` and `G₀`.
2. Change the left OS pre-Hilbert class to
   `a • (⟦F₀⟧ : OSPreHilbertSpace OS) + b • (⟦G₀⟧ : OSPreHilbertSpace OS)`.
   This is justified by the quotient `Add`/`SMul` instances in
   `SchwingerOS.lean`.
3. Push the equality into the completion with
   `UniformSpace.Completion.coe_add` and
   `UniformSpace.Completion.coe_smul`.
4. Finish by `simpa`.

The four OS-side expanded-boundary bookkeeping instantiations are exactly:

```lean
section43Transport_component_linear_comb_single_single
  (d := d) φ ψ f g hφf hψg 1 1
section43Transport_component_linear_comb_single_single
  (d := d) φ ψ f g hφf hψg 1 (-1)
section43Transport_component_linear_comb_single_single
  (d := d) φ ψ f g hφf hψg 1 Complex.I
section43Transport_component_linear_comb_single_single
  (d := d) φ ψ f g hφf hψg 1 (-Complex.I)

osHilbertClass_linear_comb_single_single
  (d := d) OS f g 1 1
osHilbertClass_linear_comb_single_single
  (d := d) OS f g 1 (-1)
osHilbertClass_linear_comb_single_single
  (d := d) OS f g 1 Complex.I
osHilbertClass_linear_comb_single_single
  (d := d) OS f g 1 (-Complex.I)
```

Use `simpa [sub_eq_add_neg, one_smul]` to match the theorem outputs to the
four terms `xF + xG`, `xF - xG`, `xF + Complex.I • xG`, and
`xF - Complex.I • xG` produced by
`selfAdjointSpectralBoundaryValueOffdiagCLM_apply`.

With that transformed-surface `hPsi` theorem, the canonical witness is
identified with the OS holomorphic matrix element by direct application of the
existing reducer:

```lean
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_fourierLaplaceTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφ_transform :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f)
    (hψ_transform :
      section43FrequencyProjection (d := d) m ψ =
        section43FourierLaplaceTransformComponent d m g) :
    ∀ t : ℝ, 0 < t →
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f.1 f.2)
        (PositiveTimeBorchersSequence.single m g.1 g.2) (t : ℂ)
```

Proof transcript:

1. Apply
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_ambient_descended_psiZ_boundaryValue_eq`
   with `f := f.1`, `hf_ord := f.2`, `g := g.1`, `hg_ord := g.2`.
2. Supply its `hPsi` hypothesis with
   `descendedPsiZ_boundaryValue_eq_osSpectral_of_fourierLaplaceTransform`.

The direct Lemma-4.2 adapter for transformed representatives becomes formal
after the two non-finite-height packets above are proved:

```lean
private theorem lemma42_matrix_element_time_interchange_of_fourierLaplaceTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφ_transform :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f)
    (hψ_transform :
      section43FrequencyProjection (d := d) m ψ =
        section43FourierLaplaceTransformComponent d m g) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.1.osConjTensorProduct g.1))
```

Production correction, 2026-04-14: this adapter surface is now quarantined in
`OSToWightmanPositivity.lean`.  The formal transitivity proof was fine as an
adapter, but the hypotheses of the supplier packet below it were too weak:
`hφf`/`hψg` alone are satisfied by the same-test specialization
`φ := f.1`, `ψ := g.1`.  Therefore this adapter may be revived only after the
supplier packet is restated with the explicit `(4.19)-(4.20)` transform
surface described above.  Until then, it is not an active production theorem
and should not be used as a downstream dependency.

Proof transcript:

1. Apply `lemma42_matrix_element_time_interchange` with
   `H := fun z =>
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact z`.
2. Supply `hH_imag_os` from
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_fourierLaplaceTransform`.
3. Supply `hlimit` from
   `tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_fourierLaplaceTransform`,
   proved from the Lemma-8.4 pointwise shell-limit supplier rather than from
   the withdrawn finite-height zero residual.

Quarantined status after the 2026-04-14 surface audit:

1. The formal dependency split remains useful: an hPsi packet would prove
   `hH_imag_os`, i.e. the identification of
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension ... ((t : ℂ) * I)`
   with the OS holomorphic matrix element.  But the old hPsi theorem surface
   with only `hφf`/`hψg` is not live.
2. It does **not** supply the `hlimit` hypothesis of
   `lemma42_matrix_element_time_interchange`; that is supplied separately by
   the Lemma-8.4 pointwise theorem
   `lemma84_bvt_W_timeShift_eq_integral_timeShift_mul_fourierTransform_psiZ_of_fourierLaplaceTransform`
   after the transform surface is in place.
3. The shell-limit theorem shape to recover, after the explicit transform
   surface is in place, is:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_fourierLaplaceTransform
    -- explicit `(4.19)-(4.20)` transform hypotheses, not only `hφf`/`hψg`
    -- but proved without finite-height shell/horizontal equality
```

   Its proof is formal from
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   and
   `bvt_W_timeShift_eq_canonicalExtension_imagAxis_of_fourierLaplaceTransform`.
   The only non-formal input below it is the Lemma-8.4 pointwise supplier. It
   must not use raw `KShell = KHorizontal`, the withdrawn finite-height
   `TW/ψ_Z` scalar theorem, or the withdrawn finite-height zero residual.

Readiness rule for this subsection:

1. No theorem without the explicit `(4.19)-(4.20)` transform surface may
   conclude a shell-to-canonical, real-time-to-Laplace, or Wightman-to-OS
   scalar identity.  In particular, `hφf`/`hψg` alone are insufficient.
2. Arbitrary-`φ, ψ` residual theorems may only compute obstruction limits; they
   must not be used as zero-limit targets.
3. As of the corrected 2026-04-13 readiness audit, the raw
   single-split/cutoff packet is retired. The support lemmas
   `tflat_pairing_eq_of_eqOn_dualCone`, `psiZ_twoPi_pairing_formula`, and
   `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`
   have already been implemented and checked. The canonical positive-height
   shell packet and the horizontal Paley packet may be used only as diagnostic
   normal forms unless the explicit Section-4.3 transform hypotheses are
   present in the theorem statement.
4. The direct pointwise theorem
   `bvt_W_timeShift_sub_descendedPsiZ_zero_of_section43Transport` remains
   forbidden. The current shell-to-OS route must go through an explicit
   Fourier-Laplace transformed scalar bridge; the raw finite-height
   canonical-shell/horizontal dual-cone EqOn is withdrawn because it would
   identify a real-time oscillatory shell with an imaginary-axis Laplace
   damping factor for arbitrary `φ, ψ`.
5. Auxiliary Lean lemmas before the next production theorem are allowed only
   for the new `Section43FourierLaplaceTransform.lean` support packet, the
   transformed hPsi packet, or the transformed non-finite-height shell-limit
   supplier.  The already-implemented shell-side `Tflat` Fubini, horizontal
   Paley, and `ψ_Z` calculation lemmas may be cited as diagnostics, but they
   are not permission to implement another finite-height residual.
6. The hPsi compactness correction remains sound: use the direct off-diagonal
   helper
   `descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_fourierLaplaceTransform`
   and never Wightman-side diagonal polarization. Any theorem that asks for
   `HasCompactSupport (φ : NPointDomain d n → ℂ)` has left the live surface.
7. If Lean implementation exposes a genuine mathematical or type-level gap not
   covered by the displayed theorem slots, stop production edits and return to
   this proof-doc section first. Do not patch around the gap with wrappers or a
   weaker theorem shape.
8. After a non-finite-height shell-limit supplier is proved, feed it directly
   into `lemma42_matrix_element_time_interchange` together with the hPsi
   `hH_imag_os` identification. Do not route it through the withdrawn
   finite-height residual.
9. Optional downstream diagnostics involving raw `singleSplit` or
   `bvtSingleSplitXiShiftScalar` are not part of the live route. They may be
   revisited only after the main positivity path is closed or after a new
   valid tube representative is documented and checked.
10. Exact verification commands for the next Lean edits are:
    `lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTransform.lean`
    after implementing the support packet;
    `lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
    after implementing any hPsi theorem or non-finite-height shell-limit
    supplier; and
    `lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
    if a new support theorem is placed in BVLimits.
    If a support theorem is promoted from private to public in an imported
    file, run that exact support-file check first, then the downstream
    Positivity check. Do not replace these with a broad build.

### 5.9.5. Detailed proof of the final public closure

The final theorem

`bvt_W_positive_of_transportImage_density`

is proved in four formal stages:

1. Transport-image core.
   Apply `bvt_wightmanInner_eq_transport_norm_sq_onImage` and
   Hilbert-space nonnegativity on the transported image.

2. Hilbert-space density.
   Use the fact that the relevant positive-time vectors are dense in
   `OSHilbertSpace OS` by construction of the completion. This is the density
   actually used in the OS I positivity mechanism.

3. VEV/transport identification.
   Show that `bvt_W` agrees with the corresponding vacuum expectation value on
   the transported positive-time core.

4. Continuity closure.
   Use continuity of `bvt_W` together with Hilbert-space closure to pass from
   the transported core to arbitrary public `BorchersSequence d`.

The only continuity allowed here is the bounded finite-support continuity
already documented in the repo. Rebuilding theorem 3 from a new global topology
on raw `BorchersSequence d` remains off-route.

Exact current implementation status:

1. the old raw same-input theorem slogan is withdrawn and must not be
   implemented literally;
2. the current local production branch already contains the Stage-3/4
   transformed-image carrier and the on-image Hilbert transport;
3. the live frontier is no longer a transport placeholder or a Schwartz-density
   theorem, but the transformed-image quadratic identity and final positivity
   closure;
4. the theorem-3 blueprint now endorses only the transformed-image /
   Hilbert-density reading of Section 4.3.

## 6. Exact relation to the current production consumers

The current legacy consumers can remain compiled, but they are not part of the
endorsed closure route.

Safe usage:

1. mine the current codebase only for reusable continuity / completion /
   positive-time Hilbert-space facts;
2. keep the deprecated `hschw` consumer chain compiled but untouched;
3. if a legacy theorem becomes useful later, re-justify it from the corrected
   transformed-image Package-I route rather than treating it as an input.

Unsafe usage:

1. introducing a new theorem whose primary conclusion is another `h*` consumer
   interface;
2. reentering the K2 common-kernel route;
3. implementing the old raw Package-I theorem surface on the same
   `BorchersSequence d` input without first fixing the transformed-image
   statement.

## 7. Minimal Lean pseudocode for the endorsed route

The later Lean implementation should use the following theorem-package names
unless an exact compile failure forces a local renaming. In that case the docs
must be updated at the same time; the names below are now part of the intended
implementation contract, not casual pseudocode.

```lean
/- Step A: one-variable identity theorem. -/
theorem identity_theorem_right_halfplane ... := by
  ...

/- Step B: compact positive-time single/split equality on {Re z > 0}. -/
theorem bvt_xiShift_eq_osInnerProduct_holomorphicValue_single ... := by
  apply identity_theorem_right_halfplane
  ...

/- Step C: withdrawn same-shell boundary pairing route (historical, false). -/
-- Do not implement `schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift`.
-- The same-input shell identity is false and remains quarantined.

/- Step D: withdrawn raw positive-time sesquilinear route (historical, false). -/
-- Do not implement `bvt_wightmanInner_eq_osInner_of_positiveTime`.

/- Step E: withdrawn raw positive-time positivity route (historical, false). -/
-- Do not implement `bvt_positiveTime_self_nonneg_from_packageC`.

/- Step F: withdrawn raw density route (historical, do not implement). -/
theorem orderedPositiveTime_dense_schwartzNPoint ... := by
  ...

theorem exists_orderedPositiveTime_seq_tendsto ... := by
  ...

/- Step G: withdrawn approximation bundling route (historical, do not implement). -/
theorem exists_positiveTime_componentwise_approximation ... := by
  ...

/- Step H: withdrawn continuity-after-density route (historical, do not implement). -/
theorem WightmanInnerProduct_tendsto_of_componentwise_tendsto ... := by
  ...

theorem re_WightmanInnerProduct_tendsto_of_componentwise_tendsto ... := by
  ...

/- Step I: final theorem-3 closure via Section 4.3 transformed image. -/
def bvtTransportImage ... := by
  ...

def BvtTransportImageSequence ... := by
  ...

noncomputable def bvt_transport_to_osHilbert_onImage ... := by
  ...

theorem bvt_wightmanInner_eq_transport_norm_sq_onImage ... := by
  ...

theorem bvt_W_positive_of_transportImage_density ... := by
  ...
```

The current production file
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
already uses the exact names
`identity_theorem_right_halfplane`,
`bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`.
The transformed-image theorem names above should therefore be treated as the
fixed guidance for the corrected Section 4.3 closure package. The older raw
same-input names
`schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift`,
`bvt_wightmanInner_eq_osInner_of_positiveTime`,
and `bvt_positiveTime_self_nonneg_from_packageC`
are withdrawn historical names and should not be reintroduced as theorem
targets.

## 8. Representation-gap note

The theorem-3 route above is the current-code realization of the OS proof.

The docs therefore record the following explicitly:

1. raw `BorchersSequence d` is a bounded finite-record representation;
2. this representation is enough for theorem 3 because
   `WightmanInnerProduct` is a finite sum;
3. therefore theorem 3 should be closed by the Section 4.3 transport-map
   realization, not by first imposing a `Submodule` / topology package on the
   raw type.

This is a local repo encoding fact, not a mathematical change to the OS route.

## 9. Support-work checklist

Before any later production proof resumes, the support work should verify:

1. no theorem-3 doc section still treats `hschw` as the target theorem shape;
2. no theorem-3 doc section still recommends `bvtInitialCore` on raw
   `BorchersSequence d`;
3. `mathlib_gap_analysis.md` classifies the raw `BorchersSequence` issue as a
   local representation gap, not an upstream gap;
4. any new test-file support work stays inside Package A through Package I
   above, and does not revive the withdrawn F/G/H density route as if it were
   endorsed.
5. the docs identify the exact current local frontier as the corrected
   transformed-image Package-I theorem surface, not as a generic
   “boundary-value limit”.
6. the docs explicitly record that Packages A-B are already implemented in
   `OSToWightmanPositivity.lean`;
7. no theorem-3 doc section still states the naive raw theorem
   `WightmanInnerProduct(bvt_W)(F,F).re = ‖u(F)‖^2` on the same raw public
   `BorchersSequence d` input as if it were already the correct Section 4.3
   theorem surface.

## 10. Bottom line

Theorem 3 is no longer a shell-comparison project.

Theorem 3 is now exactly this:

1. prove the positive-time semigroup bridge;
2. prove positivity on `PositiveTimeBorchersSequence d`;
3. define the Section 4.3 transformed Minkowski image and its OS Hilbert-space
   transport map;
4. identify the Wightman quadratic form with a Hilbert norm square on that
   transformed-image core;
5. extend positivity from the transformed-image core to arbitrary
   `BorchersSequence d` by density/continuity.

That is the only theorem-3 route this note now endorses.
