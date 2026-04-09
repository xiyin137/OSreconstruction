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
2. the live theorem-3 implementation target is now the Section 4.3 transport
   image / quadratic-identity / closure package from Package I;
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
    section43PositiveEnergyQuotientMap (d := d) n (toBorchers.funcs n) ∈
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
- the next honest Stage-5 blocker is the concrete Section-4.3 / Lemma-4.2
  adapter `lemma42_matrix_element_time_interchange`;
- the transformed-image kernel theorem `bvt_W_matrixElement_onImage` is the
  immediate consumer of that adapter, not a direct next step from slice
  descent alone.

/-- Concrete Section-4.3 / Lemma-4.2 adapter: rewrite the reconstructed
Wightman matrix element in the same one-variable slice coordinates used by
`section43_iteratedSlice_descendedPairing`, then perform the Section-8
time-variable interchange there. This is the first theorem after slice
descent that still contains genuinely new analytic content. -/
theorem lemma42_matrix_element_time_interchange
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hφ :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψ :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ... := by
  ...

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

OS I / OS II dependency note:

1. in the original paper, Eqs. (4.24)-(4.28) consume the distribution
   `\tilde W` from Eq. (4.12), so Section 4.3 is not literally independent of
   Lemma 8.8;
2. the production route must not rely on the broken OS I Lemma 8.8 itself;
3. instead, the Wightman-side kernel is supplied by the already-repaired OS II
   `bvt_F` / `bvt_W` construction built from `OSLinearGrowthCondition`;
4. the explicit Fourier-Laplace integral `(4.19)-(4.20)` still governs the
   **test-function transport** on the Section-4.3 side.

### 5.9.1. Detailed proof of `os1TransportComponent`

The production definition of

`os1TransportComponent :
  EuclideanPositiveTimeComponent d n ->L[ℂ] Section43PositiveEnergyComponent d n`

must follow the Section-4.3 paper route exactly.

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
before the final `def` is closed:

```lean
theorem os1TransportComponent_eq_iterated_oneVar
    (f : EuclideanPositiveTimeComponent d n) :
    ...

theorem os1TransportComponent_restrict_positiveEnergy
    (f : EuclideanPositiveTimeComponent d n) :
    ...

theorem os1TransportComponent_continuous :
    Continuous (os1TransportComponent d n)
```

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
   - inside that adapter, time-variable interchange is exactly the hidden
     Section-8 one-variable theorem recorded in
     `docs/os1_detailed_proof_audit.md` as
     `one_variable_time_interchange_for_wightman_pairing`;
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
